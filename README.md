# Octal-V

A machine-checked **information-flow type system for a small imperative ISA**, developed in the
[Rocq Prover](https://rocq-prover.org/) (Coq). The development defines a byte-addressed
register machine with taint-carrying values, layers three progressively more precise static
type systems on top of it, and proves type safety — progress plus preservation — for each one.

Every lemma in the development is closed with `Qed`. There are **no `admit`, `Admitted`, `Axiom`,
or `Parameter` declarations anywhere in the tree**, and every headline theorem prints
`Closed under the global context` under `Print Assumptions`.

---

## What it proves

The central result is `Safety.type_safety`: a well-formed state either steps to another
well-formed state or is terminal.

```coq
Theorem type_safety :
  forall (P : prog) (Γ : tyenv) (s : state),
    tyenv_preserves P Γ ->
    wf_state P Γ s ->
    (exists s', step P s s' /\ wf_state P Γ s') \/ terminal P s.
```

This is stated against an *abstract* typing environment `Γ : pc -> state -> Prop` together with a
preservation obligation. The work of the project is discharging that obligation for three
concrete, increasingly precise type systems — so `type_safety` is not left as scaffolding but
instantiated three times with nothing assumed.

| Phase | Module | Type system | Instantiated safety theorem |
|---|---|---|---|
| 1 | `Typing.v` | Register taint tracking | `typed_type_safety` |
| 2 | `MemTaint.v` | Register taint + static memory regions | `typed_type_safety2` |
| 3 | `DepRange.v` | Dependent value-range types + region memory safety | `typed_type_safety3` |

Each phase strictly increases precision: programs rejected by phase 1 are accepted by phase 2
when the extra memory information justifies it, and phase 3 drops the "all memory is mapped"
assumption entirely in favour of proving that typed loads stay inside declared regions.

---

## The machine

`Syntax.v` and `Machine.v` define the target. It is deliberately small.

**Values carry taint.** A `tval` is a `(val * taint)` pair and a `tbyte` is `(byte * taint)`,
where `taint = bool` and `true` means *may be secret*. Registers hold `tval`; memory is
`addr -> option tbyte`, so a location is either mapped-with-taint or unmapped.

**Instructions.**

```coq
Inductive instr :=
| Nop
| Add   : reg -> reg -> reg -> instr          (* rd rs1 rs2 *)
| Mul   : reg -> reg -> reg -> instr          (* rd rs1 rs2 *)
| Load  : size -> reg -> reg -> nat -> instr  (* sz rd base off *)
| Store : size -> reg -> reg -> nat -> instr. (* sz rs base off *)
```

`size` is `S1 | S2 | S4 | S8`; multi-byte accesses pack and unpack little-endian
(`pack_le` / `unpack_le`) and join the taint of every byte in the footprint.

**Control flow is block-structured.** A `block` is a list of instructions plus a terminator:

```coq
Inductive term := TJmp : label -> term | TBrZero : reg -> label -> label -> term | THalt.
```

A `prog` is `label -> option block`, and a `pc` is a `(label, index)` pair. The terminator is
treated as living at index `length (code b)`; any index beyond that is stuck. `fetch` returns
`FInstr` or `FTerm` accordingly.

**The semantics get stuck on unsafe operations rather than leaking.** `exec_instr` returns
`None` when a `Load` or `Store` uses a tainted base register, or when the load footprint hits
unmapped memory; `exec_term` returns `None` for `TBrZero` on a tainted condition, and for
`THalt`. This is what makes stuckness meaningful: the dynamic semantics already refuses to
branch on a secret, and the type systems are proving that well-typed programs never reach that
refusal.

`Safety.v` also proves the semantics deterministic (`step_deterministic`).

---

## The three type systems

### Phase 1 — register taint (`Typing.v`)

A state type is `sty := reg -> taint`. Typing is relational: `instr_ty`, `term_ty`,
`instrs_ty` (chained through a block), `block_ty`, `program_typed`.

- `Add` / `Mul` join the taints of their operands into `rd`.
- `Load` requires a **public base register** and conservatively sets `rd := true`.
- `Store` requires a public base register.
- `TBrZero` requires a **public condition register** — this is the no-secret-branching rule.
- Jump and branch targets are checked against the target block's entry type via the
  subtyping relation `sty_sub`.

The typing environment is per program point: `point_ok P Θ (l,ix) R` says the *remaining* code
`skipn ix (code b)` plus the terminator types from `R`. `gamma_of` bundles this with a
`mem_total` invariant (every address is `Some`), preserved across writes by `store_bytes_total`,
which is what gives `Load` definedness in this phase.

**Headline:** `program_typed_tyenv_preserves` discharges the preservation obligation, and
`typed_type_safety` is `type_safety` at the concrete `Γ`. `typed_start_wf` is the convenient
entry point: a state at the head of a typed block whose registers satisfy the block's entry
type is well-formed.

### Phase 2 — precise memory taint over static regions (`MemTaint.v`)

Phase 1 is coarse in one specific way: *every* load produces a secret. Phase 2 fixes that by
giving each program a static memory taint map `M : addr -> taint`, whose level sets are the
"statically known regions".

State types gain pointer knowledge:

```coq
Record msty := { rt : reg -> taint; pt : reg -> option addr }.
```

`pt r = Some a` means `r` provably holds the untainted, statically known address `a`.

- `MTyLoadPrec` types the loaded value at `region_taint M (a+off) (size_bytes sz)` — the join
  of `M` over exactly the bytes read — instead of `true`.
- `MTyStoreSec` permits storing a possibly-secret value when the whole footprint lies in the
  secret region.
- `MTyLoadTop` / `MTyStorePub` retain the conservative phase-1 behaviour where pointer
  knowledge is absent.

The invariant `mem_agrees M m` (defined bytes at public addresses are untainted) is maintained
by both store rules (`store_untainted_agrees`, `store_secret_agrees`).

**Precision gain, machine-checked.** `PL_typed` and `PL_runs` take the exact program *shape*
that phase 1 rejects — load, then branch on the loaded value — and show it types and runs when
the pointer targets public memory.

### Phase 3 — dependent value-range types and region memory safety (`DepRange.v`)

The largest module (~1000 lines). It adds a linear constraint language over register values and
uses it to prove **memory safety**, not just taint discipline.

```coq
Inductive cexpr      := CReg : reg -> cexpr | CConst : nat -> cexpr | CAdd : cexpr -> cexpr -> cexpr.
Inductive constraint := CLe : cexpr -> cexpr -> constraint.
Definition ctx       := list constraint.
```

`csat` / `ctx_sat` interpret constraints over `vals_of s`, the register-value valuation. A state
type is `sty3 := { rt3 : reg -> taint; dctx : ctx }`.

Context updates are proved sound rather than assumed:

- `havoc r D` drops every constraint mentioning `r` (`havoc_sound`).
- `T3AddExact` records `rd = rs1 + rs2` as two `CLe` constraints when `rd ∉ {rs1, rs2}`.
- `T3BrZero` refines the context at each successor: `r <= 0` on the *then* branch, `1 <= r` on
  the *else* branch.
- Subtyping `sty3_sub` implies context entailment via the oracle (`ctx_impl`).

**Memory is now partial.** `mem_total` is gone. Instead there are declared disjoint `region`s
(`rlo`, `rlen`, `rtnt`) and two invariants: `mem_valid` (region addresses are mapped) and
`mem_agrees3` (public-region bytes are untainted). `T3Load` and `T3Store` require `footprint_in`,
which issues two entailment queries proving `rlo <= base+off` and `base+off+size <= rlo+rlen`.
Progress for `Load` then uses only `mem_valid` plus those bounds — **typed loads never touch
unmapped memory.** Load taint is the region's `rtnt`; secret stores require a secret-region
footprint, using region disjointness.

**The entailment oracle is abstracted, not axiomatized.** A `Section` introduces

```coq
Variable entails : ctx -> constraint -> bool.
Hypothesis entails_sound :
  forall D c, entails D c = true -> forall V, ctx_sat V D -> csat V c.
```

Closing the section discharges both into the theorem statements:

```coq
typed_type_safety3
  : forall entails, (forall D c, entails D c = true -> forall V, ctx_sat V D -> csat V c) ->
    forall RS, regions_disjoint RS ->
    forall P Θ s, program_typed3 entails RS P Θ ->
    wf_state P (gamma3 entails RS P Θ) s ->
    (exists s', step P s s' /\ wf_state P (gamma3 entails RS P Θ) s') \/ terminal P s.
```

Nothing is axiomatized globally. A concrete oracle `entails_syn` (syntactic membership plus
constant comparison) with a proven `entails_syn_sound` inhabits the interface, showing the
hypothesis is satisfiable. The end-to-end demo (`P3_typed`, `s3_wf`, `P3_runs`, `P3_safe`)
type-checks and runs a load from a declared public region `[100,108)` over a memory that is
**unmapped everywhere else**.

---

## Worked examples (`Test.v`)

The test module is where the type systems are made falsifiable.

**Positive.** `Pgood` marks `r1` secret, computes `r0 := r1 + r2`, jumps, halts. `Pgood_typed`
gives the derivation, `s0_wf` an initial well-formed state, `good_runs` two real steps to a
terminal state, `good_safe` the safety corollary.

**Negative.** `Pbad` loads a byte and branches on it. Two complementary results:

- `Pbad_untypeable : forall Θ, ~ program_typed Pbad Θ` — no derivation exists for *any*
  assignment of block entry types. The `Load` forces `r0 : true`; the branch demands
  `r0 : false`. This is a genuine universally quantified rejection, not a failed proof search.
- `bad_gets_stuck` — running from a state with a tainted byte at the load address reaches a
  non-terminal state with no successor. The dynamic counterpart of the static rejection.

Phase 2's `PL_typed` / `PL_runs` then complete the story: the same *shape* becomes typeable once
the memory region information shows the load is public.

---

## Repository layout

```
_CoqProject          logical mapping (-Q simple-isa SimpleIsa) and file list
Makefile             generated by coq_makefile; regenerate rather than edit
STATUS.md            checkpoint log, Print Assumptions transcript, build log
simple-isa/
  Syntax.v           registers, taint, tval/tbyte, instr, term, block, prog, state
  Machine.v          size/packing, load_bytes/store_bytes, fetch, exec_instr, exec_term, step
  Safety.v           terminal, wf_state, tyenv, tyenv_preserves, progress, preservation,
                     step_deterministic, type_safety
  Typing.v           phase 1 — register taint
  MemTaint.v         phase 2 — static memory regions and pointer knowledge
  DepRange.v         phase 3 — constraint contexts, region memory safety, abstract entailment
  Test.v             positive and negative worked programs
  Types.v            early state_type / instr_typed sketch (see note below)
```

Dependency order, which is also compile order:

```
Syntax → Machine → Safety → Typing → { MemTaint, DepRange, Test }
```

`Syntax.v`, `Machine.v`, and `Safety.v` form the trusted base and are shared unchanged by all
three phases — each phase adds a new typing layer on top rather than modifying the semantics it
is proved against.

---

## Building

Requires a Rocq Prover installation with OCaml. `STATUS.md` records the development as built
against **Rocq 9.0.1 / OCaml 4.14.2**; the committed `Makefile` carries a
`COQMAKEFILE_VERSION` of `9.1.0`. Regenerating the Makefile is therefore the recommended first
step and is harmless in either case:

```bash
coq_makefile -f _CoqProject -o Makefile
make
```

Expected output:

```
ROCQ DEP VFILES
ROCQ compile simple-isa/Syntax.v
ROCQ compile simple-isa/Machine.v
ROCQ compile simple-isa/Safety.v
ROCQ compile simple-isa/Typing.v
ROCQ compile simple-isa/MemTaint.v
ROCQ compile simple-isa/DepRange.v
ROCQ compile simple-isa/Test.v
```

To rebuild from scratch: `make clean && coq_makefile -f _CoqProject -o Makefile && make`.

`make validate` re-checks the compiled `.vo` files with `rocqchk` against the kernel, which is
the strongest available confirmation that the proofs are accepted.

### Checking the assumptions yourself

The proof-status claim is mechanically verifiable. In `rocq repl` (or `coqtop`) with the project
load path:

```coq
From SimpleIsa Require Import Typing MemTaint DepRange Test.
Print Assumptions Typing.typed_type_safety.
Print Assumptions MemTaint.typed_type_safety2.
Print Assumptions DepRange.typed_type_safety3.
Print Assumptions Test.Pbad_untypeable.
```

Each prints `Closed under the global context`. `STATUS.md` lists all sixteen theorems checked
this way. For phase 3, entailment soundness appears as a *hypothesis inside the theorem
statement* rather than a global axiom — the global context is still closed, and
`entails_syn_sound` demonstrates the hypothesis is satisfiable.

---

## Scope and limitations

Stated plainly, because the distinction matters: these are **modelling** limitations, not
unproven obligations. Everything the development states, it proves.

- **The constraint language is linear.** `≤` over `+` and constants only. There is no
  multiplication tracking — `Mul` havocs its destination register.
- **Region bounds are constants**, not symbolic expressions.
- **The concrete oracle is intentionally weak.** `entails_syn` does syntactic membership and
  constant comparison. The `Section` interface is the seam where an SMT-backed oracle would
  plug in; the soundness hypothesis is exactly the contract such an oracle would have to meet.
- **The ISA is minimal.** No procedure calls, no indirect jumps, no dynamic allocation, no
  arithmetic overflow (values are `nat`).
- **Taint is a two-point lattice.** `bool`, not a general security lattice.
- **This is not a proof of non-interference.** The theorems establish progress and preservation
  for the taint and range disciplines — well-typed programs do not get stuck, do not branch on
  secrets, and (phase 3) do not access unmapped memory. A full two-run indistinguishability
  argument is not part of the development.

### Note on `Types.v`

`Types.v` contains an earlier sketch of the typing layer (`state_type`, `tyenv`, `instr_typed`)
that `Typing.v` supersedes. It is **not listed in `_CoqProject`**, but `Safety.v` still opens
with `From SimpleIsa Require Import Syntax Machine Types`. Since `-Q simple-isa SimpleIsa` puts
the directory on the load path, `Types.vo` must exist for `Safety.v` to compile, yet
`coq_makefile` generates no rule to build it from the current file list. If a clean build stops
at `Safety.v`, add `simple-isa/Types.v` to `_CoqProject` before `simple-isa/Safety.v` and
regenerate the Makefile. Alternatively, dropping the unused `Types` import from `Safety.v`
removes the dangling edge — nothing in `Safety.v` uses anything `Types.v` defines, and its
`tyenv` shadows the one in `Types.v`.

---

## License

No license file is present in this repository. Without one, default copyright applies and the
code is not licensed for reuse.
