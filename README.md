# STATUS

Branch: `typing-phases`. Toolchain: Rocq Prover 9.0.1 (OCaml 4.14.2).
Build: `coq_makefile -f _CoqProject -o Makefile && make` — compiles cleanly,
no warnings except none; **zero `admit` / `Admitted` / `Axiom` / `Parameter`
anywhere in the development.**

## Checkpoint summary

| Checkpoint | Status |
|---|---|
| C1 — concrete typing, `tyenv_preserves` discharged, `type_safety` instantiated | **CLOSED** |
| C2 — positive program (types + runs) and negative program (proven untypeable for *all* entry types; also proven to get dynamically stuck) | **CLOSED** |
| C3 — precise memory taint over fixed regions, preservation reproven | **CLOSED** |
| C4 — dependent value-range types, region memory safety, abstract sound entailment | **CLOSED** (see scope notes below) |

There are **no GAPs**: every lemma stated in the development is proven with `Qed`.

## Files

- `simple-isa/Typing.v` (C1, Phase 1)
  - `sty := reg -> taint` (true = may be secret), `state_satisfies`, `sty_sub`.
  - Relational typing: `instr_ty`, `term_ty`, `instrs_ty` (chain), `block_ty`,
    `program_typed`. Rules as specified: Add/Mul join operand taints; Load
    requires public base and conservatively sets `rd := true`; Store requires
    public base; `TBrZero` requires a public condition; branch/jump targets
    via `sty_sub` weakening.
  - Γ is per program point: `point_ok P Θ (l,ix) R` says the *remaining* code
    `skipn ix (code b)` plus terminator types from `R`; `gamma_of` also
    carries the `mem_total` invariant (all addresses `Some`), preserved by
    `store_bytes` (`store_bytes_total`), giving Load definedness.
  - `program_typed_tyenv_preserves : program_typed P Θ -> tyenv_preserves P (gamma_of P Θ)`
  - `typed_type_safety` = `Safety.type_safety` at the concrete Γ, with the
    `tyenv_preserves` obligation discharged. No assumptions.
- `simple-isa/Test.v` (C2)
  - Positive: `Pgood` (r1 secret; `r0 := r1 + r2`; jump; halt). `Pgood_typed`,
    `s0_wf`, `good_runs` (two real steps to a terminal state), `good_safe`.
  - Negative: `Pbad` loads a byte then branches on it.
    `Pbad_untypeable : forall Θ, ~ program_typed Pbad Θ` — no derivation
    exists for any assignment of block entry types (the Load forces
    `r0 : true`, the branch requires `r0 : false`).
    `bad_gets_stuck`: run from a state with a tainted byte at the load
    address, the machine reaches a non-terminal state with no successor —
    the dynamic counterpart of the static rejection.
- `simple-isa/MemTaint.v` (C3, Phase 2)
  - Static memory taint map `M : addr -> taint` fixed per program ("fixed,
    statically-known regions" = the level sets of `M`).
  - `msty := { rt : reg -> taint; pt : reg -> option addr }`: `pt r = Some a`
    means r provably holds the untainted, statically-known address `a`.
  - Precise rules: `MTyLoadPrec` types the loaded value with
    `region_taint M (a+off) (size_bytes sz)` (join of `M` over the footprint);
    `MTyStoreSec` allows storing a possibly-secret value when the whole
    footprint is in the secret region. `MTyLoadTop`/`MTyStorePub` keep the
    conservative Phase-1 behaviour.
  - Invariant `mem_agrees M m` (defined bytes at `M = false` addresses are
    untainted); maintained by both store rules
    (`store_untainted_agrees`, `store_secret_agrees`).
  - Preservation reproven: `program_typed2_tyenv_preserves`,
    `typed_type_safety2`.
  - Demo `PL_typed` + `PL_runs`: the exact program *shape* rejected in C2
    (load-then-branch) types and runs in Phase 2 when the pointer targets
    public memory — the precision gain, machine-checked.
- `simple-isa/DepRange.v` (C4, Phase 3)
  - Constraint language: `cexpr ::= CReg r | CConst n | CAdd e e`,
    `constraint ::= CLe e e`; contexts `ctx := list constraint`; semantics
    `csat` / `ctx_sat` over the register-value valuation `vals_of s`
    (the paper's Δ).
  - `sty3 := { rt3 : reg -> taint; dctx : ctx }`. Sound context update:
    `havoc r D` (drop constraints mentioning r, `havoc_sound`);
    `T3AddExact` additionally records `rd = rs1 + rs2` (as two `CLe`) when
    `rd ∉ {rs1, rs2}`; `T3BrZero` refines Δ with `r <= 0` (then) / `1 <= r`
    (else) at the branch targets; subtyping `sty3_sub` implies contexts via
    the oracle (`ctx_impl`).
  - Memory: declared disjoint `region`s (`rlo`, `rlen`, `rtnt`).
    **`mem_total` is gone.** Invariants: `mem_valid` (region addresses are
    mapped) and `mem_agrees3` (public-region bytes untainted).
  - Memory safety: `T3Load`/`T3Store` require `footprint_in`: two entailment
    queries proving `rlo <= base+off` and `base+off+size <= rlo+rlen` from Δ.
    Progress for Load uses only `mem_valid` + these bounds — typed loads
    never touch unmapped memory. Load result taint = the region's `rtnt`
    (precise); secret stores require a secret-region footprint
    (`store_secret_agrees3`, using region disjointness).
  - Entailment abstraction (per Rule 2): a `Section` with
    `Variable entails : ctx -> constraint -> bool` and
    `Hypothesis entails_sound : forall D c, entails D c = true -> forall V, ctx_sat V D -> csat V c`.
    Nothing is axiomatized globally; closing the section discharges both into
    the theorem statements, e.g.:

    ```
    typed_type_safety3
      : forall entails, (forall D c, entails D c = true -> forall V, ctx_sat V D -> csat V c) ->
        forall RS, regions_disjoint RS ->
        forall P Θ s, program_typed3 entails RS P Θ ->
        wf_state P (gamma3 entails RS P Θ) s ->
        (exists s', step P s s' /\ wf_state P (gamma3 entails RS P Θ) s') \/ terminal P s
    ```
  - A concrete sound oracle `entails_syn` (syntactic membership + constant
    comparison) with proven `entails_syn_sound` inhabits the interface, and
    an end-to-end demo (`P3_typed`, `s3_wf`, `P3_runs`, `P3_safe`) type-checks
    and runs a load from a declared public region `[100,108)` over a memory
    that is *unmapped everywhere else* — fully closed, zero assumptions.

  **Scope notes (what C4 does *not* model, stated honestly):** the constraint
  language is linear `≤` over `+` and constants (no `Mul` tracking — `Mul`
  havocs its destination); region bounds are constants rather than symbolic
  expressions; the concrete demo oracle is intentionally weak (the interface
  is where an SMT-backed oracle would plug in). These are modelling
  limitations, not unproven obligations — everything *stated* is proven.

## Print Assumptions (verbatim output per theorem)

Every theorem below prints exactly: `Closed under the global context`

- `Safety.type_safety` — Closed under the global context
- `Typing.program_typed_tyenv_preserves` — Closed under the global context
- `Typing.typed_type_safety` — Closed under the global context
- `Test.good_safe` — Closed under the global context
- `Test.good_runs` — Closed under the global context
- `Test.Pbad_untypeable` — Closed under the global context
- `Test.bad_gets_stuck` — Closed under the global context
- `MemTaint.program_typed2_tyenv_preserves` — Closed under the global context
- `MemTaint.typed_type_safety2` — Closed under the global context
- `MemTaint.PL_typed` — Closed under the global context
- `MemTaint.PL_runs` — Closed under the global context
- `DepRange.program_typed3_tyenv_preserves` — Closed under the global context
- `DepRange.typed_type_safety3` — Closed under the global context
- `DepRange.entails_syn_sound` — Closed under the global context
- `DepRange.P3_safe` — Closed under the global context
- `DepRange.P3_runs` — Closed under the global context

(For C4 the entailment soundness is a *hypothesis inside the statements*, as
permitted; the global context is nevertheless closed, and the `entails_syn`
instantiation shows the hypothesis is satisfiable.)

## Commits (branch `typing-phases`)

```
a573b00 C4: DepRange.v - dependent value-range types (constraint ctx, havoc, branch refinement), region-based memory safety (no mem_total), abstract sound entailment via Section; soundness fully closed; concrete syntactic oracle + end-to-end demo
25215e0 C3: MemTaint.v - precise memory taint over fixed static regions (pointer knowledge pt, region_taint loads, secret-region stores); preservation reproven; assumptions closed
8e8553f C2: Test.v - positive typed+running program; negative leaky program proven untypeable for all entry types
cec5beb C1: concrete taint typing (Typing.v); program_typed => tyenv_preserves; type_safety instantiated with no assumptions
```

## Final build log (tail), from `make clean && coq_makefile -f _CoqProject -o Makefile && make`

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

## Notes on existing code

`Syntax.v`, `Machine.v`, `Safety.v` are untouched. `_CoqProject` was extended
to include `Safety.v` (previously missing from it), `Typing.v`, `MemTaint.v`,
and `DepRange.v`; the committed `Makefile` was regenerated by `coq_makefile`
accordingly.
