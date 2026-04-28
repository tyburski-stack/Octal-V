# Project Plan (High Level)

## 1. Define the ISA Syntax
- registers, values, taints, memory addresses
- instruction datatype (`instr`)
- block structure (`code : list instr` + `term`)
- program counter as a **location** `(label, index)`
- machine state (`pc`, register file, memory)

## 2. Define the Machine Semantics
- a **true small-step relation**  
  `step : prog -> state -> state -> Prop`
- fetch based on `(label, index)`
  - if `index < length code` → execute instruction
  - if `index = length code` → execute block terminator
- fallthrough increments `index`
- jumps reset to `(target, 0)`
- “stuck” behavior via `option` for:
  - invalid fetches
  - tainted load/store addresses
  - tainted branch conditions

## 3. Write Small Examples / Tests
- tiny programs as `prog : label -> option block`
- example executions using repeated `step`
- confirm taint propagation and stuck behavior

## 4. Prove Basic Properties
- determinism of `step` ✅
- small-step reasoning infrastructure (`step*`)
- reachability lemmas

## 5. Prove Type Safety (Current Focus)
- define a notion of **well-formed state** (`wf_state`)
- define **terminal states** (`terminal`)
- prove:
  - **Progress**: well-formed states either step or terminate ✅
  - **Preservation**: stepping preserves well-formedness (via `tyenv_preserves`)
  - **Type Safety**: well-formed states never get stuck ✅

### Current Status
- Type safety theorem proven **modulo** a preservation assumption:
  ```
  tyenv_preserves P Γ
  ```
- This isolates the remaining work to the **typing system**

## 6. Next Step: Replace Assumptions with Typing Rules
- define a concrete **type environment** (`tyenv`)
- define **state types** (initially: register taint tracking)
- define:
  - `state_satisfies`
  - instruction typing rules (`instr_typed`)
  - program typing (`program_typed`)
- prove:
  ```
  program_typed P Γ -> tyenv_preserves P Γ
  ```
- eliminate assumptions and obtain full type safety

---

# Files

- `simple-isa/Syntax.v`  
  ISA datatypes, block structure, location-based program counter, machine state, update helpers

- `simple-isa/Machine.v`  
  Small-step operational semantics (`fetch`, `exec_instr`, `exec_term`, `step`)

- `simple-isa/Safety.v` (or similar)  
  Proofs of determinism, progress, preservation, and type safety

- `_CoqProject`  
  build/loadpath config (`-Q simple-isa SimpleIsa`)

---

# Build Instructions

- `_CoqProject` is handwritten (see repo).
- `Makefile` and `Makefile.conf` are generated.

If the generated `Makefile` is present:
```
make clean && make
```

Otherwise regenerate:
```
coq_makefile -f _CoqProject -o Makefile
make clean && make
```

---

# Summary

This project formalizes a taint-tracking abstract machine and proves a **type safety theorem** ensuring that well-typed programs never perform unsafe operations (e.g., secret-dependent control flow or memory access). The current development establishes the full proof structure and reduces the remaining work to defining and verifying a concrete typing system.