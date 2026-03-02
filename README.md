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
- determinism of `step`
- simple invariants about register/memory updates
- multi-step execution (`step*`) and reachability lemmas

---

# Files

- `simple-isa/Syntax.v`  
  ISA datatypes, block structure, location-based program counter, machine state, update helpers

- `simple-isa/Machine.v`  
  Small-step operational semantics (`fetch`, `exec_instr`, `exec_term`, `step`)

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