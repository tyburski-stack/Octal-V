## Project plan (high level)

1. **Define the ISA syntax**
   - registers, values, memory addresses
   - instruction datatype (`instr`)
   - machine state (`pc`, register file, memory)

2. **Define the machine semantics**
   - a small-step relation `step : prog -> state -> state -> Prop`
   - “stuck” behavior for invalid fetches/loads (via `option`)

3. **Write small examples / tests**
   - tiny programs as `prog : nat -> option instr`
   - example executions using `step`

4. **Prove basic properties**
   - determinism of `step`
   - simple invariants about register/memory updates
   - multi-step execution (`step*`) and reachability lemmas

## Files
- `simple-isa/Syntax.v` — ISA datatypes + machine state + update helpers
- `simple-isa/Machine.v` — operational semantics (`step`)
- `_CoqProject` — build/loadpath config (`-Q simple-isa SimpleIsa`)

## Makefile Instructions
- the _CoqProject is handwritten (view in the repo).
- Makefile, Makefile.conf are generated. 
- .Makefile.d is also generated (the Makefile sets VDFILE := .Makefile.d and creates it via rocq dep).
- Build commands: if the generated Makefile is present, make clean && make. 
- If not, regenerate first with coq_makefile -f _CoqProject -o Makefile and then run make clean && make.