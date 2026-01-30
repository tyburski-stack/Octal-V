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
- `simple-isa/Test.v` — example programs/tests
- `_CoqProject` — build/loadpath config (`-Q simple-isa SimpleIsa`)