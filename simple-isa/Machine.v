
Set Warnings "-notation-overridden".
From Stdlib Require Import Arith Nat Bool.
From SimpleIsa Require Import Syntax.

Inductive step (P : prog) : state -> state -> Prop :=
| StepNop :
    forall s,
      P (pc s) = Some Nop ->
      step P s {| pc := pc s + 1; rf := rf s; mm := mm s |}

| StepAdd :
    forall s rd rs1 rs2,
      P (pc s) = Some (Add rd rs1 rs2) ->
      let v := rf s rs1 + rf s rs2 in
      step P s {| pc := pc s + 1;
                  rf := regs_set (rf s) rd v;
                  mm := mm s |}

| StepMul :
    forall s rd rs1 rs2,
      P (pc s) = Some (Mul rd rs1 rs2) ->
      let v := rf s rs1 * rf s rs2 in
      step P s {| pc := pc s + 1;
                  rf := regs_set (rf s) rd v;
                  mm := mm s |}

| StepLoad :
    forall s rd base off a v,
      P (pc s) = Some (Load rd base off) ->
      a = rf s base + off ->
      mm s a = Some v ->
      step P s {| pc := pc s + 1;
                  rf := regs_set (rf s) rd v;
                  mm := mm s |}

| StepStore :
    forall s rs_val base off a,
      P (pc s) = Some (Store rs_val base off) ->
      a = rf s base + off ->
      step P s {| pc := pc s + 1;
                  rf := rf s;
                  mm := mem_set (mm s) a (rf s rs_val) |}

| StepBrZeroTaken :
    forall s rs off,
      P (pc s) = Some (BrZero rs off) ->
      rf s rs = 0 ->
      step P s {| pc := pc s + 1 + off; rf := rf s; mm := mm s |}

| StepBrZeroNotTaken :
    forall s rs off,
      P (pc s) = Some (BrZero rs off) ->
      rf s rs <> 0 ->
      step P s {| pc := pc s + 1; rf := rf s; mm := mm s |}. 