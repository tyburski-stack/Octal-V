

Set Warnings "-notation-overridden".
From Stdlib Require Import Arith Nat Bool.

Definition reg  := nat.
Definition val  := nat.
Definition addr := nat.

Inductive instr : Type :=
| Nop : instr
| Add : reg -> reg -> reg -> instr          (* rd rs1 rs2 *)
| Mul : reg -> reg -> reg -> instr          (* rd rs1 rs2 *)
| Load  : reg -> reg -> nat -> instr        (* rd base off *)
| Store : reg -> reg -> nat -> instr        (* rs_val base off *)
| BrZero : reg -> nat -> instr.             (* rs off *)

Definition prog := nat -> option instr.

Definition regs := reg -> val.
Definition mem  := addr -> option val.

Record state : Type := {
  pc : nat;
  rf : regs;
  mm : mem;
}.

Definition regs_set (r : regs) (x : reg) (v : val) : regs :=
  fun y => if Nat.eqb y x then v else r y.

Definition mem_set (m : mem) (a : addr) (v : val) : mem :=
  fun b => if Nat.eqb b a then Some v else m b.