

Set Warnings "-notation-overridden".
From Stdlib Require Import Arith Nat Bool.

Definition reg  := nat.
Definition val  := nat.
Definition addr := nat.

Definition taint := bool.
Definition tval := (val * taint)%type.

Definition t_or (t1 t2 : taint) := orb t1 t2. 

Definition tv_val (x : tval) : val := fst x.
Definition tv_taint (x : tval) : taint := snd x.

Definition mk_tval (v : val) (t : taint) : tval := (v, t).

Inductive instr : Type :=
| Nop : instr
| Add : reg -> reg -> reg -> instr          (* rd rs1 rs2 *)
| Mul : reg -> reg -> reg -> instr          (* rd rs1 rs2 *)
| Load  : reg -> reg -> nat -> instr        (* rd base off *)
| Store : reg -> reg -> nat -> instr        (* rs_val base off *)
| BrZero : reg -> nat -> instr.             (* rs off *)

Definition prog := nat -> option instr.

Definition regs := reg -> tval.
Definition mem  := addr -> option tval.

Record state : Type := {
  pc : nat;
  rf : regs;
  mm : mem;
}.

Definition regs_set (r : regs) (x : reg) (tv : tval) : regs :=
  fun y => if Nat.eqb y x then tv else r y.

Definition mem_set (m : mem) (a : addr) (tv : tval) : mem :=
  fun b => if Nat.eqb b a then Some tv else m b.

