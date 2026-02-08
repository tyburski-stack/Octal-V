

Set Warnings "-notation-overridden".
From Stdlib Require Import Arith Nat Bool.


Definition reg  := nat.
Definition val  := nat.
Definition taint := bool.
Definition addr := nat.


(* defined byte and tainted byte *)
Definition byte := nat.

Definition tbyte := (byte*taint)%type.
Definition tb_val (x : tbyte) : byte := fst x.
Definition tb_taint (x : tbyte) : taint := snd x.
Definition mk_tbyte (b : byte) (t : taint) : tbyte := (b, t).


Definition tval := (val * taint)%type.

Definition t_or (t1 t2 : taint) := orb t1 t2. 

Definition tv_val (x : tval) : val := fst x.
Definition tv_taint (x : tval) : taint := snd x.

Definition mk_tval (v : val) (t : taint) : tval := (v, t).



(* Extend induction Syntax ... *)
Inductive size : Type := S1 | S2 | S4 | S8.

Inductive instr : Type :=
| Nop : instr
| Add : reg -> reg -> reg -> instr                 (* rd rs1 rs2 *)
| Mul : reg -> reg -> reg -> instr                 (* rd rs1 rs2 *)
| Load  : size -> reg -> reg -> nat -> instr       (* sz rd base off *)
| Store : size -> reg -> reg -> nat -> instr       (* sz rs base off *)
| BrZero : reg -> nat -> instr.                    (* rs off *)

Definition prog := nat -> option instr.

Definition regs := reg -> tval. (* (val * taint) *)
Definition mem  := addr -> option tbyte.


Record state : Type := {
  pc : nat;
  rf : regs;
  mm : mem;
}.

Definition regs_set (r : regs) (x : reg) (tv : tval) : regs :=
  fun y => if Nat.eqb y x then tv else r y.

(* updated  mem_set to write t_byte*)
Definition mem_set (m : mem) (a : addr) (tb : tbyte) : mem :=
  fun b => if Nat.eqb b a then Some tb else m b.


