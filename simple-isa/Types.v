Set Warnings "-notation-overridden".
From Stdlib Require Import Arith Nat Bool Lists.List.
From SimpleIsa Require Import Syntax Machine.


(** state types (static typing layer) *)
(** state_type describes expected taint of each register
    Static abstraction of the runtime register file **)

Record state_type : Type := {
  reg_ty : reg -> taint
}.

(* Typing environment maps each program counter
   to expected state_type at that point in the program. *)

Definition tyenv : Type := pc -> state_type.

(* Runtime state satisfies a state_type if for every register,
   the actual taint matches the expected taint in the type. *)

(** planned change *)
Definition state_satisfies (s : state) (T : state_type) : Prop :=
  forall r, tv_taint (rf s r) = reg_ty T r.


(** Updating types helper *)
(** Update type of single register after instruction executes, all other
    registers keep prev type *)
Definition update_reg_ty (T : state_type) (r : reg) (t : taint) : state_type :=
  {| reg_ty := fun x => if Nat.eqb x r then t else reg_ty T x |}.

(** instruction typing rules **)
(** If execution i executes in state satisfying T, 
    resulting state will satisfy T' *)
Inductive instr_typed : state_type -> instr -> state_type -> Prop :=

(* Does nothing, unchanged type*)
| T_Nop :
    forall T,
      instr_typed T Nop T

(** Add propagates taint, result taint = or of input taints*)
| T_Add :
    forall T rd rs1 rs2,
      instr_typed T (Add rd rs1 rs2)
        (update_reg_ty T rd (t_or (reg_ty T rs1) (reg_ty T rs2)))

(** Mul behaves same as add in terms of taint*)
| T_Mul :
    forall T rd rs1 rs2,
      instr_typed T (Mul rd rs1 rs2)
        (update_reg_ty T rd (t_or (reg_ty T rs1) (reg_ty T rs2)))

(** Load requires base address to be untainted (security cond) 
    Loaded val gets some taint t_loaded (abstract for now) *)
| T_Load :
    forall T sz rd base off t_loaded,
      reg_ty T base = false ->
      instr_typed T (Load sz rd base off)
        (update_reg_ty T rd t_loaded)
  
(** store also requires base address to be untainted, doesn't change register types *)
| T_Store :
    forall T sz rs base off,
      reg_ty T base = false ->
      instr_typed T (Store sz rs base off) T.