Set Warnings "-notation-overridden".
From Stdlib Require Import Arith Nat Bool Lia Lists.List.
Import ListNotations.
From SimpleIsa Require Import Syntax Machine Safety Typing.

(* ===================================================================== *)
(* Phase 2 (Checkpoint C3): precise memory taint over FIXED, statically  *)
(* known address regions.                                                *)
(*                                                                       *)
(* The static memory model is a map  M : addr -> taint  fixed for the    *)
(* whole program ("regions" are simply the sets of addresses M sends to  *)
(* false resp. true).  State types are enriched with pointer knowledge:  *)
(*   rt : reg -> taint        (taint bound, as in Phase 1)               *)
(*   pt : reg -> option addr  (statically known fixed address)           *)
(*                                                                       *)
(* A register with  pt r = Some a  provably holds the untainted value a, *)
(* so loads and stores through it access a statically known footprint:   *)
(*  - Load becomes PRECISE: the result taint is the join of M over the   *)
(*    footprint (instead of the Phase-1 "always may-be-secret").         *)
(*  - Store of a possibly-secret value is allowed when the whole         *)
(*    footprint lies in the secret region (M = true there).              *)
(* The invariant tied to M is agreement:  every defined byte at an       *)
(* address with M a = false is untainted.  Stores maintain it.           *)
(* ===================================================================== *)

(* ------------------------------------------------------------------ *)
(* State types with pointer knowledge                                  *)
(* ------------------------------------------------------------------ *)

Record msty := {
  rt : reg -> taint;        (* true = may be secret *)
  pt : reg -> option addr;  (* statically known fixed address *)
}.

Definition upd_reg (S : msty) (x : reg) (t : taint) : msty :=
  {| rt := fun y => if Nat.eqb y x then t else rt S y;
     pt := fun y => if Nat.eqb y x then None else pt S y |}.

(* Memory agreement with the static taint map. *)
Definition mem_agrees (M : addr -> taint) (m : mem) : Prop :=
  forall a tb, m a = Some tb -> M a = false -> tb_taint tb = false.

(* Satisfaction. *)
Definition msat (M : addr -> taint) (S : msty) (s : state) : Prop :=
  (forall r, rt S r = false -> tv_taint (rf s r) = false) /\
  (forall r a, pt S r = Some a -> rf s r = mk_tval a false) /\
  mem_agrees M (mm s).

(* Subtyping: S2 weaker = more taint, fewer pointer facts. *)
Definition msty_sub (S1 S2 : msty) : Prop :=
  (forall r, rt S1 r = true -> rt S2 r = true) /\
  (forall r a, pt S2 r = Some a -> pt S1 r = Some a).

Lemma msty_sub_refl : forall S, msty_sub S S.
Proof. intros S; split; intros; assumption. Qed.

Lemma msat_sub :
  forall M S1 S2 s, msty_sub S1 S2 -> msat M S1 s -> msat M S2 s.
Proof.
  intros M S1 S2 s [Hrt Hpt] (H1 & H2 & H3).
  split; [| split].
  - intros r Hr2. destruct (rt S1 r) eqn:E1.
    + apply Hrt in E1. congruence.
    + apply H1. exact E1.
  - intros r a Hr2. apply H2. apply Hpt. exact Hr2.
  - exact H3.
Qed.

(* ------------------------------------------------------------------ *)
(* Taint of a fixed memory footprint                                   *)
(* ------------------------------------------------------------------ *)

Fixpoint region_taint (M : addr -> taint) (a : addr) (n : nat) : taint :=
  match n with
  | 0 => false
  | S n' => t_or (M a) (region_taint M (a + 1) n')
  end.

(* Loading an untainted footprint yields an untainted value. *)
Lemma load_bytes_region_taint :
  forall M n m a tbs,
    mem_agrees M m ->
    region_taint M a n = false ->
    load_bytes m a n = Some tbs ->
    tbytes_taint tbs = false.
Proof.
  intros M n; induction n as [| n IH]; intros m a tbs Hag Hrt Hl; simpl in *.
  - injection Hl as <-. reflexivity.
  - unfold t_or in Hrt. apply Bool.orb_false_iff in Hrt.
    destruct Hrt as [HMa Hrest].
    destruct (m a) as [tb |] eqn:Ema; [| discriminate].
    destruct (load_bytes m (a + 1) n) as [tbs' |] eqn:El; [| discriminate].
    injection Hl as <-.
    unfold tbytes_taint. simpl.
    unfold t_or. apply Bool.orb_false_iff. split.
    + eapply Hag; eauto.
    + apply (IH m (a + 1) tbs' Hag Hrest El).
Qed.

(* Storing untainted bytes preserves agreement (at any address). *)
Lemma store_untainted_agrees :
  forall M tbs m a,
    Forall (fun tb => tb_taint tb = false) tbs ->
    mem_agrees M m ->
    mem_agrees M (store_bytes m a tbs).
Proof.
  intros M tbs; induction tbs as [| tb tbs IH]; intros m a Hall Hag; simpl.
  - exact Hag.
  - inversion Hall as [| x l Hhd Htl]; subst.
    apply IH; [exact Htl |].
    intros x tbx Hx HMx.
    unfold mem_set in Hx.
    destruct (Nat.eqb x a) eqn:E.
    + injection Hx as <-. exact Hhd.
    + eapply Hag; eauto.
Qed.

(* Storing anything entirely inside the secret region preserves
   agreement. *)
Lemma store_secret_agrees :
  forall M tbs m a,
    (forall k, k < length tbs -> M (a + k) = true) ->
    mem_agrees M m ->
    mem_agrees M (store_bytes m a tbs).
Proof.
  intros M tbs; induction tbs as [| tb tbs IH]; intros m a Hsec Hag; simpl.
  - exact Hag.
  - apply IH.
    + intros k Hk.
      replace (a + 1 + k) with (a + S k) by lia.
      apply Hsec. simpl. lia.
    + intros x tbx Hx HMx.
      unfold mem_set in Hx.
      destruct (Nat.eqb x a) eqn:E.
      * apply Nat.eqb_eq in E. subst x.
        assert (HMa : M (a + 0) = true) by (apply Hsec; simpl; lia).
        rewrite Nat.add_0_r in HMa. congruence.
      * eapply Hag; eauto.
Qed.

Lemma unpack_le_length :
  forall k n, length (unpack_le n k) = k.
Proof.
  induction k as [| k IH]; intros n; simpl; [reflexivity |].
  rewrite IH. reflexivity.
Qed.

Lemma map_mk_tbyte_untainted :
  forall bs, Forall (fun tb => tb_taint tb = false)
                    (map (fun b => mk_tbyte b false) bs).
Proof.
  induction bs as [| b bs IH]; simpl; constructor; [reflexivity | exact IH].
Qed.

(* ------------------------------------------------------------------ *)
(* Typing rules                                                        *)
(* ------------------------------------------------------------------ *)

Inductive instr_mty (M : addr -> taint) : msty -> instr -> msty -> Prop :=
| MTyNop : forall S,
    instr_mty M S Nop S
| MTyAdd : forall S rd rs1 rs2,
    instr_mty M S (Add rd rs1 rs2) (upd_reg S rd (t_or (rt S rs1) (rt S rs2)))
| MTyMul : forall S rd rs1 rs2,
    instr_mty M S (Mul rd rs1 rs2) (upd_reg S rd (t_or (rt S rs1) (rt S rs2)))
| MTyLoadTop : forall S sz rd base off,
    rt S base = false ->                (* address public, unknown *)
    instr_mty M S (Load sz rd base off) (upd_reg S rd true)
| MTyLoadPrec : forall S sz rd base off a,
    pt S base = Some a ->               (* statically known footprint *)
    instr_mty M S (Load sz rd base off)
              (upd_reg S rd (region_taint M (a + off) (size_bytes sz)))
| MTyStorePub : forall S sz rs base off,
    rt S base = false ->
    rt S rs = false ->                  (* public data goes anywhere *)
    instr_mty M S (Store sz rs base off) S
| MTyStoreSec : forall S sz rs base off a,
    pt S base = Some a ->               (* known footprint ... *)
    (forall k, k < size_bytes sz -> M (a + off + k) = true) ->
    (* ... entirely inside the secret region: rs may be secret *)
    instr_mty M S (Store sz rs base off) S.

Inductive term_mty (P : prog) (Θ : label -> msty) : msty -> term -> Prop :=
| MTyHalt : forall S,
    term_mty P Θ S THalt
| MTyJmp : forall S l b,
    P l = Some b ->
    msty_sub S (Θ l) ->
    term_mty P Θ S (TJmp l)
| MTyBrZero : forall S r l1 l2 b1 b2,
    rt S r = false ->
    P l1 = Some b1 ->
    P l2 = Some b2 ->
    msty_sub S (Θ l1) ->
    msty_sub S (Θ l2) ->
    term_mty P Θ S (TBrZero r l1 l2).

Inductive instrs_mty (M : addr -> taint) : msty -> list instr -> msty -> Prop :=
| IMTNil : forall S,
    instrs_mty M S [] S
| IMTCons : forall S i S' l S'',
    instr_mty M S i S' ->
    instrs_mty M S' l S'' ->
    instrs_mty M S (i :: l) S''.

Definition block_mty (M : addr -> taint) (P : prog) (Θ : label -> msty)
           (S : msty) (b : block) : Prop :=
  exists S_end,
    instrs_mty M S (code b) S_end /\ term_mty P Θ S_end (termi b).

Definition program_typed2 (M : addr -> taint) (P : prog)
           (Θ : label -> msty) : Prop :=
  forall l b, P l = Some b -> block_mty M P Θ (Θ l) b.

(* ------------------------------------------------------------------ *)
(* The concrete tyenv                                                  *)
(* ------------------------------------------------------------------ *)

Definition point_ok2 (M : addr -> taint) (P : prog) (Θ : label -> msty)
           (p : pc) (S : msty) : Prop :=
  exists b,
    P (pc_lbl p) = Some b /\
    pc_ix p <= length (code b) /\
    exists S_end,
      instrs_mty M S (skipn (pc_ix p) (code b)) S_end /\
      term_mty P Θ S_end (termi b).

Definition gamma2 (M : addr -> taint) (P : prog) (Θ : label -> msty) : tyenv :=
  fun p s =>
    mem_total (mm s) /\
    exists S, point_ok2 M P Θ p S /\ msat M S s.

(* ------------------------------------------------------------------ *)
(* Progress                                                            *)
(* ------------------------------------------------------------------ *)

Lemma instr_mty_progress :
  forall M S i S' s,
    instr_mty M S i S' ->
    msat M S s ->
    mem_total (mm s) ->
    instr_safe s i.
Proof.
  intros M S i S' s Hty (H1 & H2 & H3) Htot.
  unfold instr_safe.
  destruct Hty; simpl.
  - eexists; reflexivity.
  - eexists; reflexivity.
  - eexists; reflexivity.
  - (* LoadTop *)
    rewrite (H1 base H).
    destruct (load_bytes_total (size_bytes sz) (mm s)
                (tv_val (rf s base) + off) Htot) as [tbs Hl].
    rewrite Hl. eexists; reflexivity.
  - (* LoadPrec *)
    rewrite (H2 base a H). simpl.
    destruct (load_bytes_total (size_bytes sz) (mm s) (a + off) Htot)
      as [tbs Hl].
    rewrite Hl. eexists; reflexivity.
  - (* StorePub *)
    rewrite (H1 base H). eexists; reflexivity.
  - (* StoreSec *)
    rewrite (H2 base a H). simpl. eexists; reflexivity.
Qed.

Lemma term_mty_progress :
  forall P Θ S t s,
    term_mty P Θ S t ->
    (forall r, rt S r = false -> tv_taint (rf s r) = false) ->
    term_safe s t.
Proof.
  intros P Θ S t s Hty H1.
  destruct Hty.
  - left; reflexivity.
  - right; eexists; reflexivity.
  - right. simpl. rewrite (H1 r H).
    destruct (Nat.eqb (tv_val (rf s r)) 0); eexists; reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(* Preservation of satisfaction by instructions                        *)
(* ------------------------------------------------------------------ *)

Lemma instr_mty_preserves_msat :
  forall M S i S' s s',
    instr_mty M S i S' ->
    msat M S s ->
    exec_instr s i = Some s' ->
    msat M S' s'.
Proof.
  intros M S i S' s s' Hty (H1 & H2 & H3) Hex.
  destruct Hty; simpl in Hex.
  - (* Nop *)
    injection Hex as <-. split; [| split]; simpl; assumption.
  - (* Add *)
    injection Hex as <-. split; [| split]; simpl.
    + intros r Hr. simpl in Hr. unfold regs_set.
      destruct (Nat.eqb r rd) eqn:E.
      * unfold t_or in Hr. apply Bool.orb_false_iff in Hr.
        destruct Hr as [Ha Hb].
        simpl. unfold t_or. rewrite (H1 rs1 Ha), (H1 rs2 Hb). reflexivity.
      * apply H1. exact Hr.
    + intros r a Hr. simpl in Hr. unfold regs_set.
      destruct (Nat.eqb r rd) eqn:E; [discriminate |].
      apply H2. exact Hr.
    + exact H3.
  - (* Mul *)
    injection Hex as <-. split; [| split]; simpl.
    + intros r Hr. simpl in Hr. unfold regs_set.
      destruct (Nat.eqb r rd) eqn:E.
      * unfold t_or in Hr. apply Bool.orb_false_iff in Hr.
        destruct Hr as [Ha Hb].
        simpl. unfold t_or. rewrite (H1 rs1 Ha), (H1 rs2 Hb). reflexivity.
      * apply H1. exact Hr.
    + intros r a Hr. simpl in Hr. unfold regs_set.
      destruct (Nat.eqb r rd) eqn:E; [discriminate |].
      apply H2. exact Hr.
    + exact H3.
  - (* LoadTop *)
    destruct (tv_taint (rf s base)); [discriminate |].
    destruct (load_bytes (mm s) (tv_val (rf s base) + off) (size_bytes sz))
      as [tbs |] eqn:El; [| discriminate].
    injection Hex as <-. split; [| split]; simpl.
    + intros r Hr. simpl in Hr. unfold regs_set.
      destruct (Nat.eqb r rd) eqn:E; [discriminate |].
      apply H1. exact Hr.
    + intros r a Hr. simpl in Hr. unfold regs_set.
      destruct (Nat.eqb r rd) eqn:E; [discriminate |].
      apply H2. exact Hr.
    + exact H3.
  - (* LoadPrec *)
    rewrite (H2 base a H) in Hex. simpl in Hex.
    destruct (load_bytes (mm s) (a + off) (size_bytes sz))
      as [tbs |] eqn:El; [| discriminate].
    injection Hex as <-. split; [| split]; simpl.
    + intros r Hr. simpl in Hr. unfold regs_set.
      destruct (Nat.eqb r rd) eqn:E.
      * (* the loaded footprint is untainted *)
        simpl.
        eapply load_bytes_region_taint; eauto.
      * apply H1. exact Hr.
    + intros r a' Hr. simpl in Hr. unfold regs_set.
      destruct (Nat.eqb r rd) eqn:E; [discriminate |].
      apply H2. exact Hr.
    + exact H3.
  - (* StorePub *)
    rewrite (H1 base H) in Hex.
    injection Hex as <-. split; [| split]; simpl.
    + exact H1.
    + exact H2.
    + rewrite (H1 rs H0).
      apply store_untainted_agrees; [apply map_mk_tbyte_untainted | exact H3].
  - (* StoreSec *)
    rewrite (H2 base a H) in Hex. simpl in Hex.
    injection Hex as <-. split; [| split]; simpl.
    + exact H1.
    + exact H2.
    + apply store_secret_agrees; [| exact H3].
      intros k Hk.
      rewrite length_map, unpack_le_length in Hk.
      apply H0. exact Hk.
Qed.

(* ------------------------------------------------------------------ *)
(* Inversion helpers for terminator typing                             *)
(* ------------------------------------------------------------------ *)

Lemma term_mty_jmp_inv :
  forall P Θ S l,
    term_mty P Θ S (TJmp l) ->
    exists b, P l = Some b /\ msty_sub S (Θ l).
Proof.
  intros P Θ S l H. inversion H; subst. eauto.
Qed.

Lemma term_mty_br_inv :
  forall P Θ S r l1 l2,
    term_mty P Θ S (TBrZero r l1 l2) ->
    rt S r = false /\
    (exists b1, P l1 = Some b1) /\
    (exists b2, P l2 = Some b2) /\
    msty_sub S (Θ l1) /\ msty_sub S (Θ l2).
Proof.
  intros P Θ S r l1 l2 H. inversion H; subst. eauto 8.
Qed.

(* ------------------------------------------------------------------ *)
(* From Γ to full well-formedness                                      *)
(* ------------------------------------------------------------------ *)

Lemma gamma2_wf_state :
  forall M P Θ s,
    program_typed2 M P Θ ->
    gamma2 M P Θ (pcv s) s ->
    wf_state P (gamma2 M P Θ) s.
Proof.
  intros M P Θ s HPT Hg.
  split; [exact Hg |].
  destruct Hg as (Htot & S & Hpt & Hsat).
  destruct Hpt as (b & Hb & Hix & S_end & Hchain & Htm).
  destruct (nth_opt (pc_ix (pcv s)) (code b)) as [i |] eqn:E.
  - assert (Hf : fetch P (pcv s) = Some (FInstr i)).
    { unfold fetch. rewrite Hb, E. reflexivity. }
    rewrite Hf.
    rewrite (skipn_nth_some _ _ _ _ E) in Hchain.
    inversion Hchain; subst.
    eapply instr_mty_progress; eauto.
  - assert (Hlen : pc_ix (pcv s) = length (code b)).
    { apply nth_opt_none_ge in E. lia. }
    assert (Hf : fetch P (pcv s) = Some (FTerm (termi b))).
    { unfold fetch. rewrite Hb, E, Hlen, Nat.eqb_refl. reflexivity. }
    rewrite Hf.
    rewrite Hlen in Hchain. rewrite skipn_all in Hchain.
    inversion Hchain; subst.
    destruct Hsat as (H1 & _ & _).
    eapply term_mty_progress; eauto.
Qed.

(* ------------------------------------------------------------------ *)
(* Γ is preserved by steps                                             *)
(* ------------------------------------------------------------------ *)

Lemma gamma2_preserved :
  forall M P Θ s s',
    program_typed2 M P Θ ->
    gamma2 M P Θ (pcv s) s ->
    step P s s' ->
    gamma2 M P Θ (pcv s') s'.
Proof.
  intros M P Θ s s' HPT Hg Hstep.
  destruct Hg as (Htot & S & (b & Hb & Hix & S_end & Hchain & Htm) & Hsat).
  inversion Hstep as [s0 i s1 Hf Hex | s0 t s1 Hf Hex]; subst.
  - (* instruction step *)
    pose proof (fetch_inv_instr _ _ _ _ Hb Hf) as Hnth.
    rewrite (skipn_nth_some _ _ _ _ Hnth) in Hchain.
    inversion Hchain as [| S0 i0 S' l0 S''0 Hi Hrest]; subst.
    assert (Hpc : pcv s' = pc_next (pcv s)) by (eapply exec_instr_pc; eauto).
    split.
    + eapply exec_instr_mem; eauto.
    + exists S'. split.
      * exists b. rewrite Hpc. simpl. split; [exact Hb |]. split.
        { apply nth_opt_some_lt in Hnth. lia. }
        exists S_end. split; [exact Hrest | exact Htm].
      * eapply instr_mty_preserves_msat; eauto.
  - (* terminator step *)
    destruct (fetch_inv_term _ _ _ _ Hb Hf) as [Ht Hlen].
    rewrite Hlen in Hchain. rewrite skipn_all in Hchain.
    inversion Hchain; subst.
    revert Htm Hex.
    generalize (termi b).
    intros tb Htm Hex.
    destruct tb as [l' | rr l1 l2 |].
    + (* TJmp *)
      apply term_mty_jmp_inv in Htm.
      destruct Htm as (b' & Hb' & Hsub).
      simpl in Hex. injection Hex as <-.
      split; [exact Htot |].
      exists (Θ l'). split.
      * exists b'. simpl. split; [exact Hb' |]. split; [lia |].
        destruct (HPT l' b' Hb') as (S_end' & Hchain' & Htm').
        exists S_end'. split; [exact Hchain' | exact Htm'].
      * assert (Hsat' : msat M (Θ l') s) by (eapply msat_sub; eauto).
        destruct Hsat' as (Ha & Hbp & Hc).
        split; [| split]; simpl; assumption.
    + (* TBrZero *)
      apply term_mty_br_inv in Htm.
      destruct Htm as (Hrr & (b1 & Hb1) & (b2 & Hb2) & Hsub1 & Hsub2).
      destruct Hsat as (H1 & H2 & H3).
      simpl in Hex.
      rewrite (H1 rr Hrr) in Hex.
      destruct (Nat.eqb (tv_val (rf s rr)) 0) eqn:Ez;
        injection Hex as <-.
      * split; [exact Htot |].
        exists (Θ l1). split.
        -- exists b1. simpl. split; [exact Hb1 |]. split; [lia |].
           destruct (HPT l1 b1 Hb1) as (S_end' & Hchain' & Htm').
           exists S_end'. split; [exact Hchain' | exact Htm'].
        -- assert (Hsat' : msat M (Θ l1) s)
             by (eapply msat_sub; eauto; split; [|split]; assumption).
           destruct Hsat' as (Ha & Hbp & Hc).
           split; [| split]; simpl; assumption.
      * split; [exact Htot |].
        exists (Θ l2). split.
        -- exists b2. simpl. split; [exact Hb2 |]. split; [lia |].
           destruct (HPT l2 b2 Hb2) as (S_end' & Hchain' & Htm').
           exists S_end'. split; [exact Hchain' | exact Htm'].
        -- assert (Hsat' : msat M (Θ l2) s)
             by (eapply msat_sub; eauto; split; [|split]; assumption).
           destruct Hsat' as (Ha & Hbp & Hc).
           split; [| split]; simpl; assumption.
    + (* THalt *)
      simpl in Hex. discriminate.
Qed.

(* ------------------------------------------------------------------ *)
(* Main results                                                        *)
(* ------------------------------------------------------------------ *)

Theorem program_typed2_tyenv_preserves :
  forall M P Θ,
    program_typed2 M P Θ ->
    tyenv_preserves P (gamma2 M P Θ).
Proof.
  intros M P Θ HPT s s' Hwf Hstep.
  destruct Hwf as [Hg _].
  apply gamma2_wf_state; [exact HPT |].
  eapply gamma2_preserved; eauto.
Qed.

Theorem typed_type_safety2 :
  forall M P Θ s,
    program_typed2 M P Θ ->
    wf_state P (gamma2 M P Θ) s ->
    (exists s', step P s s' /\ wf_state P (gamma2 M P Θ) s') \/ terminal P s.
Proof.
  intros M P Θ s HPT Hwf.
  apply type_safety.
  - apply program_typed2_tyenv_preserves. exact HPT.
  - exact Hwf.
Qed.

Theorem typed_start_wf2 :
  forall M P Θ s l b,
    program_typed2 M P Θ ->
    pcv s = pc_jump l ->
    P l = Some b ->
    mem_total (mm s) ->
    msat M (Θ l) s ->
    wf_state P (gamma2 M P Θ) s.
Proof.
  intros M P Θ s l b HPT Hpc Hb Htot Hsat.
  apply gamma2_wf_state; [exact HPT |].
  split; [exact Htot |].
  exists (Θ l). split.
  - exists b. rewrite Hpc. simpl. split; [exact Hb |]. split; [lia |].
    destruct (HPT l b Hb) as (S_end & Hchain & Htm).
    exists S_end. split; [exact Hchain | exact Htm].
  - exact Hsat.
Qed.

(* ------------------------------------------------------------------ *)
(* Demonstration of the precision gain                                 *)
(*                                                                     *)
(* The program below has EXACTLY the shape of the Phase-1 negative     *)
(* example (Test.v: Pbad_untypeable): load a byte, then branch on it.  *)
(* In Phase 1 it is untypeable for every entry type.  In Phase 2 it    *)
(* types, because r1 is a known pointer into public memory (M = all    *)
(* public), so the loaded value is provably untainted.                 *)
(* ------------------------------------------------------------------ *)

Definition M0 : addr -> taint := fun _ => false.

Definition blkL : block := {| code := [Load S1 0 1 0]; termi := TBrZero 0 1 1 |}.
Definition blkH : block := {| code := []; termi := THalt |}.

Definition PL : prog :=
  fun l => match l with 0 => Some blkL | 1 => Some blkH | _ => None end.

Definition SL : msty :=
  {| rt := fun _ => false;
     pt := fun r => if Nat.eqb r 1 then Some 100 else None |}.
Definition Smax : msty :=
  {| rt := fun _ => true; pt := fun _ => None |}.

Definition ThL : label -> msty :=
  fun l => match l with 0 => SL | _ => Smax end.

Lemma PL_typed : program_typed2 M0 PL ThL.
Proof.
  intros l b Hb.
  destruct l as [| [| l]]; simpl in Hb; inversion Hb; subst; clear Hb.
  - (* block 0: precise load, then branch on the loaded (public) value *)
    eexists. split.
    + eapply IMTCons; [eapply MTyLoadPrec; reflexivity | apply IMTNil].
    + eapply MTyBrZero.
      * (* the loaded value is public: region_taint of public memory *)
        reflexivity.
      * reflexivity.
      * reflexivity.
      * split; [intros r _; reflexivity | intros r a Hp; discriminate].
      * split; [intros r _; reflexivity | intros r a Hp; discriminate].
  - eexists. split; [apply IMTNil | apply MTyHalt].
Qed.

(* It also runs: r1 = 100 (a pointer into public memory), the loaded
   byte is 7, and the branch on it proceeds (to block 1) and halts. *)
Definition rfL : regs :=
  fun r => if Nat.eqb r 1 then mk_tval 100 false else mk_tval 0 false.
Definition mmL : mem := fun _ => Some (mk_tbyte 7 false).
Definition sL : state := {| pcv := pc_jump 0; rf := rfL; mm := mmL |}.

Lemma sL_wf : wf_state PL (gamma2 M0 PL ThL) sL.
Proof.
  eapply typed_start_wf2 with (l := 0) (b := blkL).
  - exact PL_typed.
  - reflexivity.
  - reflexivity.
  - intros a. eexists. reflexivity.
  - split; [| split].
    + intros r _. unfold sL, rfL. simpl.
      destruct (Nat.eqb r 1); reflexivity.
    + intros r a Hp. unfold ThL, SL in Hp. simpl in Hp.
      destruct (Nat.eqb r 1) eqn:E; [| discriminate].
      injection Hp as <-. unfold sL, rfL. simpl. rewrite E. reflexivity.
    + intros a tb Ha _. unfold sL, mmL in Ha. simpl in Ha.
      injection Ha as <-. reflexivity.
Qed.

Lemma PL_runs :
  exists s1 s2,
    step PL sL s1 /\ step PL s1 s2 /\ terminal PL s2.
Proof.
  eexists. eexists.
  split; [| split].
  - eapply StepInstr; reflexivity.
  - eapply StepTerm; reflexivity.
  - reflexivity.
Qed.
