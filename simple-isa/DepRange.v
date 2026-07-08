Set Warnings "-notation-overridden".
From Stdlib Require Import Arith Nat Bool Lia Lists.List.
Import ListNotations.
From SimpleIsa Require Import Syntax Machine Safety Typing.

(* ===================================================================== *)
(* Phase 3 (Checkpoint C4): dependent value-range types and memory       *)
(* safety.                                                               *)
(*                                                                       *)
(* State types now carry a constraint context Δ (the paper's Δ ⊢ ...)    *)
(* over register VALUES: linear inequalities between expressions built   *)
(* from registers and constants.  Memory is a fixed set of declared      *)
(* disjoint REGIONS, each with a taint classification; only addresses    *)
(* inside declared regions are guaranteed mapped.  Load/Store must       *)
(* prove — via an abstract, SOUND entailment oracle standing in for the  *)
(* paper's SMT solver — that the whole access footprint lies inside a    *)
(* declared region.  This gives:                                         *)
(*   - memory safety: typed loads never touch unmapped addresses        *)
(*     (mem_total is GONE in this phase);                                *)
(*   - precise taint: a load from a public region is public.            *)
(*                                                                       *)
(* Per the ground rules, the entailment oracle is introduced ONLY as a   *)
(* Section variable with a soundness hypothesis; closing the section     *)
(* discharges both into the theorem statements, so `Print Assumptions`   *)
(* on the exported theorems remains closed under the global context.     *)
(* ===================================================================== *)

(* ------------------------------------------------------------------ *)
(* Constraint language                                                 *)
(* ------------------------------------------------------------------ *)

Inductive cexpr : Type :=
| CReg   : reg -> cexpr
| CConst : nat -> cexpr
| CAdd   : cexpr -> cexpr -> cexpr.

Inductive constraint : Type :=
| CLe : cexpr -> cexpr -> constraint.       (* e1 <= e2 *)

Definition venv := reg -> val.

Fixpoint ceval (V : venv) (e : cexpr) : val :=
  match e with
  | CReg r => V r
  | CConst n => n
  | CAdd e1 e2 => ceval V e1 + ceval V e2
  end.

Definition csat (V : venv) (c : constraint) : Prop :=
  match c with CLe e1 e2 => ceval V e1 <= ceval V e2 end.

Definition ctx := list constraint.

Definition ctx_sat (V : venv) (D : ctx) : Prop := Forall (csat V) D.

(* Which registers an expression / constraint mentions. *)
Fixpoint e_mentions (r : reg) (e : cexpr) : bool :=
  match e with
  | CReg r' => Nat.eqb r' r
  | CConst _ => false
  | CAdd e1 e2 => orb (e_mentions r e1) (e_mentions r e2)
  end.

Definition c_mentions (r : reg) (c : constraint) : bool :=
  match c with CLe e1 e2 => orb (e_mentions r e1) (e_mentions r e2) end.

(* Havoc: forget everything about register r. *)
Definition havoc (r : reg) (D : ctx) : ctx :=
  filter (fun c => negb (c_mentions r c)) D.

Lemma ceval_agree :
  forall e V1 V2,
    (forall r, e_mentions r e = true -> V1 r = V2 r) ->
    ceval V1 e = ceval V2 e.
Proof.
  induction e as [r | n | e1 IH1 e2 IH2]; intros V1 V2 Hag; simpl.
  - apply Hag. simpl. apply Nat.eqb_refl.
  - reflexivity.
  - assert (Ha : ceval V1 e1 = ceval V2 e1).
    { apply IH1. intros r Hr. apply Hag. simpl. rewrite Hr. reflexivity. }
    assert (Hb : ceval V1 e2 = ceval V2 e2).
    { apply IH2. intros r Hr. apply Hag. simpl. rewrite Hr.
      apply Bool.orb_true_r. }
    rewrite Ha, Hb. reflexivity.
Qed.

Lemma csat_agree :
  forall c V1 V2,
    (forall r, c_mentions r c = true -> V1 r = V2 r) ->
    csat V1 c -> csat V2 c.
Proof.
  intros [e1 e2] V1 V2 Hag Hs. simpl in *.
  assert (Ha : ceval V1 e1 = ceval V2 e1).
  { apply ceval_agree. intros r Hr. apply Hag. rewrite Hr. reflexivity. }
  assert (Hb : ceval V1 e2 = ceval V2 e2).
  { apply ceval_agree. intros r Hr. apply Hag. rewrite Hr.
    apply Bool.orb_true_r. }
  rewrite <- Ha, <- Hb. exact Hs.
Qed.

(* Havocing r is sound for any new valuation that agrees off r. *)
Lemma havoc_sound :
  forall r D V V',
    ctx_sat V D ->
    (forall r', r' <> r -> V' r' = V r') ->
    ctx_sat V' (havoc r D).
Proof.
  intros r D V V' Hsat Hag.
  unfold ctx_sat in *.
  apply Forall_forall. intros c Hin.
  unfold havoc in Hin. apply filter_In in Hin.
  destruct Hin as [Hin Hnm].
  apply Bool.negb_true_iff in Hnm.
  rewrite Forall_forall in Hsat.
  apply (csat_agree c V V').
  - intros r0 Hr0. symmetry. apply Hag.
    intros ->. congruence.
  - apply Hsat. exact Hin.
Qed.

Lemma unpack_le_length3 :
  forall k n, length (unpack_le n k) = k.
Proof.
  induction k as [| k IH]; intros n; simpl; [reflexivity |].
  rewrite IH. reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(* Declared memory regions                                             *)
(* ------------------------------------------------------------------ *)

Record region : Type := {
  rlo  : addr;    (* first address *)
  rlen : nat;     (* length in bytes *)
  rtnt : taint;   (* static taint classification of the region *)
}.

Definition r_contains (rg : region) (a : addr) : Prop :=
  rlo rg <= a < rlo rg + rlen rg.

(* Declared regions must be pairwise disjoint (a side condition on the
   program's region declaration). *)
Definition regions_disjoint (RS : list region) : Prop :=
  forall rg1 rg2 a,
    In rg1 RS -> In rg2 RS ->
    r_contains rg1 a -> r_contains rg2 a ->
    rg1 = rg2.

(* Memory invariants relative to the declared regions:
   - validity: region addresses are mapped (NO global mem_total here);
   - agreement: bytes in public regions are untainted. *)
Definition mem_valid (RS : list region) (m : mem) : Prop :=
  forall rg a, In rg RS -> r_contains rg a -> m a <> None.

Definition mem_agrees3 (RS : list region) (m : mem) : Prop :=
  forall rg a tb,
    In rg RS -> r_contains rg a -> rtnt rg = false ->
    m a = Some tb -> tb_taint tb = false.

(* ------------------------------------------------------------------ *)
(* State types with a constraint context                               *)
(* ------------------------------------------------------------------ *)

Record sty3 : Type := {
  rt3  : reg -> taint;
  dctx : ctx;
}.

Definition upd3 (S : sty3) (x : reg) (t : taint) (D : ctx) : sty3 :=
  {| rt3 := fun y => if Nat.eqb y x then t else rt3 S y;
     dctx := D |}.

Definition vals_of (s : state) : venv := fun r => tv_val (rf s r).

Definition sat3 (RS : list region) (S : sty3) (s : state) : Prop :=
  (forall r, rt3 S r = false -> tv_taint (rf s r) = false) /\
  ctx_sat (vals_of s) (dctx S) /\
  mem_valid RS (mm s) /\
  mem_agrees3 RS (mm s).

(* ------------------------------------------------------------------ *)
(* Generic memory lemmas (no entailment involved)                      *)
(* ------------------------------------------------------------------ *)

Lemma load_bytes_defined :
  forall n m a,
    (forall k, k < n -> m (a + k) <> None) ->
    exists tbs, load_bytes m a n = Some tbs.
Proof.
  induction n as [| n IH]; intros m a Hdef; simpl.
  - eexists; reflexivity.
  - destruct (m a) as [tb |] eqn:Ema.
    + destruct (IH m (a + 1)) as [tbs Htbs].
      * intros k Hk. replace (a + 1 + k) with (a + S k) by lia.
        apply Hdef. lia.
      * rewrite Htbs. eexists; reflexivity.
    + exfalso. apply (Hdef 0); [lia |]. rewrite Nat.add_0_r. exact Ema.
Qed.

(* Loading a footprint of provably-untainted addresses yields an
   untainted value. *)
Lemma load_bytes_untainted_in :
  forall (Pub : addr -> Prop) n m a tbs,
    (forall x tb, Pub x -> m x = Some tb -> tb_taint tb = false) ->
    (forall k, k < n -> Pub (a + k)) ->
    load_bytes m a n = Some tbs ->
    tbytes_taint tbs = false.
Proof.
  intros Pub n; induction n as [| n IH]; intros m a tbs Hp Hin Hl; simpl in Hl.
  - injection Hl as <-. reflexivity.
  - destruct (m a) as [tb |] eqn:Ema; [| discriminate].
    destruct (load_bytes m (a + 1) n) as [tbs' |] eqn:El; [| discriminate].
    injection Hl as <-.
    unfold tbytes_taint. simpl. unfold t_or.
    apply Bool.orb_false_iff. split.
    + apply (Hp a tb); [| exact Ema].
      specialize (Hin 0 (Nat.lt_0_succ n)). rewrite Nat.add_0_r in Hin.
      exact Hin.
    + apply (IH m (a + 1) tbs' Hp); [| exact El].
      intros k Hk. replace (a + 1 + k) with (a + S k) by lia.
      apply Hin. lia.
Qed.

(* Stores never unmap addresses. *)
Lemma store_bytes_preserves_defined :
  forall tbs m a x,
    m x <> None ->
    store_bytes m a tbs x <> None.
Proof.
  induction tbs as [| tb tbs IH]; intros m a x Hx; simpl.
  - exact Hx.
  - apply IH. unfold mem_set.
    destruct (Nat.eqb x a); [discriminate | exact Hx].
Qed.

(* Addresses outside the written footprint are unchanged. *)
Lemma store_bytes_outside :
  forall tbs m a x,
    (x < a \/ a + length tbs <= x) ->
    store_bytes m a tbs x = m x.
Proof.
  induction tbs as [| tb tbs IH]; intros m a x Hout; simpl.
  - reflexivity.
  - simpl in Hout.
    rewrite IH by lia.
    unfold mem_set.
    destruct (Nat.eqb x a) eqn:E.
    + apply Nat.eqb_eq in E. lia.
    + reflexivity.
Qed.

(* Storing untainted bytes preserves agreement (at any address). *)
Lemma store_untainted_agrees3 :
  forall RS tbs m a,
    Forall (fun tb => tb_taint tb = false) tbs ->
    mem_agrees3 RS m ->
    mem_agrees3 RS (store_bytes m a tbs).
Proof.
  intros RS tbs; induction tbs as [| tb tbs IH]; intros m a Hall Hag; simpl.
  - exact Hag.
  - inversion Hall as [| x0 l0 Hhd Htl]; subst.
    apply IH; [exact Htl |].
    intros rg x tbx Hin Hc Ht Hx.
    unfold mem_set in Hx.
    destruct (Nat.eqb x a) eqn:E.
    + injection Hx as <-. exact Hhd.
    + eapply Hag; eauto.
Qed.

(* Storing anything with a footprint inside a SECRET region preserves
   agreement, provided regions are disjoint. *)
Lemma store_secret_agrees3 :
  forall RS rg tbs m a,
    regions_disjoint RS ->
    In rg RS ->
    rtnt rg = true ->
    (forall k, k < length tbs -> r_contains rg (a + k)) ->
    mem_agrees3 RS m ->
    mem_agrees3 RS (store_bytes m a tbs).
Proof.
  intros RS rg tbs m a Hdisj Hin Hsec Hfoot Hag.
  intros rg' x tbx Hin' Hc' Ht' Hx.
  destruct (Nat.lt_ge_cases x a) as [Hlt | Hge].
  - (* below the footprint: unchanged *)
    rewrite store_bytes_outside in Hx by lia.
    eapply Hag; eauto.
  - destruct (Nat.lt_ge_cases x (a + length tbs)) as [Hin_fp | Hout].
    + (* inside the footprint: x lies in the secret region rg, and in
         the public region rg' — contradiction with disjointness *)
      exfalso.
      assert (Hcx : r_contains rg x).
      { replace x with (a + (x - a)) by lia.
        apply Hfoot. lia. }
      specialize (Hdisj rg' rg x Hin' Hin Hc' Hcx). subst rg'.
      congruence.
    + (* above the footprint: unchanged *)
      rewrite store_bytes_outside in Hx by lia.
      eapply Hag; eauto.
Qed.

Lemma map_mk_tbyte_untainted3 :
  forall bs, Forall (fun tb => tb_taint tb = false)
                    (map (fun b => mk_tbyte b false) bs).
Proof.
  induction bs as [| b bs IH]; simpl; constructor; [reflexivity | exact IH].
Qed.

(* ================================================================== *)
(* The typing system, parameterized by a SOUND entailment oracle.      *)
(*                                                                     *)
(* This Section is the ONLY permitted abstraction for the paper's SMT  *)
(* entailment Δ ⊢ c: `entails` is a Section variable, its soundness a  *)
(* Section hypothesis.  Both are discharged into the statements of the *)
(* theorems below when the Section closes; nothing is axiomatized      *)
(* globally.                                                           *)
(* ================================================================== *)

Section WithEntails.

  Variable entails : ctx -> constraint -> bool.

  Hypothesis entails_sound :
    forall D c,
      entails D c = true ->
      forall V, ctx_sat V D -> csat V c.

  (* The fixed, statically declared memory regions. *)
  Variable RS : list region.
  Hypothesis RS_disjoint : regions_disjoint RS.

  (* ---------------------------------------------------------------- *)
  (* Subtyping                                                         *)
  (* ---------------------------------------------------------------- *)

  Definition ctx_impl (D1 D2 : ctx) : bool := forallb (entails D1) D2.

  Lemma ctx_impl_sound :
    forall D1 D2 V,
      ctx_impl D1 D2 = true -> ctx_sat V D1 -> ctx_sat V D2.
  Proof.
    intros D1 D2 V Himp Hsat.
    unfold ctx_impl in Himp. rewrite forallb_forall in Himp.
    unfold ctx_sat.
    apply Forall_forall. intros c Hin.
    eapply entails_sound; eauto.
  Qed.

  Definition sty3_sub (S1 S2 : sty3) : Prop :=
    (forall r, rt3 S1 r = true -> rt3 S2 r = true) /\
    ctx_impl (dctx S1) (dctx S2) = true.

  Lemma sat3_sub :
    forall S1 S2 s, sty3_sub S1 S2 -> sat3 RS S1 s -> sat3 RS S2 s.
  Proof.
    intros S1 S2 s [Hrt Himp] (H1 & H2 & H3 & H4).
    split; [| split; [| split]].
    - intros r Hr2. destruct (rt3 S1 r) eqn:E1.
      + apply Hrt in E1. congruence.
      + apply H1. exact E1.
    - eapply ctx_impl_sound; eauto.
    - exact H3.
    - exact H4.
  Qed.

  (* ---------------------------------------------------------------- *)
  (* Footprint side conditions, via the entailment oracle              *)
  (* ---------------------------------------------------------------- *)

  (* The footprint  [base+off, base+off+n)  lies inside region rg. *)
  Definition footprint_in (D : ctx) (base : reg) (off n : nat)
             (rg : region) : Prop :=
    entails D (CLe (CConst (rlo rg)) (CAdd (CReg base) (CConst off))) = true /\
    entails D (CLe (CAdd (CReg base) (CConst (off + n)))
                   (CConst (rlo rg + rlen rg))) = true.

  Lemma footprint_in_sound :
    forall D base off n rg V,
      footprint_in D base off n rg ->
      ctx_sat V D ->
      forall k, k < n -> r_contains rg (V base + off + k).
  Proof.
    intros D base off n rg V [Hlo Hhi] Hsat k Hk.
    apply (entails_sound _ _ Hlo) in Hsat as Hlo'.
    apply (entails_sound _ _ Hhi) in Hsat as Hhi'.
    simpl in Hlo', Hhi'.
    unfold r_contains. lia.
  Qed.

  (* ---------------------------------------------------------------- *)
  (* Typing rules                                                      *)
  (* ---------------------------------------------------------------- *)

  Inductive instr_ty3 : sty3 -> instr -> sty3 -> Prop :=
  | T3Nop : forall S,
      instr_ty3 S Nop S
  | T3AddHavoc : forall S rd rs1 rs2,
      instr_ty3 S (Add rd rs1 rs2)
        (upd3 S rd (t_or (rt3 S rs1) (rt3 S rs2)) (havoc rd (dctx S)))
  | T3AddExact : forall S rd rs1 rs2,
      rd <> rs1 -> rd <> rs2 ->
      instr_ty3 S (Add rd rs1 rs2)
        (upd3 S rd (t_or (rt3 S rs1) (rt3 S rs2))
              (CLe (CReg rd) (CAdd (CReg rs1) (CReg rs2)) ::
               CLe (CAdd (CReg rs1) (CReg rs2)) (CReg rd) ::
               havoc rd (dctx S)))
  | T3MulHavoc : forall S rd rs1 rs2,
      instr_ty3 S (Mul rd rs1 rs2)
        (upd3 S rd (t_or (rt3 S rs1) (rt3 S rs2)) (havoc rd (dctx S)))
  | T3Load : forall S sz rd base off rg,
      In rg RS ->
      rt3 S base = false ->
      footprint_in (dctx S) base off (size_bytes sz) rg ->
      instr_ty3 S (Load sz rd base off)
        (upd3 S rd (rtnt rg) (havoc rd (dctx S)))
  | T3Store : forall S sz rs base off rg,
      In rg RS ->
      rt3 S base = false ->
      footprint_in (dctx S) base off (size_bytes sz) rg ->
      (rt3 S rs = false \/ rtnt rg = true) ->
      instr_ty3 S (Store sz rs base off) S.

  Inductive term_ty3 (P : prog) (Θ : label -> sty3) : sty3 -> term -> Prop :=
  | T3Halt : forall S,
      term_ty3 P Θ S THalt
  | T3Jmp : forall S l b,
      P l = Some b ->
      sty3_sub S (Θ l) ->
      term_ty3 P Θ S (TJmp l)
  | T3BrZero : forall S r l1 l2 b1 b2,
      rt3 S r = false ->
      P l1 = Some b1 ->
      P l2 = Some b2 ->
      (* the branch refines Δ: r = 0 on the then-branch, r >= 1 on the
         else-branch *)
      sty3_sub {| rt3 := rt3 S; dctx := CLe (CReg r) (CConst 0) :: dctx S |}
               (Θ l1) ->
      sty3_sub {| rt3 := rt3 S; dctx := CLe (CConst 1) (CReg r) :: dctx S |}
               (Θ l2) ->
      term_ty3 P Θ S (TBrZero r l1 l2).

  Inductive instrs_ty3 : sty3 -> list instr -> sty3 -> Prop :=
  | I3Nil : forall S,
      instrs_ty3 S [] S
  | I3Cons : forall S i S' l S'',
      instr_ty3 S i S' ->
      instrs_ty3 S' l S'' ->
      instrs_ty3 S (i :: l) S''.

  Definition block_ty3 (P : prog) (Θ : label -> sty3)
             (S : sty3) (b : block) : Prop :=
    exists S_end,
      instrs_ty3 S (code b) S_end /\ term_ty3 P Θ S_end (termi b).

  Definition program_typed3 (P : prog) (Θ : label -> sty3) : Prop :=
    forall l b, P l = Some b -> block_ty3 P Θ (Θ l) b.

  (* ---------------------------------------------------------------- *)
  (* The concrete tyenv (NO mem_total: memory safety is by typing)     *)
  (* ---------------------------------------------------------------- *)

  Definition point_ok3 (P : prog) (Θ : label -> sty3)
             (p : pc) (S : sty3) : Prop :=
    exists b,
      P (pc_lbl p) = Some b /\
      pc_ix p <= length (code b) /\
      exists S_end,
        instrs_ty3 S (skipn (pc_ix p) (code b)) S_end /\
        term_ty3 P Θ S_end (termi b).

  Definition gamma3 (P : prog) (Θ : label -> sty3) : tyenv :=
    fun p s =>
      exists S, point_ok3 P Θ p S /\ sat3 RS S s.

  (* ---------------------------------------------------------------- *)
  (* Progress                                                          *)
  (* ---------------------------------------------------------------- *)

  Lemma instr_ty3_progress :
    forall S i S' s,
      instr_ty3 S i S' ->
      sat3 RS S s ->
      instr_safe s i.
  Proof.
    intros S i S' s Hty Hsat.
    unfold instr_safe.
    destruct Hty; simpl;
      destruct Hsat as (Hs1 & Hs2 & Hs3 & Hs4).
    - eexists; reflexivity.
    - eexists; reflexivity.
    - eexists; reflexivity.
    - eexists; reflexivity.
    - (* Load: the footprint is inside rg, hence mapped *)
      rewrite (Hs1 base H0).
      destruct (load_bytes_defined (size_bytes sz) (mm s)
                  (tv_val (rf s base) + off)) as [tbs Hl].
      { intros k Hk.
        apply (Hs3 rg); [exact H |].
        replace (tv_val (rf s base) + off + k)
          with (vals_of s base + off + k) by reflexivity.
        eapply footprint_in_sound; eauto. }
      rewrite Hl. eexists; reflexivity.
    - (* Store *)
      rewrite (Hs1 base H0). eexists; reflexivity.
  Qed.

  Lemma term_ty3_progress :
    forall P Θ S t s,
      term_ty3 P Θ S t ->
      (forall r, rt3 S r = false -> tv_taint (rf s r) = false) ->
      term_safe s t.
  Proof.
    intros P Θ S t s Hty H1.
    destruct Hty.
    - left; reflexivity.
    - right; eexists; reflexivity.
    - right. simpl. rewrite (H1 r H).
      destruct (Nat.eqb (tv_val (rf s r)) 0); eexists; reflexivity.
  Qed.

  (* ---------------------------------------------------------------- *)
  (* Preservation of satisfaction by instructions                      *)
  (* ---------------------------------------------------------------- *)

  Lemma instr_ty3_preserves_sat3 :
    forall S i S' s s',
      instr_ty3 S i S' ->
      sat3 RS S s ->
      exec_instr s i = Some s' ->
      sat3 RS S' s'.
  Proof.
    intros S i S' s s' Hty Hsat Hex.
    destruct Hty; simpl in Hex;
      destruct Hsat as (Hs1 & Hs2 & Hs3 & Hs4).
    - (* Nop *)
      injection Hex as <-. split; [| split; [| split]]; simpl; assumption.
    - (* AddHavoc *)
      injection Hex as <-. split; [| split; [| split]]; simpl.
      + intros r Hr. simpl in Hr. unfold regs_set.
        destruct (Nat.eqb r rd) eqn:E.
        * unfold t_or in Hr. apply Bool.orb_false_iff in Hr.
          destruct Hr as [Ha Hb].
          simpl. unfold t_or. rewrite (Hs1 rs1 Ha), (Hs1 rs2 Hb). reflexivity.
        * apply Hs1. exact Hr.
      + eapply havoc_sound; [exact Hs2 |].
        intros r' Hne. unfold vals_of. simpl. unfold regs_set.
        destruct (Nat.eqb r' rd) eqn:E.
        * apply Nat.eqb_eq in E. congruence.
        * reflexivity.
      + exact Hs3.
      + exact Hs4.
    - (* AddExact *)
      injection Hex as <-. split; [| split; [| split]]; simpl.
      + intros r Hr. simpl in Hr. unfold regs_set.
        destruct (Nat.eqb r rd) eqn:E.
        * unfold t_or in Hr. apply Bool.orb_false_iff in Hr.
          destruct Hr as [Ha Hb].
          simpl. unfold t_or. rewrite (Hs1 rs1 Ha), (Hs1 rs2 Hb). reflexivity.
        * apply Hs1. exact Hr.
      + (* the two exact constraints, then the havoc'd rest *)
        assert (Ers1 : Nat.eqb rs1 rd = false)
          by (apply Nat.eqb_neq; congruence).
        assert (Ers2 : Nat.eqb rs2 rd = false)
          by (apply Nat.eqb_neq; congruence).
        constructor; [| constructor].
        * simpl. unfold vals_of. simpl. unfold regs_set.
          rewrite Nat.eqb_refl, Ers1, Ers2. simpl. lia.
        * simpl. unfold vals_of. simpl. unfold regs_set.
          rewrite Nat.eqb_refl, Ers1, Ers2. simpl. lia.
        * eapply havoc_sound; [exact Hs2 |].
          intros r' Hne. unfold vals_of. simpl. unfold regs_set.
          destruct (Nat.eqb r' rd) eqn:E.
          -- apply Nat.eqb_eq in E. congruence.
          -- reflexivity.
      + exact Hs3.
      + exact Hs4.
    - (* MulHavoc *)
      injection Hex as <-. split; [| split; [| split]]; simpl.
      + intros r Hr. simpl in Hr. unfold regs_set.
        destruct (Nat.eqb r rd) eqn:E.
        * unfold t_or in Hr. apply Bool.orb_false_iff in Hr.
          destruct Hr as [Ha Hb].
          simpl. unfold t_or. rewrite (Hs1 rs1 Ha), (Hs1 rs2 Hb). reflexivity.
        * apply Hs1. exact Hr.
      + eapply havoc_sound; [exact Hs2 |].
        intros r' Hne. unfold vals_of. simpl. unfold regs_set.
        destruct (Nat.eqb r' rd) eqn:E.
        * apply Nat.eqb_eq in E. congruence.
        * reflexivity.
      + exact Hs3.
      + exact Hs4.
    - (* Load *)
      destruct (tv_taint (rf s base)) eqn:Etb; [discriminate |].
      destruct (load_bytes (mm s) (tv_val (rf s base) + off) (size_bytes sz))
        as [tbs |] eqn:El; [| discriminate].
      injection Hex as <-. split; [| split; [| split]]; simpl.
      + intros r Hr. simpl in Hr. unfold regs_set.
        destruct (Nat.eqb r rd) eqn:E.
        * (* the loaded value: rg is public here *)
          simpl.
          eapply (load_bytes_untainted_in (r_contains rg)
                    (size_bytes sz) (mm s) (tv_val (rf s base) + off) tbs).
          -- intros x tb Hcx Hmx. eapply Hs4; eauto.
          -- intros k Hk.
             replace (tv_val (rf s base) + off + k)
               with (vals_of s base + off + k) by reflexivity.
             eapply footprint_in_sound; eauto.
          -- exact El.
        * apply Hs1. exact Hr.
      + eapply havoc_sound; [exact Hs2 |].
        intros r' Hne. unfold vals_of. simpl. unfold regs_set.
        destruct (Nat.eqb r' rd) eqn:E.
        * apply Nat.eqb_eq in E. congruence.
        * reflexivity.
      + exact Hs3.
      + exact Hs4.
    - (* Store *)
      destruct (tv_taint (rf s base)) eqn:Etb; [discriminate |].
      injection Hex as <-. split; [| split; [| split]]; simpl.
      + exact Hs1.
      + exact Hs2.
      + (* validity: stores never unmap *)
        intros rg' a' Hin' Hc'.
        apply store_bytes_preserves_defined.
        apply (Hs3 rg' a' Hin' Hc').
      + (* agreement *)
        destruct H2 as [Hpub | Hsec].
        * (* stored value is public: untainted bytes anywhere *)
          rewrite (Hs1 rs Hpub).
          apply store_untainted_agrees3;
            [apply map_mk_tbyte_untainted3 | exact Hs4].
        * (* footprint inside a secret region *)
          eapply store_secret_agrees3 with (rg := rg);
            [exact RS_disjoint | exact H | exact Hsec | | exact Hs4].
          intros k Hk.
          rewrite length_map, unpack_le_length3 in Hk.
          replace (tv_val (rf s base) + off + k)
            with (vals_of s base + off + k) by reflexivity.
          eapply footprint_in_sound; eauto.
  Qed.

  (* ---------------------------------------------------------------- *)
  (* Inversion helpers                                                 *)
  (* ---------------------------------------------------------------- *)

  Lemma term_ty3_jmp_inv :
    forall P Θ S l,
      term_ty3 P Θ S (TJmp l) ->
      exists b, P l = Some b /\ sty3_sub S (Θ l).
  Proof.
    intros P Θ S l H. inversion H; subst. eauto.
  Qed.

  Lemma term_ty3_br_inv :
    forall P Θ S r l1 l2,
      term_ty3 P Θ S (TBrZero r l1 l2) ->
      rt3 S r = false /\
      (exists b1, P l1 = Some b1) /\
      (exists b2, P l2 = Some b2) /\
      sty3_sub {| rt3 := rt3 S; dctx := CLe (CReg r) (CConst 0) :: dctx S |}
               (Θ l1) /\
      sty3_sub {| rt3 := rt3 S; dctx := CLe (CConst 1) (CReg r) :: dctx S |}
               (Θ l2).
  Proof.
    intros P Θ S r l1 l2 H. inversion H; subst. eauto 8.
  Qed.

  (* ---------------------------------------------------------------- *)
  (* From Γ to full well-formedness                                    *)
  (* ---------------------------------------------------------------- *)

  Lemma gamma3_wf_state :
    forall P Θ s,
      program_typed3 P Θ ->
      gamma3 P Θ (pcv s) s ->
      wf_state P (gamma3 P Θ) s.
  Proof.
    intros P Θ s HPT Hg.
    split; [exact Hg |].
    destruct Hg as (S & Hpt & Hsat).
    destruct Hpt as (b & Hb & Hix & S_end & Hchain & Htm).
    destruct (nth_opt (pc_ix (pcv s)) (code b)) as [i |] eqn:E.
    - assert (Hf : fetch P (pcv s) = Some (FInstr i)).
      { unfold fetch. rewrite Hb, E. reflexivity. }
      rewrite Hf.
      rewrite (skipn_nth_some _ _ _ _ E) in Hchain.
      inversion Hchain; subst.
      eapply instr_ty3_progress; eauto.
    - assert (Hlen : pc_ix (pcv s) = length (code b)).
      { apply nth_opt_none_ge in E. lia. }
      assert (Hf : fetch P (pcv s) = Some (FTerm (termi b))).
      { unfold fetch. rewrite Hb, E, Hlen, Nat.eqb_refl. reflexivity. }
      rewrite Hf.
      rewrite Hlen in Hchain. rewrite skipn_all in Hchain.
      inversion Hchain; subst.
      destruct Hsat as (H1 & _).
      eapply term_ty3_progress; eauto.
  Qed.

  (* ---------------------------------------------------------------- *)
  (* Γ is preserved by steps                                           *)
  (* ---------------------------------------------------------------- *)

  Lemma gamma3_preserved :
    forall P Θ s s',
      program_typed3 P Θ ->
      gamma3 P Θ (pcv s) s ->
      step P s s' ->
      gamma3 P Θ (pcv s') s'.
  Proof.
    intros P Θ s s' HPT Hg Hstep.
    destruct Hg as (S & (b & Hb & Hix & S_end & Hchain & Htm) & Hsat).
    inversion Hstep as [s0 i s1 Hf Hex | s0 t s1 Hf Hex]; subst.
    - (* instruction step *)
      pose proof (fetch_inv_instr _ _ _ _ Hb Hf) as Hnth.
      rewrite (skipn_nth_some _ _ _ _ Hnth) in Hchain.
      inversion Hchain as [| S0 i0 S' l0 S''0 Hi Hrest]; subst.
      assert (Hpc : pcv s' = pc_next (pcv s)) by (eapply exec_instr_pc; eauto).
      exists S'. split.
      + exists b. rewrite Hpc. simpl. split; [exact Hb |]. split.
        { apply nth_opt_some_lt in Hnth. lia. }
        exists S_end. split; [exact Hrest | exact Htm].
      + eapply instr_ty3_preserves_sat3; eauto.
    - (* terminator step *)
      destruct (fetch_inv_term _ _ _ _ Hb Hf) as [Ht Hlen].
      rewrite Hlen in Hchain. rewrite skipn_all in Hchain.
      inversion Hchain; subst.
      revert Htm Hex.
      generalize (termi b).
      intros tb Htm Hex.
      destruct tb as [l' | rr l1 l2 |].
      + (* TJmp *)
        apply term_ty3_jmp_inv in Htm.
        destruct Htm as (b' & Hb' & Hsub).
        simpl in Hex. injection Hex as <-.
        exists (Θ l'). split.
        * exists b'. simpl. split; [exact Hb' |]. split; [lia |].
          destruct (HPT l' b' Hb') as (S_end' & Hchain' & Htm').
          exists S_end'. split; [exact Hchain' | exact Htm'].
        * assert (Hsat' : sat3 RS (Θ l') s) by (eapply sat3_sub; eauto).
          destruct Hsat' as (Ha & Hb2 & Hc & Hd).
          split; [| split; [| split]]; simpl; assumption.
      + (* TBrZero *)
        apply term_ty3_br_inv in Htm.
        destruct Htm as (Hrr & (b1 & Hb1) & (b2 & Hb2') & Hsub1 & Hsub2).
        destruct Hsat as (H1 & H2 & H3 & H4).
        simpl in Hex.
        rewrite (H1 rr Hrr) in Hex.
        destruct (Nat.eqb (tv_val (rf s rr)) 0) eqn:Ez;
          injection Hex as <-.
        * (* then-branch: rr = 0 *)
          apply Nat.eqb_eq in Ez.
          assert (Hsat' : sat3 RS (Θ l1) s).
          { eapply sat3_sub; [exact Hsub1 |].
            split; [exact H1 |].
            split; [| split; [exact H3 | exact H4]].
            constructor; [| exact H2].
            simpl. unfold vals_of. lia. }
          exists (Θ l1). split.
          -- exists b1. simpl. split; [exact Hb1 |]. split; [lia |].
             destruct (HPT l1 b1 Hb1) as (S_end' & Hchain' & Htm').
             exists S_end'. split; [exact Hchain' | exact Htm'].
          -- destruct Hsat' as (Ha & Hb3 & Hc & Hd).
             split; [| split; [| split]]; simpl; assumption.
        * (* else-branch: rr >= 1 *)
          apply Nat.eqb_neq in Ez.
          assert (Hsat' : sat3 RS (Θ l2) s).
          { eapply sat3_sub; [exact Hsub2 |].
            split; [exact H1 |].
            split; [| split; [exact H3 | exact H4]].
            constructor; [| exact H2].
            simpl. unfold vals_of. lia. }
          exists (Θ l2). split.
          -- exists b2. simpl. split; [exact Hb2' |]. split; [lia |].
             destruct (HPT l2 b2 Hb2') as (S_end' & Hchain' & Htm').
             exists S_end'. split; [exact Hchain' | exact Htm'].
          -- destruct Hsat' as (Ha & Hb3 & Hc & Hd).
             split; [| split; [| split]]; simpl; assumption.
      + (* THalt *)
        simpl in Hex. discriminate.
  Qed.

  (* ---------------------------------------------------------------- *)
  (* Main results                                                      *)
  (* ---------------------------------------------------------------- *)

  Theorem program_typed3_tyenv_preserves :
    forall P Θ,
      program_typed3 P Θ ->
      tyenv_preserves P (gamma3 P Θ).
  Proof.
    intros P Θ HPT s s' Hwf Hstep.
    destruct Hwf as [Hg _].
    apply gamma3_wf_state; [exact HPT |].
    eapply gamma3_preserved; eauto.
  Qed.

  Theorem typed_type_safety3 :
    forall P Θ s,
      program_typed3 P Θ ->
      wf_state P (gamma3 P Θ) s ->
      (exists s', step P s s' /\ wf_state P (gamma3 P Θ) s') \/ terminal P s.
  Proof.
    intros P Θ s HPT Hwf.
    apply type_safety.
    - apply program_typed3_tyenv_preserves. exact HPT.
    - exact Hwf.
  Qed.

  Theorem typed_start_wf3 :
    forall P Θ s l b,
      program_typed3 P Θ ->
      pcv s = pc_jump l ->
      P l = Some b ->
      sat3 RS (Θ l) s ->
      wf_state P (gamma3 P Θ) s.
  Proof.
    intros P Θ s l b HPT Hpc Hb Hsat.
    apply gamma3_wf_state; [exact HPT |].
    exists (Θ l). split.
    - exists b. rewrite Hpc. simpl. split; [exact Hb |]. split; [lia |].
      destruct (HPT l b Hb) as (S_end & Hchain & Htm).
      exists S_end. split; [exact Hchain | exact Htm].
    - exact Hsat.
  Qed.

End WithEntails.

(* ================================================================== *)
(* A concrete SOUND entailment oracle (a very small "SMT solver"):     *)
(* syntactic membership plus constant comparison.  This demonstrates   *)
(* that the Section interface is inhabitable, and lets us state fully  *)
(* closed end-to-end corollaries.                                      *)
(* ================================================================== *)

Fixpoint cexpr_eqb (e1 e2 : cexpr) : bool :=
  match e1, e2 with
  | CReg r1, CReg r2 => Nat.eqb r1 r2
  | CConst n1, CConst n2 => Nat.eqb n1 n2
  | CAdd a1 b1, CAdd a2 b2 => andb (cexpr_eqb a1 a2) (cexpr_eqb b1 b2)
  | _, _ => false
  end.

Lemma cexpr_eqb_eq : forall e1 e2, cexpr_eqb e1 e2 = true -> e1 = e2.
Proof.
  induction e1 as [r1 | n1 | a1 IHa b1 IHb]; intros [r2 | n2 | a2 b2] H;
    simpl in H; try discriminate.
  - apply Nat.eqb_eq in H. subst; reflexivity.
  - apply Nat.eqb_eq in H. subst; reflexivity.
  - apply Bool.andb_true_iff in H. destruct H as [Ha Hb].
    rewrite (IHa a2 Ha), (IHb b2 Hb). reflexivity.
Qed.

Definition constraint_eqb (c1 c2 : constraint) : bool :=
  match c1, c2 with
  | CLe a1 b1, CLe a2 b2 => andb (cexpr_eqb a1 a2) (cexpr_eqb b1 b2)
  end.

Lemma constraint_eqb_eq :
  forall c1 c2, constraint_eqb c1 c2 = true -> c1 = c2.
Proof.
  intros [a1 b1] [a2 b2] H. simpl in H.
  apply Bool.andb_true_iff in H. destruct H as [Ha Hb].
  rewrite (cexpr_eqb_eq a1 a2 Ha), (cexpr_eqb_eq b1 b2 Hb). reflexivity.
Qed.

Definition entails_syn (D : ctx) (c : constraint) : bool :=
  orb (existsb (constraint_eqb c) D)
      (match c with
       | CLe (CConst n) (CConst m) => Nat.leb n m
       | _ => false
       end).

Lemma entails_syn_sound :
  forall D c,
    entails_syn D c = true ->
    forall V, ctx_sat V D -> csat V c.
Proof.
  intros D c H V Hsat.
  unfold entails_syn in H.
  apply Bool.orb_true_iff in H.
  destruct H as [Hmem | Hconst].
  - apply existsb_exists in Hmem.
    destruct Hmem as (c' & Hin & Heq).
    apply constraint_eqb_eq in Heq. subst c'.
    unfold ctx_sat in Hsat.
    rewrite Forall_forall in Hsat. apply Hsat. exact Hin.
  - destruct c as [e1 e2].
    destruct e1 as [| n |]; try discriminate.
    destruct e2 as [| m |]; try discriminate.
    simpl. apply Nat.leb_le. exact Hconst.
Qed.

(* ------------------------------------------------------------------ *)
(* End-to-end demonstration with the concrete oracle: a memory-safe,   *)
(* taint-precise load from a declared public region [100, 108), whose  *)
(* bounds are discharged by entailment from Δ.  Note there is NO       *)
(* mem_total here: memory is only known to be mapped inside the        *)
(* declared region, and the typed Load is proven to stay inside it.    *)
(* ------------------------------------------------------------------ *)

Definition rg_pub : region := {| rlo := 100; rlen := 8; rtnt := false |}.
Definition RS1 : list region := [rg_pub].

Lemma RS1_disjoint : regions_disjoint RS1.
Proof.
  intros rg1 rg2 a Hin1 Hin2 _ _.
  simpl in Hin1, Hin2.
  destruct Hin1 as [<- | []]; destruct Hin2 as [<- | []]; reflexivity.
Qed.

(* Δ at entry: exactly the two footprint bounds the Load needs. *)
Definition D1 : ctx :=
  [ CLe (CConst 100) (CAdd (CReg 1) (CConst 0));
    CLe (CAdd (CReg 1) (CConst (0 + size_bytes S1))) (CConst (100 + 8)) ].

Definition S3entry : sty3 := {| rt3 := fun _ => false; dctx := D1 |}.
Definition S3top : sty3 := {| rt3 := fun _ => true; dctx := [] |}.

Definition blk3 : block := {| code := [Load S1 0 1 0]; termi := THalt |}.
Definition P3 : prog :=
  fun l => match l with 0 => Some blk3 | _ => None end.
Definition Th3 : label -> sty3 :=
  fun l => match l with 0 => S3entry | _ => S3top end.

Lemma P3_typed : program_typed3 entails_syn RS1 P3 Th3.
Proof.
  intros l b Hb.
  destruct l as [| l]; simpl in Hb; inversion Hb; subst; clear Hb.
  eexists. split.
  - eapply I3Cons; [| apply I3Nil].
    eapply T3Load with (rg := rg_pub).
    + simpl. left. reflexivity.
    + reflexivity.
    + split; reflexivity.
  - apply T3Halt.
Qed.

(* An initial state: r1 = 100, memory mapped (only) on the region. *)
Definition rf3 : regs :=
  fun r => if Nat.eqb r 1 then mk_tval 100 false else mk_tval 0 false.
Definition mm3 : mem :=
  fun a => if andb (Nat.leb 100 a) (Nat.ltb a 108)
           then Some (mk_tbyte 42 false)
           else None.                       (* everything else UNMAPPED *)
Definition s3 : state := {| pcv := pc_jump 0; rf := rf3; mm := mm3 |}.

Lemma s3_wf : wf_state P3 (gamma3 entails_syn RS1 P3 Th3) s3.
Proof.
  eapply typed_start_wf3 with (l := 0) (b := blk3).
  - exact entails_syn_sound.
  - exact P3_typed.
  - reflexivity.
  - reflexivity.
  - split; [| split; [| split]].
    + intros r _. unfold s3, rf3. simpl.
      destruct (Nat.eqb r 1); reflexivity.
    + unfold vals_of, s3, rf3, S3entry, D1. simpl.
      constructor; [simpl; lia |].
      constructor; [simpl; lia |].
      constructor.
    + intros rg a Hin Hc. simpl in Hin.
      destruct Hin as [<- | []].
      unfold r_contains in Hc. simpl in Hc.
      intros K. change (mm3 a = None) in K. unfold mm3 in K.
      rewrite (proj2 (Nat.leb_le 100 a)) in K by lia.
      rewrite (proj2 (Nat.ltb_lt a 108)) in K by lia.
      cbn in K. discriminate K.
    + intros rg a tb Hin Hc Ht Ha. simpl in Hin.
      destruct Hin as [<- | []].
      revert Ha.
      change (mm3 a = Some tb -> tb_taint tb = false).
      unfold mm3.
      destruct (andb (Nat.leb 100 a) (Nat.ltb a 108)).
      * intros Ha. inversion Ha; subst; reflexivity.
      * intros Ha. discriminate Ha.
Qed.

(* The typed program runs: the load executes (memory safety!) and the
   machine reaches the halting terminator. *)
Lemma P3_runs :
  exists s1, step P3 s3 s1 /\ terminal P3 s1.
Proof.
  eexists. split.
  - eapply StepInstr; reflexivity.
  - reflexivity.
Qed.

(* Fully closed end-to-end type safety for the demo program. *)
Corollary P3_safe :
  (exists s', step P3 s3 s' /\ wf_state P3 (gamma3 entails_syn RS1 P3 Th3) s')
  \/ terminal P3 s3.
Proof.
  eapply typed_type_safety3.
  - exact entails_syn_sound.
  - exact RS1_disjoint.
  - exact P3_typed.
  - exact s3_wf.
Qed.
