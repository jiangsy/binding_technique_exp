Require Import Coq.Program.Equality.
Require Import Lia.
Require Import Metalib.Metatheory.
From Hammer Require Import Tactics.

From Coq Require Import ssreflect ssrfun ssrbool.

Require Import fsub.lngen.def_ott.
Require Import fsub.lngen.prop_ln.
Require Import common.ltac_ln.
Require Import common.prop_ln.
Require Import fsub.lngen.def_extra.
Require Import fsub.lngen.prop_basic.

Lemma subtyping_refl Γ A :
  Γ ⊢ A ->
  Γ ⊢ A <: A.
Proof.
  intros. induction H; hauto ctrs:subtyping, wf_typ.
Qed.

Lemma subtyping_narrowing' B :
  (forall Γ A C,  
    uniq Γ ->
    Γ ⊢ A <: B ->
    Γ ⊢ B <: C ->
    Γ ⊢ A <: C) ->
  (forall Γ1 Γ2 X A B' C,
    uniq (Γ2 ++ (X , entry_tvar B) :: Γ1) ->
    (Γ2 ++ (X , entry_tvar B) :: Γ1) ⊢ A <: C ->
    Γ1 ⊢ B' <: B ->
    (Γ2 ++ (X , entry_tvar B') :: Γ1) ⊢ A <: C). 
Proof. 
  intros. dependent induction H1; try hauto ctrs:subtyping use:wf_typ_rebinding.
  - destruct (X0 == X).
    + subst. assert (A = B) by (hauto use:binds_exact). subst.
      eapply sub_tvar_bound; eauto.
      eapply H; eauto. hauto use:uniq_rebind. 
      rewrite_env (nil ++ (Γ2 ++ (X ~ entry_tvar B')) ++ Γ1). 
      apply subtyping_weakening; eauto.
    + eapply sub_tvar_bound; eauto.
      eapply binds_rebind_mid; eauto.
  - inst_cofinites_for sub_all; eauto. 
    + intros. inst_cofinites_with X0.
      rewrite_env (((X0, entry_tvar B1) :: Γ2) ++ (X, entry_tvar B') :: Γ1).
      eapply H2; eauto. simpl; auto.
Qed.

Theorem subtyping_transitivity Γ A B C n :
  size_typ B < n -> 
  uniq Γ ->
  Γ ⊢ A <: B ->
  Γ ⊢ B <: C ->
  Γ ⊢ A <: C.
Proof.
  move : Γ A B C.
  induction n; intros; auto. inversion H.
  induction H1; subst; intros; try hauto ctrs:subtyping use:subtyping_wf_typ1, subtyping_wf_typ2.
  - inversion H2; eauto using subtyping.
  - simpl in *. inversion H2; subst.
    * hauto ctrs:subtyping use:subtyping_wf_typ1, subtyping_wf_typ2. 
    * econstructor. eapply IHn; eauto. lia.
      eapply IHn; eauto. lia.
  - simpl in *. inversion H2; subst; eauto.
    + eapply sub_top. inst_cofinites_for wf_typ_all.
      * hauto ctrs:subtyping use:subtyping_wf_typ1, subtyping_wf_typ2. 
      * intros. inst_cofinites_with X.
        rewrite_env (nil ++ ((X, entry_tvar A1) :: Γ)).
        eapply wf_typ_rebinding.
        hauto ctrs:subtyping use:subtyping_wf_typ1, subtyping_wf_typ2.
    + inst_cofinites_for sub_all. 
      * hauto ctrs:subtyping use:subtyping_wf_typ1, subtyping_wf_typ2.
      * eapply IHn; eauto. lia.
      * intros. inst_cofinites_with X.
        eapply IHn; eauto.
        rewrite size_typ_open_typ_wrt_typ_rec_var; lia.
        rewrite_env (nil ++ ((X, entry_tvar B0) :: Γ)).
        eapply subtyping_narrowing'; eauto. intros.
        eapply IHn; eauto. lia.
Qed.

Lemma subtyping_narrowing Γ1 Γ2 X A B B' C :
  uniq (Γ2 ++ (X , entry_tvar B) :: Γ1) ->
  (Γ2 ++ (X , entry_tvar B) :: Γ1) ⊢ A <: C ->
  Γ1 ⊢ B' <: B ->
  (Γ2 ++ (X , entry_tvar B') :: Γ1) ⊢ A <: C.
Proof.
  intros. eapply subtyping_narrowing'; eauto.
  intros. eapply subtyping_transitivity; eauto.
Qed.

Lemma subtyping_subst_tvar Γ1 Γ2 X A B C C':
  (Γ2 ++ (X, entry_tvar C) :: Γ1) ⊢ A <: B ->
  ⊢ (Γ2 ++ (X, entry_tvar C) :: Γ1) ->
  Γ1 ⊢ C' <: C ->
  ((map (subst_typ_in_entry C' X) Γ2) ++ Γ1) ⊢ subst_typ_in_typ C' X A <: subst_typ_in_typ C' X B.
Proof.
  intros. dependent induction H; simpl; destruct_eq_atom; try hauto ctrs:subtyping use:wf_typ_subst_tvar, subtyping_wf_typ.
  - eapply subtyping_refl; eauto.
     hauto ctrs:subtyping use:wf_typ_subst_tvar, subtyping_wf_typ.
  - apply binds_exact in H; auto. inversion H; subst.
    + eapply subtyping_transitivity with (B:=C); eauto.
      * eapply wf_ctx_uniq. eapply wf_ctx_subst_tvar; eauto.
      * rewrite_env (nil ++ (map (subst_typ_in_entry C' X) Γ2) ++ Γ1).
        eapply subtyping_weakening; eauto.
      * erewrite <- subst_typ_in_typ_fresh_eq with (A2:=C).
        eapply IHsubtyping; eauto.
        rewrite wf_typ_tvar_upper; eauto.  
        hauto inv:wf_ctx use:wf_ctx_strengthening.
  - eapply sub_tvar_bound; eauto.
    eapply binds_tvar_subst_tvar; eauto.
  - inst_cofinites_for sub_all; eauto.
    intros. inst_cofinites_with X0.
    setoid_rewrite subst_typ_in_typ_open_typ_wrt_typ in H2; 
    try hauto use:subtyping_wf_typ.
    move : H2 => /(_ _ _ X) => H2.
    simpl in H2. destruct_eq_atom.
    rewrite_env (map (subst_typ_in_entry C' X) ((X0 , entry_tvar B1) :: Γ2) ++ Γ1).
    eapply H2; simpl; eauto.
    constructor; eauto.
Qed.

Lemma wf_typ_subst_var Γ1 Γ2 x A B:
  (Γ2 ++ (x, entry_var B) :: Γ1) ⊢ A ->
  (Γ2 ++ Γ1) ⊢ A.
Proof.
  intros. dependent induction H; eauto using wf_typ.
  - apply binds_remove_mid_diff_bind in H; hauto use:wf_typ.
  - inst_cofinites_for wf_typ_all; eauto. intros. 
    inst_cofinites_with X.
    rewrite_env (((X, entry_tvar A) :: Γ2) ++ Γ1).
    eapply H1; simpl; eauto.
Qed.

Lemma subtyping_subst_var Γ1 Γ2 x A B C:
  (Γ2 ++ (x, entry_var C) :: Γ1) ⊢ A <: B ->
  (Γ2 ++ Γ1) ⊢ A <: B.
Proof.
  intros. dependent induction H; try hauto ctrs:subtyping use:wf_typ_subst_var.
  - eapply sub_tvar_bound with (A:=A); eauto.
    eapply binds_remove_mid_diff_bind in H; hauto.
  - inst_cofinites_for sub_all.
    + hauto use:wf_typ_subst_var.
    + eauto.
    + intros. inst_cofinites_with X. 
      rewrite_env (((X, entry_tvar B1) :: Γ2) ++ Γ1).
      eapply H2. simpl; eauto.
Qed.