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
Require Import fsub.lngen.prop_subtyping.

Lemma typing_subst_tvar Γ1 Γ2 X t A B C :
  (Γ2 ++ (X, entry_tvar B) :: Γ1) ⊢ t : A ->
  ⊢ (Γ2 ++ (X, entry_tvar B) :: Γ1) ->
  Γ1 ⊢ C <: B ->
  ((map (subst_typ_in_entry C X) Γ2) ++ Γ1) ⊢ subst_typ_in_exp C X t : subst_typ_in_typ C X A.
Proof.
  intros. dependent induction H; simpl; eauto using typing.
  - econstructor.
    + hauto use:subst_typ_in_typ_lc_typ, subtyping_wf_typ, wf_typ_lc_typ.
    + eapply binds_var_subst_tvar; eauto.
      unfold not. intros. subst.
      assert (binds X (entry_tvar B) (Γ2 ++ (X, entry_tvar B) :: Γ1)); eauto.
      unify_binds.
  - inst_cofinites_for typing_abs. 
    + eapply wf_typ_subst_tvar; eauto.
    + intros. inst_cofinites_with x.
      rewrite_env ((map (subst_typ_in_entry C X) ((x, entry_var A) :: Γ2)) ++ Γ1).
      setoid_rewrite subst_typ_in_exp_open_exp_wrt_exp in H1; try hauto use:subtyping_wf_typ.
      move : H1 => /(_ _ _ X) H1. simpl in H1. destruct_eq_atom.
      eapply H1; simpl; eauto.
      eapply wf_cons_var; eauto.
  - inst_cofinites_for typing_tabs.
    + eapply wf_typ_subst_tvar; eauto.
    + intros. inst_cofinites_with X0.
      rewrite_env (map (subst_typ_in_entry C X) ((X0, entry_tvar A) :: Γ2) ++ Γ1).
      setoid_rewrite subst_typ_in_typ_open_typ_wrt_typ in H1; try hauto use:subtyping_wf_typ.
      setoid_rewrite subst_typ_in_exp_open_exp_wrt_typ in H1; try hauto use:subtyping_wf_typ.
      move : H1 => /(_ _ _ X) H1.
      simpl in H1. destruct_eq_atom. eapply H1; simpl; eauto.
      eapply wf_cons_tvar; eauto.
  - rewrite subst_typ_in_typ_open_typ_wrt_typ.
    + hauto use:subtyping_wf_typ.
    + eapply typing_tapp; eauto. fold subst_typ_in_typ.
      eapply subtyping_subst_tvar with (C:=B); eauto.
Qed.

Lemma typing_subst_var Γ1 Γ2 x t s A B :
  (Γ2 ++ (x, entry_var B) :: Γ1) ⊢ t : A ->
  ⊢ (Γ2 ++ (x, entry_var B) :: Γ1) ->
  Γ1 ⊢ s : B ->
  (Γ2 ++ Γ1) ⊢ subst_exp_in_exp s x t : A.
Proof.
  intros. dependent induction H; simpl; try hauto use:typing.
  - destruct_eq_atom; eauto.
    + apply binds_exact in H0; eauto.
      inversion H0; subst.
      rewrite_env (nil ++ Γ2 ++ Γ1). 
      apply typing_weakening. simpl; eauto.
    + apply binds_remove_mid in H0; eauto using typing. 
  - inst_cofinites_for typing_abs.
    + hauto use:wf_typ_subst_var.
    + intros. inst_cofinites_with x0.
      setoid_rewrite subst_exp_in_exp_open_exp_wrt_exp in H1; eauto.
      move : H1 => /(_ _ _ x) => H1; eauto.
      simpl in H1. destruct_eq_atom. 
      rewrite_env (((x0, entry_var A) :: Γ2) ++ Γ1). eapply H1; simpl; eauto.
      constructor; eauto. 
  - inst_cofinites_for typing_tabs.
    + hauto use:wf_typ_subst_var.
    + intros. inst_cofinites_with X.
      setoid_rewrite subst_exp_in_exp_open_exp_wrt_typ in H1; eauto.
      rewrite_env (((X, entry_tvar A) :: Γ2) ++ Γ1). eapply H1; simpl; 
      eauto using wf_ctx.
  - eapply typing_tapp; eauto.
    eapply subtyping_subst_var; eauto. 
Qed.

Corollary typing_subst_tvar0 Γ X t A B C :
  ((X, entry_tvar B) :: Γ) ⊢ t : A ->
  ⊢ ((X, entry_tvar B) :: Γ) ->
  Γ ⊢ C <: B ->
  Γ ⊢ subst_typ_in_exp C X t : subst_typ_in_typ C X A.
Proof.
  intros. rewrite_env ((map (subst_typ_in_entry C X) nil) ++ Γ).
  eapply typing_subst_tvar; eauto.
Qed.

Corollary typing_subst_var0 Γ x t s A B :
  ((x, entry_var B) :: Γ) ⊢ t : A ->
  ⊢ ((x, entry_var B) :: Γ) ->
  Γ ⊢ s : B ->
  Γ ⊢ subst_exp_in_exp s x t : A.
Proof.
  intros. rewrite_env (nil ++ Γ).
  eapply typing_subst_var; eauto.
Qed.

Theorem preservation Γ t t' A : 
  ⊢ Γ ->
  Γ ⊢ t : A ->
  t ⤳ t' ->
  Γ ⊢ t' : A.
Proof.
  move => Huniq Hty Hstep. move : Γ A Hty Huniq. 
    induction Hstep; intros; try hauto inv:typing ctrs:typing depth:2.
  - ssimpl.
    pick fresh x. inst_cofinites_with x.
    erewrite subst_exp_in_exp_intro; eauto.
    eapply typing_subst_var0; eauto using wf_ctx.
  - ssimpl.
    pick fresh X. inst_cofinites_with X.
    erewrite subst_typ_in_exp_intro; eauto.
    erewrite subst_typ_in_typ_intro; eauto.
    eapply typing_subst_tvar0; eauto using wf_ctx.
Qed.

Lemma value_arr_inv t A B :
  nil ⊢ t : typ_arr A B ->
  is_value t ->
  exists A' t', t = exp_abs A' t'.
Proof.
  intros. dependent induction H; simpl;
    try hauto.
  - inversion H0; subst; eauto.
Qed.

Lemma value_all_inv t A B :
  nil ⊢ t : typ_all A B ->
  is_value t ->
  exists A' t', t = exp_tabs A' t'.
Proof.
  intros. dependent induction H; simpl;
    try hauto.
  - inversion H0; subst; eauto.
Qed.
  
Theorem progress t A :
  nil ⊢ t : A ->
  is_value t \/ exists t', t ⤳ t'.
Proof.
  intros. dependent induction H; subst; try hauto ctrs:typing.
  - ssimpl; try hauto ctrs:typing, step.
    hauto use:value_arr_inv ctrs:step.
  - ssimpl; try hauto ctrs:typing, step.
    hauto use:value_all_inv ctrs:step.
Qed.