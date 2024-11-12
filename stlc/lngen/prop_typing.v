Require Import Coq.Program.Equality.
Require Import Metalib.Metatheory.

Require Import stlc.lngen.def_ott.
Require Import stlc.lngen.prop_ln.
Require Import common.ltac_common.
Require Import common.ltac_ln.
Require Import stlc.lngen.def_extra.

Hint Constructors typing : core.

Lemma typing_lc Γ t A : 
  Γ ⊢ t : A ->
  lc_exp t.
Proof.
  intros. induction H; eauto.
Qed.

Lemma binds_same {T} Γ1 Γ2 x (A B : T): 
  binds x A (Γ2 ++ (x, B) :: Γ1) ->
  x `notin` dom (Γ2 ++ Γ1) ->
  A = B.
Proof.
  intros. induction Γ2; destruct_binds; eauto.
  - exfalso. eapply binds_dom_contradiction; eauto.
  - destruct a. destruct_binds; eauto.
Qed.

Lemma typing_weaken Γ1 Γ2 Γ3 t A:
  Γ3 ++ Γ1 ⊢ t : A ->
  Γ3 ++ Γ2 ++ Γ1 ⊢ t : A.
Proof.
  intros. dependent induction H; eauto.
  - inst_cofinites_for typing_abs. intros.
    rewrite_env (((x, A) :: Γ3) ++ Γ2 ++ Γ1).
    eapply H0; eauto.
Qed.

Theorem typing_subst Γ1 Γ2 x s t A B:
  x `notin` dom (Γ2 ++ Γ1) ->
  Γ2 ++ (x, B) :: Γ1 ⊢ t : A ->
  Γ1 ⊢ s : B ->
  Γ2 ++ Γ1 ⊢ (subst_exp_in_exp s x t) : A.
Proof.
  intros. dependent induction H0; eauto.
  - simpl. destruct_eq_atom. eauto.
    + eapply binds_same in H0; subst; eauto.
      rewrite_env (nil ++ Γ2 ++ Γ1). eapply typing_weaken; eauto.
    + apply binds_remove_mid in H0; eauto. 
  - simpl. inst_cofinites_for typing_abs. intros.
    inst_cofinites_with x0.
    rewrite_env (((x0, A) :: Γ2) ++ Γ1). 
    replace (exp_var_f x0) with (subst_exp_in_exp s x (exp_var_f x0)); eauto.
    rewrite <- subst_exp_in_exp_open_exp_wrt_exp.
    eapply H0; simpl; eauto.
    + eapply typing_lc; eauto.
    + simpl. destruct_eq_atom; eauto.
  - simpl. eapply typing_app; eauto.
Qed.

Corollary typing_subst0 Γ x s t A B: 
  x `notin` dom Γ ->
  ((x, B) :: Γ) ⊢ t : A ->
  Γ ⊢ s : B ->
  Γ ⊢ (subst_exp_in_exp s x t) : A.
Proof.
  intros. rewrite <- (app_nil_l Γ). eapply typing_subst; eauto.
Qed.

Theorem preservation Γ t t' A : 
  Γ ⊢ t : A ->
  t ⤳ t' ->
  Γ ⊢ t' : A.
Proof.
  intros Htyping Hstep. generalize dependent A.
  induction Hstep; intros; inversion Htyping; subst; eauto.
  - inversion H2. subst.
    pick fresh x. inst_cofinites_with x.
    apply typing_subst0 with (s:=s) in H3; eauto.
    rewrite subst_exp_in_exp_open_exp_wrt_exp in H3; eauto.
    simpl in H3. destruct_eq_atom. eauto.
    rewrite subst_exp_in_exp_fresh_eq in H3; eauto.
    eapply typing_lc; eauto.
Qed.

Theorem progress' Γ t A : 
  Γ ⊢ t : A ->
  Γ = nil ->
  is_value t \/ exists t', t ⤳ t'.
Proof.
  intros H. induction H; simpl; intros; subst; eauto.
  - right. inversion H; subst.
    + inversion H1. 
    + eauto using step. 
    + specialize (IHtyping1 (eq_refl _)).
      destruct IHtyping1; eauto.
      * inversion H3.
      * destruct H3 as [t']. eauto using step.
Qed.

Theorem progress t A : 
  nil ⊢ t : A ->
  is_value t \/ exists t', t ⤳ t'.
Proof.
  intros H. eapply progress'; eauto.
Qed.