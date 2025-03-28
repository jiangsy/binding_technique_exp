Require Import Coq.Program.Equality.
Require Import Metalib.Metatheory.
From Hammer Require Import Tactics.

Require Import systemf.lngen.def_ott.
Require Import systemf.lngen.prop_ln.
Require Import common.ltac_ln.
Require Import common.prop_ln.
Require Import systemf.lngen.def_extra.

From Coq Require Import ssreflect ssrfun ssrbool.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Lemma typing_lc_typ : forall Γ t A, Γ ⊢ t : A -> lc_typ A.
Proof.
  intros. induction H; try qauto inv:lc_typ ctrs:lc_typ.
  - pick fresh x. inst_cofinites_with x.
    qauto inv:lc_typ ctrs:lc_typ.
  - pick fresh X. inst_cofinites_with X.
    eapply lc_typ_all_exists; eauto.
  - inversion IHtyping; subst. pick fresh X. inst_cofinites_with X.
    erewrite subst_typ_in_typ_intro; eauto.
    eapply subst_typ_in_typ_lc_typ; eauto.
Qed.

Lemma typing_lc_exp : forall Γ t A, Γ ⊢ t : A -> lc_exp t.
Proof.
  intros. induction H; try qauto inv:lc_exp ctrs:lc_exp.
  - pick fresh x. inst_cofinites_with x.
    eapply lc_exp_abs_exists; eauto.
  - pick fresh X. inst_cofinites_with X.
    eapply lc_exp_tabs_exists; eauto.
Qed.

Hint Constructors uniq : core.
Hint Resolve typing_lc_typ typing_lc_exp : core.

Lemma typing_weakening Γ1 Γ2 Γ3 t A :
  (Γ1 ++ Γ3) ⊢ t : A ->
  uniq (Γ1 ++ Γ2 ++ Γ3) ->
  (Γ1 ++ Γ2 ++ Γ3) ⊢ t : A.
Proof.
  intros. dependent induction H; eauto using typing.
  - inst_cofinites_for typing_abs; eauto. intros.
    inst_cofinites_with x.
    rewrite_env (((x, entry_var A) :: Γ1) ++ Γ2 ++ Γ3).
    eapply H1; eauto. simpl; eauto.
  - inst_cofinites_for typing_tabs; eauto. intros.
    inst_cofinites_with X.
    rewrite_env (((X, entry_tvar) :: Γ1) ++ Γ2 ++ Γ3).
    eapply H0; eauto.
    simpl; eauto.
Qed.

Lemma typing_subst_var Γ1 Γ2 x t s A B :
  (Γ2 ++ (x, entry_var B) :: Γ1) ⊢ t : A ->
  uniq (Γ2 ++ (x, entry_var B) :: Γ1) ->
  Γ1 ⊢ s : B ->
  (Γ2 ++ Γ1) ⊢ subst_exp_in_exp s x t : A.
Proof.
  intros. dependent induction H; simpl; eauto using typing.
  - destruct_eq_atom; eauto.
    assert (binds x (entry_var B) (Γ2 ++ (x, entry_var B) :: Γ1)) by auto.
    unify_binds.
    rewrite_env (nil ++ Γ2 ++ Γ1). apply typing_weakening; simpl; eauto.
    eapply uniq_remove_mid with (F:=x~entry_var A); eauto.
    eapply binds_remove_mid in H0; eauto using typing.
  - inst_cofinites_for typing_abs; eauto.
    intros. inst_cofinites_with x0.
    rewrite_env (((x0, entry_var A) :: Γ2) ++ Γ1).
    setoid_rewrite subst_exp_in_exp_open_exp_wrt_exp in H1; eauto.
    move : H1 => /(_ _ _ x) H1. 
    simpl in H1. destruct_eq_atom. 
    eapply H1; simpl; eauto.
  - inst_cofinites_for typing_tabs; eauto.
    intros. inst_cofinites_with X.
    rewrite_env (((X, entry_tvar) :: Γ2) ++ Γ1).
    setoid_rewrite subst_exp_in_exp_open_exp_wrt_typ in H0; eauto.
    move : H0 => /(_ _ _ x) H0. 
    eapply H0; simpl; eauto.
Qed.

Hint Rewrite -> subst_typ_in_typ_open_typ_wrt_typ subst_typ_in_exp_open_exp_wrt_typ : ln.

Lemma typing_subst_tvar Γ1 Γ2 X t A B :
  (Γ2 ++ (X, entry_tvar) :: Γ1) ⊢ t : A ->
  uniq (Γ2 ++ (X, entry_tvar) :: Γ1) ->
  lc_typ B ->
  map (subst_typ_in_entry B X) (Γ2 ++ Γ1) ⊢ subst_typ_in_exp B X t : subst_typ_in_typ B X A.
Proof.
  intros. dependent induction H; simpl; eauto using typing.
  - econstructor; eauto using subst_typ_in_typ_lc_typ.
    replace (entry_var (subst_typ_in_typ B X A)) with (subst_typ_in_entry B X (entry_var A)) by auto.
    eapply binds_map; eauto.
    apply binds_remove_mid in H0; eauto. 
    hauto use:binds_exact.
  - inst_cofinites_for typing_abs.
    hauto use:subst_typ_in_typ_lc_typ.
    intros. inst_cofinites_with x.
    rewrite_env (map (subst_typ_in_entry B X) (((x, entry_var A) :: Γ2) ++ Γ1)).
    setoid_rewrite subst_typ_in_exp_open_exp_wrt_exp in H1; auto.
    simpl in H1. eapply H1; simpl; eauto.
  - inst_cofinites_for typing_tabs. intros. 
    inst_cofinites_with X0.
    rewrite_env (map (subst_typ_in_entry B X) (((X0, entry_tvar) :: Γ2) ++ Γ1)).
    setoid_rewrite subst_typ_in_exp_open_exp_wrt_typ in H0; auto.
    setoid_rewrite subst_typ_in_typ_open_typ_wrt_typ in H0; auto.
    move : H0 => /(_ _ _ X) H0.
    simpl in H0. destruct_eq_atom.
    eapply H0; eauto. sfirstorder.
  - rewrite subst_typ_in_typ_open_typ_wrt_typ; eauto.
    sauto lq: on use: subst_typ_in_typ_lc_typ.
Qed.

Lemma typing_subst_var0 Γ x t s A B :
  x `notin` dom (Γ) ->
  uniq Γ ->
  ((x, entry_var B) :: Γ) ⊢ t : A ->
  Γ ⊢ s : B ->
  Γ ⊢ subst_exp_in_exp s x t : A.
Proof.
  intros. rewrite_env (nil ++ Γ).
  eapply typing_subst_var; eauto. 
Qed.

Lemma map_subst_tvar_in_entry_fresh_eq Γ X B :
  X `notin` tvar_in_entries Γ ->
  map (subst_typ_in_entry B X) Γ = Γ.
Proof.
  intros. induction Γ; simpl; eauto.
  destruct a; destruct e; simpl in *; f_equal; eauto.
  rewrite subst_typ_in_typ_fresh_eq; eauto.
Qed.

Lemma typing_subst_tvar0 Γ X t A B :
  (* this condition is automatically satisfied using De Brujin *)
  uniq Γ -> 
  X `notin` dom (Γ) `union` tvar_in_entries Γ ->
  ((X, entry_tvar) :: Γ) ⊢ t : A ->
  lc_typ B ->
  Γ ⊢ subst_typ_in_exp B X t : subst_typ_in_typ B X A.
Proof.
  intros. replace (Γ) with (map (subst_typ_in_entry B X) (nil ++ Γ)) by
    (apply map_subst_tvar_in_entry_fresh_eq; eauto).
  eapply typing_subst_tvar; eauto.
Qed.

Theorem preservation Γ t t' A : 
  uniq Γ ->
  Γ ⊢ t : A ->
  t ⤳ t' ->
  Γ ⊢ t' : A.
Proof.
  move => Huniq Hty Hstep. move : Γ A Hty Huniq. 
    induction Hstep; intros; try hauto inv:typing ctrs:typing depth:2.
  - ssimpl.
    pick fresh x. inst_cofinites_with x.
    erewrite subst_exp_in_exp_intro; eauto.
    eapply typing_subst_var0; eauto.
  - ssimpl.
    pick fresh X. inst_cofinites_with X.
    erewrite subst_typ_in_typ_intro; eauto.
    erewrite subst_typ_in_exp_intro; eauto.
    eapply typing_subst_tvar0; eauto.
Qed.

Theorem progress t A :
  nil ⊢ t : A ->
  is_value t \/ exists t', t ⤳ t'.
Proof.
  intros. dependent induction H; subst; simpl; try hauto ctrs:typing,step.
  - inversion H; subst; hauto ctrs:typing,step depth:5.
  - inversion H0; subst; hauto ctrs:typing,step.
Qed.