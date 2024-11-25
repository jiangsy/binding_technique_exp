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
    + admit.
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
      eapply subtyping_subst with (C:=B); eauto.
Admitted.

Theorem preservation Γ t t' A : 
  uniq Γ ->
  Γ ⊢ t : A ->
  t ⤳ t' ->
  Γ ⊢ t' : A.
Proof.
  move => Huniq Hty Hstep. move : Γ A Hty Huniq. 
    induction Hstep; intros; try hauto inv:typing ctrs:typing depth:2.
  - ssimpl. admit.
  - ssimpl.
    pick fresh X. inst_cofinites_with X. admit.
Admitted.

Theorem progress t A :
  nil ⊢ t : A ->
  is_value t \/ exists t', t ⤳ t'.
Proof.
Admitted.