Require Import List.
Require Import Program.Equality.
From Hammer Require Import Tactics.
From Coq Require Import ssreflect ssrfun ssrbool.

Require Import common.prop_as_core.
Require Import common.prop_as_unscoped.
Require Import fsub.autosubst2_sctx.def_as2.
Require Import fsub.autosubst2_sctx.def_extra.
Require Import fsub.autosubst2_sctx.prop_basic.
Require Import fsub.autosubst2_sctx.prop_subtyping.

Import SubstNotations.
Import UnscopedNotations.

Lemma typing_narrowing Γ1 Γ2 A B C t :
  Γ2 ++ (entry_tvar A) :: Γ1 ⊢ t : C ->
  Γ1 ⊢ B <: A ->
  Γ2 ++ (entry_tvar B) :: Γ1 ⊢ t : C.
Proof.
  intro H. dependent induction H; intros; 
    try hauto ctrs:typing.
  - admit.
  - apply typing_abs.
    + eapply wf_typ_narrowing; eauto.
    + replace (entry_var A0 :: Γ2 ++ (entry_tvar B) :: Γ1) with ((entry_var A0 :: Γ2) ++ (entry_tvar B :: Γ1)) by auto.
      eapply IHtyping; simpl; eauto.
  - apply typing_tabs; eauto.
    + eapply wf_typ_narrowing; eauto.
    + admit.
  - eapply typing_tapp; eauto.
    eapply subtyping_narrowing; eauto. 
  - eapply typing_sub; eauto.
    eapply subtyping_narrowing; eauto. 
Admitted.