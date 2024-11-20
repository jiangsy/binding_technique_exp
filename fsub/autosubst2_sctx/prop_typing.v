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

Lemma lookup_var_narrowing Γ1 Γ2 A A' B x :
  lookup_var x (Γ2 ++ entry_tvar A :: Γ1) B ->
  lookup_var x (Γ2 ++ entry_tvar A' :: Γ1) B.
Proof.
  intros. dependent induction H; 
    destruct Γ2; hauto ctrs:lookup_var.
Qed.

Lemma typing_narrowing Γ1 Γ2 A B C t :
  Γ2 ++ (entry_tvar A) :: Γ1 ⊢ t : C ->
  Γ1 ⊢ B <: A ->
  Γ2 ++ (entry_tvar B) :: Γ1 ⊢ t : C.
Proof.
  intro H. dependent induction H; intros; 
    try hauto ctrs:typing.
  - hauto ctrs:typing use:lookup_var_narrowing.
  - apply typing_abs.
    + eapply wf_typ_narrowing; eauto.
    + replace (entry_var A0 :: Γ2 ++ (entry_tvar B) :: Γ1) with ((entry_var A0 :: Γ2) ++ (entry_tvar B :: Γ1)) by auto.
      eapply IHtyping; simpl; eauto.
  - apply typing_tabs; eauto.
    + eapply wf_typ_narrowing; eauto.
    + replace (entry_tvar A0 :: Γ2 ++ entry_tvar B :: Γ1) with 
        ((entry_tvar A0 :: Γ2) ++ entry_tvar B :: Γ1) by (simpl; eauto).
      eapply IHtyping with (A:=A); simpl; eauto.
  - eapply typing_tapp; eauto.
    eapply subtyping_narrowing; eauto. 
  - eapply typing_sub; eauto.
    eapply subtyping_narrowing; eauto. 
Qed.

Definition ctx_var_subst Γ Γ' σ τ :=
  forall x A, lookup_var x Γ A -> (Γ' ⊢ τ x : A [σ]).

Lemma typing_subst Γ Γ' A t σ τ :
  Γ ⊢ t : A ->
  ctx_tvar_subst Γ Γ' σ ->
  ctx_var_subst Γ Γ' σ τ -> 
  Γ' ⊢ t [σ;τ] : A [σ] .
Proof.
  move => Hty. move : Γ' σ τ.
  induction Hty; intros; asimpl; try hauto ctrs:typing.
  - eapply typing_abs; eauto. 
    + eapply wf_typ_subst_tvar; eauto.
      hauto unfold:ctx_tvar_subst_wf,ctx_tvar_subst use:sub_wf_typ1,sub_wf_typ2.
    + eapply IHHty; eauto.
      * unfold ctx_var_subst in *. intros.
        unfold ctx_tvar_subst. intros. 
        inversion H2; subst; asimpl; eauto. 
        eapply sub_renaming_var0; eauto.
      * unfold ctx_var_subst. intros.
        inversion H2; subst; asimpl; try hauto ctrs:typing, lookup_var.
        eapply typing_weakening_var0; eauto.
  - eapply typing_tabs; eauto.
    + eapply wf_typ_subst_tvar; eauto.
      hauto unfold:ctx_tvar_subst_wf,ctx_tvar_subst use:sub_wf_typ1,sub_wf_typ2.
    + eapply IHHty; eauto. 
      * unfold ctx_tvar_subst in *. intros. 
        inversion H2; subst; asimpl; eauto.
        eapply sub_tvar_bound; eauto using lookup_tvar.
        replace (subst_typ (σ >> ren_typ ↑) A) with (A [σ] ⟨ ↑ ⟩) by (asimpl; auto).
        eapply sub_weakening_tvar0. eapply subtyping_reflexivity.
        eapply wf_typ_subst_tvar; eauto.
        hauto unfold:ctx_tvar_subst_wf,ctx_tvar_subst use:sub_wf_typ1,sub_wf_typ2.
        replace (subst_typ (σ >> ren_typ ↑) A1) with (A1 [σ] ⟨ ↑ ⟩) by (asimpl; auto).
        eapply sub_weakening_tvar0. eauto.
      * unfold ctx_var_subst in *. intros.
        inversion H2; subst; asimpl; eauto.
        replace (subst_typ (σ >> ren_typ ↑) A1) with (A1 [σ] ⟨ ↑ ⟩) by (asimpl; auto).
        eapply typing_weakening_tvar0; eauto.
  - asimpl. subst.
    eapply typing_tapp with (A:=A [σ]) (B:=B [up_typ_typ σ]); asimpl; eauto. 
    eapply subtyping_subst; eauto.
  - eapply typing_sub with (A:=A [σ]); eauto.
    eapply subtyping_subst; eauto.
Qed.