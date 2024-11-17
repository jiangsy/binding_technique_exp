Require Import common.prop_as_core. 
Require Import common.prop_as_unscoped.
Require Import fsub.autosubst2_sctx.def_as2.
Require Import fsub.autosubst2_sctx.def_extra.

From Coq Require Import ssreflect ssrfun ssrbool.
From Hammer Require Import Tactics.
Require Import Coq.Program.Equality.
Require Import List.

Import SubstNotations.
Import UnscopedNotations.

Definition ctx_tvar_rename_weak Γ Γ' ξ :=
  forall X B, lookup_tvar X Γ B -> exists B', lookup_tvar (ξ X) Γ' B'.

Definition ctx_tvar_rename Γ Γ' ξ :=
  forall X B, lookup_tvar X Γ B -> lookup_tvar (ξ X) Γ' (B ⟨ ξ ⟩).

Definition ctx_tvar_subst_wf Γ Γ' σ :=
  forall X A, lookup_tvar X Γ A -> Γ' ⊢ σ X.

Lemma ctx_tvar_rename_weak_rebounding Γ1 Γ2 A A':
  ctx_tvar_rename_weak (Γ2 ++ (entry_tvar A) :: Γ1)  (Γ2 ++ (entry_tvar A') :: Γ1) id.
Proof.
  intros. induction Γ2; simpl;
    hauto unfold:ctx_tvar_rename_weak inv:lookup_tvar ctrs:lookup_tvar.
Qed.

Lemma wf_typ_renaming_tvar Δ Δ' A ξ:
  Δ ⊢ A ->
  ctx_tvar_rename_weak Δ Δ' ξ ->
  Δ' ⊢ A ⟨ ξ ⟩.
Proof.
  move: Δ Δ' ξ. induction A; try hauto.
  - intros. unfold ctx_tvar_rename_weak in *.
    asimpl. simpl in *. 
    hauto inv:lookup_tvar ctrs:lookup_tvar.
Qed.

Lemma wf_typ_renaming_tvar' Δ Δ' A A' ξ:
  Δ ⊢ A ->
  ctx_tvar_rename_weak Δ Δ' ξ ->
  A' = A ⟨ ξ ⟩ ->
  Δ' ⊢ A'.
Proof.
  intros. subst. eapply wf_typ_renaming_tvar; eauto.
Qed.

Corollary wf_typ_weakening_tvar0 Δ A B:
  Δ ⊢ A ->
  ((entry_tvar B) :: Δ) ⊢ A ⟨↑⟩.
Proof.
  hauto unfold:ctx_tvar_rename_weak inv:lookup_tvar ctrs:lookup_tvar
    use:wf_typ_renaming_tvar.
Qed.

Lemma wf_typ_subst_tvar Δ Δ' A σ:
  Δ ⊢ A ->
  ctx_tvar_subst_wf Δ Δ' σ ->
  Δ' ⊢ A [ σ ].
Proof.
  move: Δ Δ' σ. induction A; intros; 
    try hauto unfold:ctx_tvar_subst_wf.
  - asimpl. simpl in *; split.
    + hauto. 
    + eapply IHA2; hauto unfold:ctx_tvar_subst_wf use:wf_typ_weakening_tvar0 inv:lookup_tvar. 
Qed.

Lemma wf_typ_narrowing : forall Δ1 Δ2 A B C,
  Δ2 ++ (entry_tvar A) :: Δ1 ⊢ C->
  Δ2 ++ (entry_tvar B) :: Δ1 ⊢ C.
Proof.
  intros. eapply wf_typ_renaming_tvar' with (ξ:=id) in H; eauto.
  - eapply ctx_tvar_rename_weak_rebounding; eauto.
  - asimpl; auto.
Qed.