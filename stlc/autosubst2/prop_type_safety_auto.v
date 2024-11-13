Require Import common.prop_as_core.
Require Import common.prop_as_unscoped.
Require Import stlc.autosubst2.def_as2.
Require Import stlc.autosubst2.def_extra.

From Coq Require Import ssreflect ssrfun ssrbool.
From Hammer Require Import Tactics.
Require Import Coq.Program.Equality.
Require Import List.

Definition ctx_var_rename {T} ζ Γ Δ :=
  forall i (A : T), lookup i Γ A -> lookup (ζ i) Δ A.

Import SubstNotations.
Import UnscopedNotations.

Hint Constructors lookup typing : core.

Theorem typing_rename Γ t A: 
  Γ ⊢ t : A ->
  forall Δ ζ,
    ctx_var_rename ζ Γ Δ ->
    Δ ⊢ t ⟨ζ⟩ : A.
Proof.
  intros H. induction H; intros; 
    hauto q:on unfold:ctx_var_rename inv:typing,lookup ctrs:typing,lookup.
Qed.

Corollary typing_weaken : forall Γ t A B,
  Γ ⊢ t : A ->
  (B :: Γ) ⊢ t ⟨↑⟩ : A.
Proof.
  hauto q:on unfold:ctx_var_rename 
    use:typing_rename ctrs:typing,lookup.
Qed.

Definition ctx_var_subst Γ Δ τ := 
  forall x A, lookup x Γ A -> Δ ⊢ τ x : A.

Theorem typing_subst_var Γ t A : 
  Γ ⊢ t : A ->
  forall Δ τ,
    ctx_var_subst Γ Δ τ ->
    Δ ⊢ t [τ] : A.
Proof.
  intro H. induction H; 
    try hauto q:on unfold!:ctx_var_subst drew:off exh:off inv:typing,lookup ctrs:typing use:typing_weaken limit:200.
Qed.

Corollary typing_subst_var0 Γ t s A B: 
  (B :: Γ) ⊢ t : A ->
  Γ ⊢ s : B ->
  Γ ⊢ t [s..] : A.
Proof.
  intros.
  hauto q:on inv:typing,lookup ctrs:typing,lookup unfold:ctx_var_subst use:typing_subst_var.
Qed.

Theorem preservation Γ t t' A : 
  Γ ⊢ t : A ->
  t ⤳ t' ->
  Γ ⊢ t' : A.
Proof.
  intros Htyping Hstep. generalize dependent A.
  induction Hstep; hauto use:typing_subst_var0 ctrs:typing inv:typing.
Qed.

Theorem progress' Γ t A : 
  Γ ⊢ t : A ->
  Γ = nil ->
  is_value t \/ exists t', t ⤳ t'.
Proof.
  intros H. induction H; hauto inv:lookup,typing ctrs:step.
Qed.

Theorem progress t A : 
  nil ⊢ t : A ->
  is_value t \/ exists t', t ⤳ t'.
Proof.
  intros H. eapply progress'; eauto.
Qed.