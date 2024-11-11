Require Import stlc.autosubst2.prop_as_core.
Require Import stlc.autosubst2.prop_as_unscoped.
Require Import stlc.autosubst2.def_as2.
Require Import stlc.autosubst2.def_extra.

Require Import Coq.Program.Equality.
Require Import List.

Definition ctx_var_rename {T} ζ Γ Δ :=
  forall i (A : T), lookup i Γ A -> lookup (ζ i) Δ A.

Import SubstNotations.
Import UnscopedNotations.

Hint Constructors lookup typing : core.

Theorem typing_rename Γ t A : 
  Γ ⊢ t : A ->
  forall Δ ζ,
    ctx_var_rename ζ Γ Δ ->
    Δ ⊢ t ⟨ζ⟩ : A.
Proof.
  intros H. induction H; intros; asimpl; eauto.
  - apply typing_abs. 
    eapply IHtyping; eauto.
    unfold ctx_var_rename in *. intros.
    inversion H1; subst; asimpl; eauto.
    econstructor. eauto.
Qed.

Corollary typing_weaken : forall Γ t A B,
  Γ ⊢ t : A ->
  (B :: Γ) ⊢ t ⟨↑⟩ : A.
Proof.
  intros. 
  eapply typing_rename; eauto.
  - unfold ctx_var_rename. intros. eauto.
Qed.

Definition ctx_var_subst Γ Δ τ := 
  forall x A, lookup x Γ A -> Δ ⊢ τ x : A.

Theorem typing_subst_var Γ t A : 
  Γ ⊢ t : A ->
  forall Δ τ,
    ctx_var_subst Γ Δ τ ->
    Δ ⊢ t [τ] : A.
Proof.
  intro H. induction H; intros; asimpl; eauto.
  - eapply typing_abs.
    eapply IHtyping.
    unfold ctx_var_subst in *. intros.
    inversion H1; subst; asimpl; eauto.
    eapply typing_weaken; eauto.
Qed.

Corollary typing_subst_var0 Γ t s A B: 
  (B :: Γ) ⊢ t : A ->
  Γ ⊢ s : B ->
  Γ ⊢ t [s..] : A.
Proof.
  intros. eapply typing_subst_var; eauto.
  - unfold ctx_var_subst. intros.
    inversion H1; subst; asimpl; eauto.
Qed.

Theorem preservation Γ t t' A : 
  Γ ⊢ t : A ->
  t ⤳ t' ->
  Γ ⊢ t' : A.
Proof.
  intros Htyping Hstep. generalize dependent A.
  induction Hstep; intros; inversion Htyping; subst; eauto.
  - inversion H2. subst. eauto using typing_subst_var0.
Qed.

(* dependent induction will introduce a dependency 
on Eqdep.Eq_rect_eq.eq_rect_eq. Usually such a dependency
should be eliminated. not sure if it's caused by polymorphism of `nil` here *)
Theorem progress' Γ t A : 
  Γ ⊢ t : A ->
  Γ = nil ->
  is_value t \/ exists t', t ⤳ t'.
Proof.
  intros H. induction H; simpl; intros; subst; eauto.
  - inversion H.
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