Require Import common.prop_as_core.
Require Import common.prop_as_unscoped.
Require Import stlc.autosubst2.def_as2.
Require Import stlc.autosubst2.def_extra.

Require Import Lia.
From Coq Require Import ssreflect ssrfun ssrbool.
From Hammer Require Import Tactics.
Require Import Coq.Program.Equality.
Require Import List.
Require Import Coq.Arith.Bool_nat.


Definition ctx_var_rename {T} ζ Γ Δ :=
  forall i (A : T), lookup i Γ A -> lookup (ζ i) Δ A.

Import SubstNotations.
Import UnscopedNotations.

Hint Constructors lookup typing : core.

Theorem typing_renaming Γ t A: 
  Γ ⊢ t : A ->
  forall Δ ζ,
    ctx_var_rename ζ Γ Δ ->
    Δ ⊢ t ⟨ζ⟩ : A.
Proof.
  intros H. induction H; intros; 
    hauto q:on unfold:ctx_var_rename inv:typing,lookup ctrs:typing,lookup.
Qed.

Fixpoint occurs_free (x : nat) (t : exp) : Prop :=
  match t with 
  | exp_var i => x = i
  | exp_app s1 s2 => occurs_free x s1 \/ occurs_free x s2
  | exp_abs s => occurs_free (S x) s
  | exp_unit => False
  end.

Definition ctx_free_var_rename {T} ζ Γ Δ t :=
  forall i (A : T), occurs_free i t -> lookup i Γ A -> lookup (ζ i) Δ A.

Theorem typing_renaming' Γ t A : 
  Γ ⊢ t : A ->
  forall Δ ζ,
    ctx_free_var_rename ζ Γ Δ t ->
    Δ ⊢ t ⟨ζ⟩ : A.
Proof.
  intros H. induction H; intros; asimpl; eauto.
  - hauto ctrs:typing unfold:ctx_free_var_rename.
  - apply typing_abs. 
    eapply IHtyping; eauto.
    unfold ctx_free_var_rename in *. intros.
    inversion H2; subst; asimpl; eauto.
    econstructor. eauto.
  - hauto ctrs:typing unfold:ctx_free_var_rename. 
Qed.

Fixpoint up_Renexp_k (ξ : nat -> nat) (k : nat) :=
  match k with 
  | 0 => ξ
  | S k' => upRen_exp_exp (up_Renexp_k ξ k')
  end.

Lemma occurs_free_false t i :
  occurs_free i (t ⟨fun x => if (lt_ge_dec x i) then x else (1 + x)⟩) -> False.
Proof.
  move : i. induction t; simpl in *; intros; auto.
  - destruct (lt_ge_dec n i); simpl in H; try lia.
  - eapply IHt with (i := S i); eauto. asimpl in H.
    replace (ren_exp (fun x : nat => if is_left (lt_ge_dec x (S i)) then x else S x) t) with
    (t ⟨0 .: (fun x : nat => if is_left (lt_ge_dec x i) then x else S x) >> S⟩). auto.
    apply extRen_exp. intros. destruct (lt_ge_dec x (S i)); simpl.
    + destruct x; simpl; auto.
      unfold_funcomp. simpl. destruct (lt_ge_dec x i); auto. lia.
    + destruct x; simpl. lia. unfold_funcomp.
      simpl. destruct (lt_ge_dec x i); auto. lia.
  - hauto.
Qed.

Lemma occurs_free_0_shift_false t :
  occurs_free 0 (t ⟨↑⟩) -> False.
Proof.
  apply occurs_free_false.
Qed.

(* 
https://metacoq.github.io/v1.2-8.16/MetaCoq.PCUIC.Bidirectional.BDStrengthening.html#strengthening 
seems to be a reference, but too complicated 
*)
Corollary typing_strengthening_var0 : forall Γ t A B,
  (B :: Γ) ⊢ t ⟨↑⟩ : A ->
  Γ ⊢ t : A.
Proof.
  intros.
  replace t with ((t ⟨↑⟩) ⟨fun x => x - 1⟩).
  eapply typing_renaming'; eauto.
  - unfold ctx_free_var_rename. intros.
    inversion H1; subst; auto.
    + exfalso. eapply occurs_free_0_shift_false; eauto.
    + simpl in *. replace (n - 0) with n by lia. auto.
  - asimpl. replace t with (t ⟨ id ⟩) at 2 by (asimpl; auto).
    apply extRen_exp; eauto. intros. induction x; simpl; auto.
Qed.

Corollary typing_weakening : forall Γ t A B,
  Γ ⊢ t : A ->
  (B :: Γ) ⊢ t ⟨↑⟩ : A.
Proof.
  hauto q:on unfold:ctx_var_rename 
    use:typing_renaming ctrs:typing,lookup.
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
    try hauto q:on unfold!:ctx_var_subst drew:off exh:off inv:typing,lookup ctrs:typing use:typing_weakening limit:200.
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