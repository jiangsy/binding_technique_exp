Require Import List.

Require Import binder.autosubst2.def.
Require Import binder.autosubst2.prop_as_core.
Require Import binder.autosubst2.prop_as_unscoped.


Definition ctx := list ty.

Definition lookup_fun {T} n (Δ : list T) :=
  nth_error Δ n.

Inductive lookup {T} : nat -> list T -> T -> Prop :=
| here A Γ : lookup 0 (A :: Γ) A
| there n Γ A B : lookup n Γ A -> lookup (S n) (cons B Γ) A.

Hint Constructors lookup : core.

Lemma lookup_iff {T} n (Γ : list T) A : lookup n Γ A -> lookup_fun n Γ = Some A.
Proof.
  intros. induction H; eauto.
Qed.

Lemma lookup_det {U} n (Γ : list U) A B : lookup n Γ A -> lookup n Γ B -> A = B.
Proof.
  intros. induction H; inversion H0; eauto.
Qed.

Derive Inversion lookup_inv 
  with (forall {U} i (Γ : list U) A, lookup i Γ A) Sort Prop.

Import SubstNotations.
Import UnscopedNotations.

Reserved Notation "Γ ⊢ t : A" 
  (at level 50, t at next level, no associativity).
Inductive typing : ctx -> tm -> ty -> Prop :=
| typing_var : forall (Γ : ctx) (i : nat) (A : ty),
  lookup i Γ A ->
  Γ ⊢ (var_tm i) : A
| typing_lam : forall (Γ : ctx) (A B : ty) (t : tm),
  (A :: Γ) ⊢ t : B ->
  Γ ⊢ (lam A t) : (arr A B)
| typing_app : forall (Γ : ctx) (s t : tm) (A B : ty),
  Γ ⊢ s : (arr A B) ->
  Γ ⊢ t : A ->
  Γ ⊢ (app s t) : B
| typing_tlam : forall (Γ : ctx) (t : tm) (A : ty),
  (map (ren_ty shift) Γ) ⊢ t : A ->
  Γ ⊢ (tlam t) : (all A)
| typing_tapp : forall (Γ : ctx) (t : tm) (A B A' : ty),
  Γ ⊢ t : (all A) ->
  A' = A [B..] ->
  Γ ⊢ tapp t B : A'
where "Γ ⊢ t : A" := (typing Γ t A).

Definition ctx_var_rename {T} ζ Γ Δ :=
  forall i (A : T), lookup i Γ A -> lookup (ζ i) Δ A.

Lemma lookup_map {T} : forall (A : T) (f : T -> T) (Γ : list T) x ,
  lookup x Γ A -> lookup x (map f Γ) (f A).
Proof.
  intros. induction H; simpl; eauto.
Qed.

Lemma typing_rename Γ t A : 
  Γ ⊢ t : A ->
  forall Δ ξ ζ,
    ctx_var_rename ζ Γ Δ ->
    (map (ren_ty ξ) Δ) ⊢ t ⟨ξ;ζ⟩ : A ⟨ξ⟩.
Proof.
  intros H. induction H; intros; asimpl.
  - eapply typing_var.
    eapply lookup_map; eauto.
  - eapply typing_lam. admit.
  - eapply typing_app; eauto. 
  - eapply typing_tlam; asimpl; eauto.
    admit. 
  - eapply typing_tapp with (A:=A ⟨up_ren ξ⟩).
    + fsimpl. eauto.
    + admit.
Admitted.