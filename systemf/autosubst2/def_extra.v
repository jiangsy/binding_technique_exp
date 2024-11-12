Require Import List.

Require Import common.prop_as_core.
Require Import common.prop_as_unscoped.
Require Import systemf.autosubst2.def_as2.

Definition ctx := list typ.

Definition lookup_fun {T} n (Δ : list T) :=
  nth_error Δ n.

Inductive lookup {T} : nat -> list T -> T -> Prop :=
| here A Γ : lookup 0 (A :: Γ) A
| there n Γ A B : lookup n Γ A -> lookup (S n) (cons B Γ) A.

Import SubstNotations.
Import UnscopedNotations.

Reserved Notation "Γ ⊢ t : A" 
  (at level 50, t at next level, no associativity).
Inductive typing : ctx -> exp -> typ -> Prop :=
| typing_var : forall (Γ : ctx) (i : nat) (A : typ),
  lookup i Γ A ->
  Γ ⊢ (exp_var i) : A
| typing_abs : forall (Γ : ctx) (A B : typ) (t : exp),
  (A :: Γ) ⊢ t : B ->
  Γ ⊢ (exp_abs A t) : (typ_arr A B)
| typing_app : forall (Γ : ctx) (s t : exp) (A B : typ),
  Γ ⊢ s : (typ_arr A B) ->
  Γ ⊢ t : A ->
  Γ ⊢ (exp_app s t) : B
| typing_tabs : forall (Γ : ctx) (t : exp) (A : typ),
  (map (ren_typ ↑) Γ) ⊢ t : A ->
  Γ ⊢ (exp_tabs t) : (typ_all A)
| typing_tapp : forall (Γ : ctx) (t : exp) (A B A' : typ),
  Γ ⊢ t : (typ_all A) ->
  A' = A [B..] ->
  Γ ⊢ exp_tapp t B : A'
where "Γ ⊢ t : A" := (typing Γ t A).