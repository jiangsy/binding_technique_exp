Require Import stlc.autosubst2.prop_as_core.
Require Import stlc.autosubst2.prop_as_unscoped.
Require Import stlc.autosubst2.def_as2.

Require Import List.
Import SubstNotations.
Import UnscopedNotations.

(* https://github.com/yiyunliu/autosubst-stlc/blob/master/typing.v *)

Definition ctx := list typ.

Inductive lookup {T} : nat -> list T -> T -> Prop :=
| here A Γ : lookup 0 (A :: Γ) A
| there n Γ A B : lookup n Γ A -> lookup (S n) (cons B Γ) A.

Reserved Notation "Γ ⊢ t : A" 
  (at level 99, t at next level, no associativity).
Inductive typing : ctx -> exp -> typ -> Prop :=
| typing_unit : forall (Γ : ctx),
  Γ ⊢ exp_unit : typ_unit
| typing_var : forall (Γ : ctx) (i : nat) (A : typ),
  lookup i Γ A ->
  Γ ⊢ (exp_var i) : A
| typing_abs : forall (Γ : ctx) (A B : typ) (t : exp),
  (A :: Γ) ⊢ t : B ->
  Γ ⊢ (exp_abs t) : (typ_arr A B)
| typing_app : forall (Γ : ctx) (s t : exp) (A B : typ),
  Γ ⊢ s : (typ_arr A B) ->
  Γ ⊢ t : A ->
  Γ ⊢ (exp_app s t) : B
where "Γ ⊢ t : A" := (typing Γ t A).

Reserved Notation "t ⤳ t'" (at level 80).
Inductive step : exp -> exp -> Prop :=
| step_beta : forall (t s : exp),
  exp_app (exp_abs t) s ⤳ t [s..]
| step_app : forall (t t' s : exp),
  t ⤳ t' ->
  exp_app t s ⤳ exp_app t' s
where "t ⤳ t'" := (step t t').

Definition is_value (t : exp) : Prop :=
  match t with
  | exp_abs _ => True
  | exp_unit => True
  | _ => False
  end.