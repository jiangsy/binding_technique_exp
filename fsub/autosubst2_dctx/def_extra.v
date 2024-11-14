Require Import List.

Require Import common.prop_as_core.
Require Import common.prop_as_unscoped.
Require Import fsub.autosubst2_dctx.def_as2.

Import SubstNotations.
Import UnscopedNotations.

Definition ctx := list typ.

Inductive lookup {T} : nat -> list T -> T -> Prop :=
| here A Γ : lookup 0 (A :: Γ) A
| there n Γ A B : lookup n Γ A -> lookup (S n) (cons B Γ) A.

Fixpoint wf_typ Δ A := match A with
  | typ_var X => exists B, lookup X Δ B
  | typ_top => True
  | typ_arr A B => wf_typ Δ A /\ wf_typ Δ B
  | typ_all A B => wf_typ Δ A /\ wf_typ (A :: Δ) B
end.

Notation "Δ ⊢ A" := (wf_typ Δ A) (at level 99).

Reserved Notation "Δ ⊢ A <: B" 
  (at level 99, A at next level, no associativity).
Inductive subtyping : ctx -> typ -> typ -> Prop :=
| sub_top Δ A :
  Δ ⊢ A ->
  Δ ⊢ A <: typ_top
| sub_tvar_refl Δ X :
  Δ ⊢ typ_var X ->
  Δ ⊢ typ_var X <: typ_var X
| sub_tvar_bound Δ X A B: 
  lookup X Δ A ->
  Δ ⊢ A <: B ->
  Δ ⊢ typ_var X <: B
| sub_arrow Δ A1 A2 B1 B2 : 
  Δ ⊢ B1 <: A1 ->
  Δ ⊢ A2 <: B2 ->
  Δ ⊢ (typ_arr A1 A2) <: (typ_arr B1 B2)
| sub_all Δ A1 A2 B1 B2 : 
  Δ ⊢ B1 ->
  Δ ⊢ B1 <: A1 ->
  (B1 :: Δ) ⊢ A2 <: B2 ->
  Δ ⊢ (typ_all A1 A2) <: (typ_all B1 B2)
where "Δ ⊢ A <: B" := (subtyping Δ A B).

Reserved Notation "Δ ;; Γ ⊢ t : A" 
  (at level 99, Γ at next level, t at next level, no associativity).
Inductive typing : ctx -> ctx -> exp -> typ -> Prop :=
| typing_var Δ Γ i A :
  lookup i Γ A ->
  Δ ;; Γ ⊢ (exp_var i) : A
| typing_abs Δ Γ t A B :
  Δ ⊢ A ->
  Δ ;; (A :: Γ) ⊢ t : B ->
  Δ ;; Γ ⊢ (exp_abs A t) : (typ_arr A B)
| typing_app Δ Γ s t A B :
  Δ ;; Γ ⊢ t : (typ_arr A B) ->
  Δ ;; Γ ⊢ s : A ->
  Δ ;; Γ ⊢ (exp_app t s) : B
| typing_tabs : forall Δ Γ t A B,
  Δ ⊢ A ->
  (A :: Δ) ;; (map (ren_typ ↑) Γ) ⊢ t : B ->
  Δ ;; Γ ⊢ (exp_tabs A t) : (typ_all A B)
| typing_tapp : forall Δ Γ t A B A' B',
  Δ ;; Γ ⊢ t : (typ_all A B) ->
  Δ ⊢ A' <: A ->
  B' = B [A'..] ->
  Δ ;; Γ ⊢ exp_tapp t A' : B'
| typing_sub : forall Δ Γ t A B,
  Δ ;; Γ ⊢ t : A ->
  Δ ⊢ A <: B ->
  Δ ;; Γ ⊢ t : B
where "Δ ;; Γ ⊢ t : A" := (typing Δ Γ t A).

Definition is_value (t : exp) : Prop :=
  match t with
  | exp_abs _ _ => True
  | exp_tabs _ _ => True
  | _ => False
  end.

Reserved Notation "t ⤳ t'" (at level 80).
Inductive step : exp -> exp -> Prop :=
| step_beta t s A :
  is_value s ->
  exp_app (exp_abs A t) s ⤳ t [typ_var ; scons s exp_var] 
| step_inst t A B :
  exp_tapp (exp_tabs A t) B ⤳ t [scons B typ_var; exp_var]
| step_appl t t' s : 
  t ⤳ t' -> 
  exp_app t s ⤳ exp_app t' s
| step_appr t s s' : 
  is_value t ->
  s ⤳ s' -> 
  exp_app t s ⤳ exp_app t s'
| step_tapp t t' A : 
  t ⤳ t' ->
  exp_tapp t A ⤳ exp_tapp t' A
where "t ⤳ t'" := (step t t').