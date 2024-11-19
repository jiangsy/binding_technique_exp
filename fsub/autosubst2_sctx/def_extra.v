Require Import List.

Require Import common.prop_as_core.
Require Import common.prop_as_unscoped.
Require Import fsub.autosubst2_sctx.def_as2.

Import SubstNotations.
Import UnscopedNotations.

Definition ctx := list entry.

Definition ren_var_entry (ξ : nat -> nat) (e : entry) : entry :=
  match e with
  | entry_var A => entry_var (A ⟨ ξ ⟩)
  | entry_tvar A => entry_tvar (A)
  end.

(* Definition subst_entry (σ : nat -> typ) (e : entry) : entry :=
  match e with
  | entry_var A => entry_var (A [σ])
  | entry_tvar A => entry_tvar (A [σ])
  end. *)

Inductive lookup_tvar : nat -> list entry -> typ -> Prop :=
| here_tvar A Γ : lookup_tvar 0 ((entry_tvar A) :: Γ) (A ⟨ ↑ ⟩) 
| skip_var n Γ A B : lookup_tvar n Γ A -> lookup_tvar n (cons (entry_var B) Γ) A
| there_tvar n Γ A B : lookup_tvar n Γ A -> lookup_tvar (S n) (cons (entry_tvar B) Γ) (A ⟨ ↑ ⟩).

Inductive lookup_var : nat -> list entry -> typ -> Prop :=
| here_var A Γ : lookup_var 0 ((entry_var A) :: Γ) A 
| skip_tvar n Γ A B : lookup_var n Γ A -> lookup_var n (cons (entry_tvar B) Γ) (A ⟨ ↑ ⟩)
| there_var n Γ A B : lookup_var n Γ A -> lookup_var (S n) (cons (entry_var B) Γ) A.

Fixpoint wf_typ Γ A := match A with
  | typ_var X => exists B, lookup_tvar X Γ B
  | typ_top => True
  | typ_arr A B => wf_typ Γ A /\ wf_typ Γ B
  | typ_all A B => wf_typ Γ A /\ wf_typ ((entry_tvar A) :: Γ) B
end.

Notation "Γ ⊢ A" := (wf_typ Γ A) (at level 99).

Reserved Notation "Γ ⊢ A <: B" 
  (at level 99, A at next level, no associativity).
Inductive subtyping : ctx -> typ -> typ -> Prop :=
| sub_top Γ A :
  Γ ⊢ A ->
  Γ ⊢ A <: typ_top
| sub_tvar_refl Γ X :
  Γ ⊢ typ_var X ->
  Γ ⊢ typ_var X <: typ_var X
| sub_tvar_bound Γ X A B: 
  lookup_tvar X Γ A ->
  Γ ⊢ A <: B ->
  Γ ⊢ typ_var X <: B
| sub_arrow Γ A1 A2 B1 B2 : 
  Γ ⊢ B1 <: A1 ->
  Γ ⊢ A2 <: B2 ->
  Γ ⊢ (typ_arr A1 A2) <: (typ_arr B1 B2)
| sub_all Γ A1 A2 B1 B2
  (Hwf : Γ ⊢ B1) 
  (Hsub1 : Γ ⊢ B1 <: A1)
  (Hsub2 : ((entry_tvar B1) :: Γ) ⊢ A2 <: B2) :
  Γ ⊢ (typ_all A1 A2) <: (typ_all B1 B2)
where "Γ ⊢ A <: B" := (subtyping Γ A B).

Reserved Notation "Γ ⊢ t : A" 
  (at level 99, t at next level, no associativity).
Inductive typing : ctx -> exp -> typ -> Prop :=
| typing_var Γ i A :
  lookup_var i Γ A ->
  Γ ⊢ (exp_var i) : A
| typing_abs Γ t A B :
  Γ ⊢ A ->
  (entry_var A :: Γ) ⊢ t : B ->
  Γ ⊢ (exp_abs A t) : (typ_arr A B)
| typing_app Γ s t A B :
  Γ ⊢ t : (typ_arr A B) ->
  Γ ⊢ s : A ->
  Γ ⊢ (exp_app t s) : B
| typing_tabs : forall Γ t A B,
  Γ ⊢ A ->
  (entry_tvar A :: (map (ren_var_entry ↑) Γ)) ⊢ t : B ->
  Γ ⊢ (exp_tabs A t) : (typ_all A B)
| typing_tapp : forall Γ t A B A' B',
  Γ ⊢ t : (typ_all A B) ->
  Γ ⊢ A' <: A ->
  B' = B [A'..] ->
  Γ ⊢ exp_tapp t A' : B'
| typing_sub : forall Γ t A B,
  Γ ⊢ t : A ->
  Γ ⊢ A <: B ->
  Γ ⊢ t : B
where " Γ ⊢ t : A" := (typing Γ t A).

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