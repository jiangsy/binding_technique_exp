Require Import List.

Require Import common.prop_as_core.
Require Import common.prop_as_unscoped.
Require Import fsub.autosubst2_sctx.def_as2.

Import SubstNotations.
Import UnscopedNotations.

Definition ctx := list entry.

Definition ren_entry (ξ : nat -> nat) (e : entry) : entry :=
  match e with
  | entry_var A => entry_var (A ⟨ ξ ⟩)
  | entry_tvar A => entry_tvar (A ⟨ ξ ⟩)
  end.

Inductive lookup_tvar : nat -> list entry -> typ -> Prop :=
| here_tvar A Δ : lookup_tvar 0 ((entry_tvar A) :: Δ) (A ⟨ ↑ ⟩) 
| skip_var n Δ A B : lookup_tvar n Δ A -> lookup_tvar n (cons (entry_var B) Δ) A
| there_tvar n Δ A B : lookup_tvar n Δ A -> lookup_tvar (S n) (cons (entry_tvar B) Δ) (A ⟨ ↑ ⟩).

Inductive lookup_var : nat -> list entry -> typ -> Prop :=
| here_var A Γ : lookup_var 0 ((entry_var A) :: Γ) A 
| skip_tvar n Γ A B : lookup_var n Γ A -> lookup_var n (cons (entry_tvar B) Γ) (A ⟨ ↑ ⟩)
| there_var n Γ A B : lookup_var n Γ A -> lookup_var (S n) (cons (entry_var B) Γ) A.

Fixpoint wf_typ Δ A := match A with
  | typ_var X => exists B, lookup_tvar X Δ B
  | typ_top => True
  | typ_arr A B => wf_typ Δ A /\ wf_typ Δ B
  | typ_all A B => wf_typ Δ A /\ wf_typ ((entry_tvar A) :: Δ) B
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
  lookup_tvar X Δ A ->
  Δ ⊢ A <: B ->
  Δ ⊢ typ_var X <: B
| sub_arrow Δ A1 A2 B1 B2 : 
  Δ ⊢ B1 <: A1 ->
  Δ ⊢ A2 <: B2 ->
  Δ ⊢ (typ_arr A1 A2) <: (typ_arr B1 B2)
| sub_all Δ A1 A2 B1 B2
  (Hwf : Δ ⊢ B1) 
  (Hsub1 : Δ ⊢ B1 <: A1)
  (Hsub2 : ((entry_tvar B1) :: Δ) ⊢ A2 <: B2) :
  Δ ⊢ (typ_all A1 A2) <: (typ_all B1 B2)
where "Δ ⊢ A <: B" := (subtyping Δ A B).

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
  (entry_tvar A :: (map (ren_entry ↑) Γ)) ⊢ t : B ->
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