Require Import fsub.lngen.def_ott.
Require Import fsub.lngen.prop_ln.

Definition ctx := list (atom * entry).

Fixpoint tvar_in_entries (Γ : ctx) : atoms :=
  match Γ with
  | nil => {}
  | (X, entry_tvar A) :: Γ' => tvar_in_typ A \u (tvar_in_entries Γ')
  | (X, entry_var A) :: Γ' => tvar_in_typ A \u tvar_in_entries Γ'
  end.

Ltac gather_atoms ::=
  let A := gather_atoms_with (fun x : vars => x) in
  let B := gather_atoms_with (fun x : var => {{ x }}) in
  let C1 := gather_atoms_with (fun x : exp => var_in_exp x) in
  let C2 := gather_atoms_with (fun x : exp => tvar_in_exp x) in
  let D := gather_atoms_with (fun x : typ => tvar_in_typ x) in
  let E1:= gather_atoms_with (fun x : ctx => dom x) in
  let E2:= gather_atoms_with (fun x : ctx => tvar_in_entries x) in
  constr:(A \u B \u C1 \u C2 \u D \u E1 \u E2).

Reserved Notation "Γ ⊢ A" (at level 50, no associativity).
Inductive wf_typ : ctx -> typ -> Prop :=
| wf_tvar : forall Γ X A,
  binds X (entry_tvar A) Γ ->
  Γ ⊢ typ_var_f X
| wf_top : forall Γ,
  Γ ⊢ typ_top
| wf_arr : forall Γ A B,
  Γ ⊢ A -> 
  Γ ⊢ B -> 
  Γ ⊢ typ_arr A B
| wf_all : forall L Γ A B,
  Γ ⊢ A ->
  (forall X, X `notin` L ->
    ((X, entry_tvar A) :: Γ) ⊢ open_typ_wrt_typ B (typ_var_f X)) ->
  Γ ⊢ typ_all A B
where "Γ ⊢ A" := (wf_typ Γ A).

Reserved Notation "Γ ⊢ A <: B" (at level 50, A at next level, no associativity).
Inductive subtyping : ctx -> typ -> typ -> Prop :=
| sub_top : forall Γ A,
  Γ ⊢ A ->
  Γ ⊢ A <: typ_top
| sub_tvar_refl : forall Γ X,
  Γ ⊢ typ_var_f X ->
  Γ ⊢ typ_var_f X <: typ_var_f X
| sub_tvar_bound : forall Γ X A B,
  binds X (entry_tvar A) Γ ->
  Γ ⊢ A <: B ->
  Γ ⊢ typ_var_f X <: B
| sub_arrow : forall Γ A1 A2 B1 B2,
  Γ ⊢ B1 <: A1 ->
  Γ ⊢ A2 <: B2 ->
  Γ ⊢ (typ_arr A1 A2) <: (typ_arr B1 B2)
| sub_all : forall L Γ A1 A2 B1 B2,
  Γ ⊢ B1 ->
  Γ ⊢ B1 <: A1 ->
  (forall X, X `notin` L ->
    ((X, entry_tvar B1) :: Γ) ⊢ open_typ_wrt_typ A2 (typ_var_f X) <: open_typ_wrt_typ B2 (typ_var_f X)) ->
  Γ ⊢ (typ_all A1 A2) <: (typ_all B1 B2)
where "Γ ⊢ A <: B" := (subtyping Γ A B).

Reserved Notation "Γ ⊢ t : A" 
  (at level 50, t at next level, no associativity).
Inductive typing : ctx -> exp -> typ -> Prop :=
| typing_var : forall (Γ : ctx) (x : atom) (A : typ),
  lc_typ A ->
  binds x (entry_var A) Γ ->
  Γ ⊢ (exp_var_f x) : A
| typing_abs : forall (L : atoms) (Γ : ctx) (A B : typ) (t : exp),
  lc_typ A ->
  (forall x, 
    x `notin` L -> ((x , entry_var A) :: Γ) ⊢ open_exp_wrt_exp t (exp_var_f x) : B) ->
  Γ ⊢ (exp_abs A t) : (typ_arr A B)
| typing_app : forall (Γ : ctx) (s t : exp) (A B : typ),
  Γ ⊢ s : (typ_arr A B) ->
  Γ ⊢ t : A ->
  Γ ⊢ (exp_app s t) : B
| typing_tabs : forall (L : atoms) (Γ : ctx) (t : exp) (A B : typ),
  (forall X, X `notin` L -> 
    ((X , entry_tvar A) :: Γ) ⊢ (open_exp_wrt_typ t (typ_var_f X)) : open_typ_wrt_typ B (typ_var_f X)) ->
  Γ ⊢ (exp_tabs A t) : (typ_all A B)
| typing_tapp : forall (Γ : ctx) (t : exp) (A B C: typ),
  Γ ⊢ C <: A ->
  Γ ⊢ t : (typ_all A B) ->
  Γ ⊢ exp_tapp t C : (open_typ_wrt_typ B C)
where "Γ ⊢ t : A" := (typing Γ t A).

Definition is_value (t : exp) : Prop :=
  match t with
  | exp_abs _ _ => True
  | exp_tabs _ _ => True
  | _ => False
  end.

Reserved Notation "t ⤳ t'" (at level 80).
Inductive step : exp -> exp -> Prop :=
| step_appl t t' s : 
  t ⤳ t' -> 
  exp_app t s ⤳ exp_app t' s
| step_appr t s s' : 
  is_value t ->
  s ⤳ s' -> 
  exp_app t s ⤳ exp_app t s'
| step_beta t s A : 
  is_value s ->
  exp_app (exp_abs A t) s ⤳ open_exp_wrt_exp t s
| step_tapp t t' A : 
  t ⤳ t' ->
  exp_tapp t A ⤳ exp_tapp t' A
| step_inst t A B :  
  exp_tapp (exp_tabs A t) B ⤳ open_exp_wrt_typ t B
where "t ⤳ t'" := (step t t').