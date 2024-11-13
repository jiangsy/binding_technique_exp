Require Import systemf.lngen.def_ott.
Require Import systemf.lngen.prop_ln.

Inductive ctx_entry :=
| tvar
| var_typ (A : typ).

Definition ctx := list (atom * ctx_entry).

Ltac gather_atoms ::=
  let A := gather_atoms_with (fun x : vars => x) in
  let B := gather_atoms_with (fun x : var => {{ x }}) in
  let C1 := gather_atoms_with (fun x : exp => var_in_exp x) in
  let C2 := gather_atoms_with (fun x : exp => tvar_in_exp x) in
  let D := gather_atoms_with (fun x : typ => tvar_in_typ x) in
  let DE:= gather_atoms_with (fun x : ctx => dom x) in
  constr:(A \u B \u C1 \u C2 \u D \u D).

Reserved Notation "Γ ⊢ t : A" 
  (at level 50, t at next level, no associativity).
Inductive typing : ctx -> exp -> typ -> Prop :=
| typing_var : forall (Γ : ctx) (x : atom) (A : typ),
  binds x (var_typ A) Γ ->
  Γ ⊢ (exp_var_f x) : A
| typing_abs : forall (L : atoms) (Γ : ctx) (A B : typ) (t : exp),
  (forall x, 
    x `notin` L -> ((x , var_typ A) :: Γ) ⊢ t : B) ->
  Γ ⊢ (exp_abs A t) : (typ_arr A B)
| typing_app : forall (Γ : ctx) (s t : exp) (A B : typ),
  Γ ⊢ s : (typ_arr A B) ->
  Γ ⊢ t : A ->
  Γ ⊢ (exp_app s t) : B
| typing_tabs : forall (L : atoms) (Γ : ctx) (t : exp) (A : typ),
  (forall X, X `notin` L -> 
    ((X , tvar) :: Γ) ⊢ t : open_typ_wrt_typ A (typ_var_f X)) ->
  Γ ⊢ (exp_tabs t) : (typ_all A)
| typing_tapp : forall (Γ : ctx) (t : exp) (A B A' : typ),
  Γ ⊢ t : (typ_all A) ->
  Γ ⊢ exp_tapp t B : (open_typ_wrt_typ A B)
where "Γ ⊢ t : A" := (typing Γ t A).

Definition is_value (t : exp) : Prop :=
  match t with
  | exp_abs _ _ => True
  | exp_tabs _ => True
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
| step_inst t A: 
  exp_tapp (exp_tabs t) A ⤳ open_exp_wrt_typ t A
where "t ⤳ t'" := (step t t').