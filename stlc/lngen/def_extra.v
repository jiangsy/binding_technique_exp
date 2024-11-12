Require Import stlc.lngen.def_ott.
Require Import stlc.lngen.prop_ln.

Definition ctx := list (atom * typ).

Reserved Notation "Γ ⊢ t : A" 
  (at level 99, t at next level, no associativity).
Inductive typing : ctx -> exp -> typ -> Prop :=
| typing_var : forall (Γ : ctx) (x : atom) (A : typ),
  binds x A Γ ->
  Γ ⊢ (exp_var_f x) : A
| typing_unit : forall (Γ : ctx),
  Γ ⊢ exp_unit : typ_unit
| typing_abs : forall (L : atoms) (Γ : ctx) (A B : typ) (t : exp),
  (forall x, 
    x `notin` L -> ((x , A) :: Γ) ⊢ open_exp_wrt_exp t (exp_var_f x) : B) ->
  Γ ⊢ (exp_abs t) : (typ_arr A B)
| typing_app : forall (Γ : ctx) (s t : exp) (A B : typ),
  Γ ⊢ s : (typ_arr A B) ->
  Γ ⊢ t : A ->
  Γ ⊢ (exp_app s t) : B
where "Γ ⊢ t : A" := (typing Γ t A).

Reserved Notation "t ⤳ t'" (at level 80).
Inductive step : exp -> exp -> Prop :=
| step_beta : forall (t s : exp),
  exp_app (exp_abs t) s ⤳ open_exp_wrt_exp t s
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

Ltac gather_atoms ::=
  let A := gather_atoms_with (fun x : vars => x) in
  let B := gather_atoms_with (fun x : var => {{ x }}) in
  let C := gather_atoms_with (fun x => var_in_exp x) in
  let D := gather_atoms_with (fun x : ctx => dom x) in

  constr:(A \u B \u C \u D).