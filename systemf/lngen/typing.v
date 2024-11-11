Require Import systemf.lngen.def_ott.
Require Import systemf.lngen.prop_ln.


Inductive ctx_entry :=
| tvar
| var_typ (A : typ).

Definition ctx := list (atom * ctx_entry).

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