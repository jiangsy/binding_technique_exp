Require Import systemf.lngen.def.
Require Import systemf.lngen.prop_ln.


Inductive ctx_entry :=
| tvar
| var_typ (A : ftyp).

Definition ctx := list (atom * ctx_entry).

Reserved Notation "Γ ⊢ t : A" 
  (at level 50, t at next level, no associativity).
Inductive typing : ctx -> fexp -> ftyp -> Prop :=
| typing_var : forall (Γ : ctx) (x : atom) (A : ftyp),
  binds x (var_typ A) Γ ->
  Γ ⊢ (fexp_var_f x) : A
| typing_abs : forall (L : atoms) (Γ : ctx) (A B : ftyp) (t : fexp),
  (forall x, 
    x `notin` L -> ((x , var_typ A) :: Γ) ⊢ t : B) ->
  Γ ⊢ (fexp_abs A t) : (ftyp_arr A B)
| typing_app : forall (Γ : ctx) (s t : fexp) (A B : ftyp),
  Γ ⊢ s : (ftyp_arr A B) ->
  Γ ⊢ t : A ->
  Γ ⊢ (fexp_app s t) : B
| typing_tabs : forall (L : atoms) (Γ : ctx) (t : fexp) (A : ftyp),
  (forall X, X `notin` L -> 
    ((X , tvar) :: Γ) ⊢ t : open_ftyp_wrt_ftyp A (ftyp_var_f X)) ->
  Γ ⊢ (fexp_tabs t) : (ftyp_all A)
| typing_tapp : forall (Γ : ctx) (t : fexp) (A B A' : ftyp),
  Γ ⊢ t : (ftyp_all A) ->
  Γ ⊢ fexp_tapp t B : (open_ftyp_wrt_ftyp A B)
where "Γ ⊢ t : A" := (typing Γ t A).