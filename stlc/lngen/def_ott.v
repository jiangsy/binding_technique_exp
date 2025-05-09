(* generated by Ott 0.34, locally-nameless lngen from: stlc/lngen/language.ott *)
Require Import Bool.
Require Import Metalib.Metatheory.
Require Import List.
(** syntax *)
Definition expvar : Set := var.

Inductive exp : Set := 
 | exp_var_b (_:nat)
 | exp_var_f (x:expvar)
 | exp_unit : exp
 | exp_abs (e:exp)
 | exp_app (e1:exp) (e2:exp).

Inductive typ : Set := 
 | typ_unit : typ
 | typ_arr (A1:typ) (A2:typ).

(* EXPERIMENTAL *)
(** auxiliary functions on the new list types *)
(** library functions *)
(** subrules *)
(** arities *)
(** opening up abstractions *)
Fixpoint open_exp_wrt_exp_rec (k:nat) (e_5:exp) (e__6:exp) {struct e__6}: exp :=
  match e__6 with
  | (exp_var_b nat) => 
      match lt_eq_lt_dec nat k with
        | inleft (left _) => exp_var_b nat
        | inleft (right _) => e_5
        | inright _ => exp_var_b (nat - 1)
      end
  | (exp_var_f x) => exp_var_f x
  | exp_unit => exp_unit 
  | (exp_abs e) => exp_abs (open_exp_wrt_exp_rec (S k) e_5 e)
  | (exp_app e1 e2) => exp_app (open_exp_wrt_exp_rec k e_5 e1) (open_exp_wrt_exp_rec k e_5 e2)
end.

Definition open_exp_wrt_exp e_5 e__6 := open_exp_wrt_exp_rec 0 e__6 e_5.

(** terms are locally-closed pre-terms *)
(* definitions *)

(* defns LC_exp *)
Inductive lc_exp : exp -> Prop :=    (* defn lc_exp *)
 | lc_exp_var_f : forall (x:expvar),
     (lc_exp (exp_var_f x))
 | lc_exp_unit : 
     (lc_exp exp_unit)
 | lc_exp_abs : forall (e:exp),
      ( forall x , lc_exp  ( open_exp_wrt_exp e (exp_var_f x) )  )  ->
     (lc_exp (exp_abs e))
 | lc_exp_app : forall (e1 e2:exp),
     (lc_exp e1) ->
     (lc_exp e2) ->
     (lc_exp (exp_app e1 e2)).
(** free variables *)
Fixpoint var_in_exp (e_5:exp) : vars :=
  match e_5 with
  | (exp_var_b nat) => {}
  | (exp_var_f x) => {{x}}
  | exp_unit => {}
  | (exp_abs e) => (var_in_exp e)
  | (exp_app e1 e2) => (var_in_exp e1) \u (var_in_exp e2)
end.

(** substitutions *)
Fixpoint subst_exp_in_exp (e_5:exp) (x5:expvar) (e__6:exp) {struct e__6} : exp :=
  match e__6 with
  | (exp_var_b nat) => exp_var_b nat
  | (exp_var_f x) => (if eq_var x x5 then e_5 else (exp_var_f x))
  | exp_unit => exp_unit 
  | (exp_abs e) => exp_abs (subst_exp_in_exp e_5 x5 e)
  | (exp_app e1 e2) => exp_app (subst_exp_in_exp e_5 x5 e1) (subst_exp_in_exp e_5 x5 e2)
end.


(* definitions *)


(** infrastructure *)
#[export] Hint Constructors lc_exp : core.


