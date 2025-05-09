(* generated by Ott 0.34, locally-nameless lngen from: systemf/lngen/language.ott *)
Require Import Bool.
Require Import Metalib.Metatheory.
Require Import List.
(** syntax *)
Definition typvar : Set := var.
Definition expvar : Set := var.

Inductive typ : Set := 
 | typ_var_b (_:nat)
 | typ_var_f (X:typvar)
 | typ_arr (A1:typ) (A2:typ)
 | typ_all (A:typ).

Inductive entry : Set := 
 | entry_var (A:typ)
 | entry_tvar : entry.

Inductive exp : Set := 
 | exp_var_b (_:nat)
 | exp_var_f (x:expvar)
 | exp_abs (A:typ) (e:exp)
 | exp_app (e1:exp) (e2:exp)
 | exp_tabs (e:exp)
 | exp_tapp (e:exp) (A:typ).

(* EXPERIMENTAL *)
(** auxiliary functions on the new list types *)
(** library functions *)
(** subrules *)
(** arities *)
(** opening up abstractions *)
Fixpoint open_typ_wrt_typ_rec (k:nat) (A_5:typ) (A__6:typ) {struct A__6}: typ :=
  match A__6 with
  | (typ_var_b nat) => 
      match lt_eq_lt_dec nat k with
        | inleft (left _) => typ_var_b nat
        | inleft (right _) => A_5
        | inright _ => typ_var_b (nat - 1)
      end
  | (typ_var_f X) => typ_var_f X
  | (typ_arr A1 A2) => typ_arr (open_typ_wrt_typ_rec k A_5 A1) (open_typ_wrt_typ_rec k A_5 A2)
  | (typ_all A) => typ_all (open_typ_wrt_typ_rec (S k) A_5 A)
end.

Definition open_entry_wrt_typ_rec (k:nat) (A5:typ) (entry5:entry) : entry :=
  match entry5 with
  | (entry_var A) => entry_var (open_typ_wrt_typ_rec k A5 A)
  | entry_tvar => entry_tvar 
end.

Fixpoint open_exp_wrt_exp_rec (k:nat) (e_5:exp) (e__6:exp) {struct e__6}: exp :=
  match e__6 with
  | (exp_var_b nat) => 
      match lt_eq_lt_dec nat k with
        | inleft (left _) => exp_var_b nat
        | inleft (right _) => e_5
        | inright _ => exp_var_b (nat - 1)
      end
  | (exp_var_f x) => exp_var_f x
  | (exp_abs A e) => exp_abs A (open_exp_wrt_exp_rec (S k) e_5 e)
  | (exp_app e1 e2) => exp_app (open_exp_wrt_exp_rec k e_5 e1) (open_exp_wrt_exp_rec k e_5 e2)
  | (exp_tabs e) => exp_tabs (open_exp_wrt_exp_rec k e_5 e)
  | (exp_tapp e A) => exp_tapp (open_exp_wrt_exp_rec k e_5 e) A
end.

Fixpoint open_exp_wrt_typ_rec (k:nat) (A_5:typ) (e_5:exp) {struct e_5}: exp :=
  match e_5 with
  | (exp_var_b nat) => exp_var_b nat
  | (exp_var_f x) => exp_var_f x
  | (exp_abs A e) => exp_abs (open_typ_wrt_typ_rec k A_5 A) (open_exp_wrt_typ_rec k A_5 e)
  | (exp_app e1 e2) => exp_app (open_exp_wrt_typ_rec k A_5 e1) (open_exp_wrt_typ_rec k A_5 e2)
  | (exp_tabs e) => exp_tabs (open_exp_wrt_typ_rec (S k) A_5 e)
  | (exp_tapp e A) => exp_tapp (open_exp_wrt_typ_rec k A_5 e) (open_typ_wrt_typ_rec k A_5 A)
end.

Definition open_entry_wrt_typ A5 entry5 := open_entry_wrt_typ_rec 0 entry5 A5.

Definition open_exp_wrt_exp e_5 e__6 := open_exp_wrt_exp_rec 0 e__6 e_5.

Definition open_exp_wrt_typ A_5 e_5 := open_exp_wrt_typ_rec 0 e_5 A_5.

Definition open_typ_wrt_typ A_5 A__6 := open_typ_wrt_typ_rec 0 A__6 A_5.

(** terms are locally-closed pre-terms *)
(* definitions *)

(* defns LC_typ *)
Inductive lc_typ : typ -> Prop :=    (* defn lc_typ *)
 | lc_typ_var_f : forall (X:typvar),
     (lc_typ (typ_var_f X))
 | lc_typ_arr : forall (A1 A2:typ),
     (lc_typ A1) ->
     (lc_typ A2) ->
     (lc_typ (typ_arr A1 A2))
 | lc_typ_all : forall (A:typ),
      ( forall X , lc_typ  ( open_typ_wrt_typ A (typ_var_f X) )  )  ->
     (lc_typ (typ_all A)).

(* defns LC_entry *)
Inductive lc_entry : entry -> Prop :=    (* defn lc_entry *)
 | lc_entry_var : forall (A:typ),
     (lc_typ A) ->
     (lc_entry (entry_var A))
 | lc_entry_tvar : 
     (lc_entry entry_tvar).

(* defns LC_exp *)
Inductive lc_exp : exp -> Prop :=    (* defn lc_exp *)
 | lc_exp_var_f : forall (x:expvar),
     (lc_exp (exp_var_f x))
 | lc_exp_abs : forall (A:typ) (e:exp),
     (lc_typ A) ->
      ( forall x , lc_exp  ( open_exp_wrt_exp e (exp_var_f x) )  )  ->
     (lc_exp (exp_abs A e))
 | lc_exp_app : forall (e1 e2:exp),
     (lc_exp e1) ->
     (lc_exp e2) ->
     (lc_exp (exp_app e1 e2))
 | lc_exp_tabs : forall (e:exp),
      ( forall X , lc_exp  ( open_exp_wrt_typ e (typ_var_f X) )  )  ->
     (lc_exp (exp_tabs e))
 | lc_exp_tapp : forall (e:exp) (A:typ),
     (lc_exp e) ->
     (lc_typ A) ->
     (lc_exp (exp_tapp e A)).
(** free variables *)
Fixpoint tvar_in_typ (A_5:typ) : vars :=
  match A_5 with
  | (typ_var_b nat) => {}
  | (typ_var_f X) => {{X}}
  | (typ_arr A1 A2) => (tvar_in_typ A1) \u (tvar_in_typ A2)
  | (typ_all A) => (tvar_in_typ A)
end.

Fixpoint var_in_exp (e_5:exp) : vars :=
  match e_5 with
  | (exp_var_b nat) => {}
  | (exp_var_f x) => {{x}}
  | (exp_abs A e) => (var_in_exp e)
  | (exp_app e1 e2) => (var_in_exp e1) \u (var_in_exp e2)
  | (exp_tabs e) => (var_in_exp e)
  | (exp_tapp e A) => (var_in_exp e)
end.

Definition tvar_in_entry (entry5:entry) : vars :=
  match entry5 with
  | (entry_var A) => (tvar_in_typ A)
  | entry_tvar => {}
end.

Fixpoint tvar_in_exp (e_5:exp) : vars :=
  match e_5 with
  | (exp_var_b nat) => {}
  | (exp_var_f x) => {}
  | (exp_abs A e) => (tvar_in_typ A) \u (tvar_in_exp e)
  | (exp_app e1 e2) => (tvar_in_exp e1) \u (tvar_in_exp e2)
  | (exp_tabs e) => (tvar_in_exp e)
  | (exp_tapp e A) => (tvar_in_exp e) \u (tvar_in_typ A)
end.

(** substitutions *)
Fixpoint subst_typ_in_typ (A_5:typ) (X5:typvar) (A__6:typ) {struct A__6} : typ :=
  match A__6 with
  | (typ_var_b nat) => typ_var_b nat
  | (typ_var_f X) => (if eq_var X X5 then A_5 else (typ_var_f X))
  | (typ_arr A1 A2) => typ_arr (subst_typ_in_typ A_5 X5 A1) (subst_typ_in_typ A_5 X5 A2)
  | (typ_all A) => typ_all (subst_typ_in_typ A_5 X5 A)
end.

Fixpoint subst_exp_in_exp (e_5:exp) (x5:expvar) (e__6:exp) {struct e__6} : exp :=
  match e__6 with
  | (exp_var_b nat) => exp_var_b nat
  | (exp_var_f x) => (if eq_var x x5 then e_5 else (exp_var_f x))
  | (exp_abs A e) => exp_abs A (subst_exp_in_exp e_5 x5 e)
  | (exp_app e1 e2) => exp_app (subst_exp_in_exp e_5 x5 e1) (subst_exp_in_exp e_5 x5 e2)
  | (exp_tabs e) => exp_tabs (subst_exp_in_exp e_5 x5 e)
  | (exp_tapp e A) => exp_tapp (subst_exp_in_exp e_5 x5 e) A
end.

Definition subst_typ_in_entry (A5:typ) (X5:typvar) (entry5:entry) : entry :=
  match entry5 with
  | (entry_var A) => entry_var (subst_typ_in_typ A5 X5 A)
  | entry_tvar => entry_tvar 
end.

Fixpoint subst_typ_in_exp (A_5:typ) (X5:typvar) (e_5:exp) {struct e_5} : exp :=
  match e_5 with
  | (exp_var_b nat) => exp_var_b nat
  | (exp_var_f x) => exp_var_f x
  | (exp_abs A e) => exp_abs (subst_typ_in_typ A_5 X5 A) (subst_typ_in_exp A_5 X5 e)
  | (exp_app e1 e2) => exp_app (subst_typ_in_exp A_5 X5 e1) (subst_typ_in_exp A_5 X5 e2)
  | (exp_tabs e) => exp_tabs (subst_typ_in_exp A_5 X5 e)
  | (exp_tapp e A) => exp_tapp (subst_typ_in_exp A_5 X5 e) (subst_typ_in_typ A_5 X5 A)
end.


(* definitions *)


(** infrastructure *)
#[export] Hint Constructors lc_typ lc_entry lc_exp : core.


