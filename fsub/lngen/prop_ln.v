Require Import Coq.Arith.Wf_nat.
Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.Program.Equality.

Require Export Metalib.Metatheory.
Require Export Metalib.LibLNgen.

Require Export fsub.lngen.def_ott.

Local Set Warnings "-non-recursive". 

(** NOTE: Auxiliary theorems are hidden in generated documentation.
    In general, there is a [_rec] version of every lemma involving
    [open] and [close]. *)


(* *********************************************************************** *)
(** * Induction principles for nonterminals *)

Scheme typ_ind' := Induction for typ Sort Prop.

Combined Scheme typ_mutind from typ_ind'.

Scheme typ_rec' := Induction for typ Sort Set.

Combined Scheme typ_mutrec from typ_rec'.

Scheme exp_ind' := Induction for exp Sort Prop.

Combined Scheme exp_mutind from exp_ind'.

Scheme exp_rec' := Induction for exp Sort Set.

Combined Scheme exp_mutrec from exp_rec'.

Scheme entry_ind' := Induction for entry Sort Prop.

Combined Scheme entry_mutind from entry_ind'.

Scheme entry_rec' := Induction for entry Sort Set.

Combined Scheme entry_mutrec from entry_rec'.


(* *********************************************************************** *)
(** * Close *)

Fixpoint close_typ_wrt_typ_rec (n1 : nat) (X1 : typvar) (A1 : typ) {struct A1} : typ :=
  match A1 with
    | typ_var_f X2 => if (X1 == X2) then (typ_var_b n1) else (typ_var_f X2)
    | typ_var_b n2 => if (lt_ge_dec n2 n1) then (typ_var_b n2) else (typ_var_b (S n2))
    | typ_top => typ_top
    | typ_arr A2 A3 => typ_arr (close_typ_wrt_typ_rec n1 X1 A2) (close_typ_wrt_typ_rec n1 X1 A3)
    | typ_all B1 A2 => typ_all (close_typ_wrt_typ_rec n1 X1 B1) (close_typ_wrt_typ_rec (S n1) X1 A2)
  end.

Definition close_typ_wrt_typ X1 A1 := close_typ_wrt_typ_rec 0 X1 A1.

Fixpoint close_exp_wrt_typ_rec (n1 : nat) (X1 : typvar) (e1 : exp) {struct e1} : exp :=
  match e1 with
    | exp_var_f x1 => exp_var_f x1
    | exp_var_b n2 => exp_var_b n2
    | exp_abs A1 e2 => exp_abs (close_typ_wrt_typ_rec n1 X1 A1) (close_exp_wrt_typ_rec n1 X1 e2)
    | exp_app e2 e3 => exp_app (close_exp_wrt_typ_rec n1 X1 e2) (close_exp_wrt_typ_rec n1 X1 e3)
    | exp_tabs A1 e2 => exp_tabs (close_typ_wrt_typ_rec n1 X1 A1) (close_exp_wrt_typ_rec (S n1) X1 e2)
    | exp_tapp e2 A1 => exp_tapp (close_exp_wrt_typ_rec n1 X1 e2) (close_typ_wrt_typ_rec n1 X1 A1)
  end.

Fixpoint close_exp_wrt_exp_rec (n1 : nat) (x1 : expvar) (e1 : exp) {struct e1} : exp :=
  match e1 with
    | exp_var_f x2 => if (x1 == x2) then (exp_var_b n1) else (exp_var_f x2)
    | exp_var_b n2 => if (lt_ge_dec n2 n1) then (exp_var_b n2) else (exp_var_b (S n2))
    | exp_abs A1 e2 => exp_abs A1 (close_exp_wrt_exp_rec (S n1) x1 e2)
    | exp_app e2 e3 => exp_app (close_exp_wrt_exp_rec n1 x1 e2) (close_exp_wrt_exp_rec n1 x1 e3)
    | exp_tabs A1 e2 => exp_tabs A1 (close_exp_wrt_exp_rec n1 x1 e2)
    | exp_tapp e2 A1 => exp_tapp (close_exp_wrt_exp_rec n1 x1 e2) A1
  end.

Definition close_exp_wrt_typ X1 e1 := close_exp_wrt_typ_rec 0 X1 e1.

Definition close_exp_wrt_exp x1 e1 := close_exp_wrt_exp_rec 0 x1 e1.

Fixpoint close_entry_wrt_typ_rec (n1 : nat) (X1 : typvar) (et1 : entry) {struct et1} : entry :=
  match et1 with
    | entry_tvar A1 => entry_tvar (close_typ_wrt_typ_rec n1 X1 A1)
    | entry_var A1 => entry_var (close_typ_wrt_typ_rec n1 X1 A1)
  end.

Definition close_entry_wrt_typ X1 et1 := close_entry_wrt_typ_rec 0 X1 et1.


(* *********************************************************************** *)
(** * Size *)

Fixpoint size_typ (A1 : typ) {struct A1} : nat :=
  match A1 with
    | typ_var_f X1 => 1
    | typ_var_b n1 => 1
    | typ_top => 1
    | typ_arr A2 A3 => 1 + (size_typ A2) + (size_typ A3)
    | typ_all B1 A2 => 1 + (size_typ B1) + (size_typ A2)
  end.

Fixpoint size_exp (e1 : exp) {struct e1} : nat :=
  match e1 with
    | exp_var_f x1 => 1
    | exp_var_b n1 => 1
    | exp_abs A1 e2 => 1 + (size_typ A1) + (size_exp e2)
    | exp_app e2 e3 => 1 + (size_exp e2) + (size_exp e3)
    | exp_tabs A1 e2 => 1 + (size_typ A1) + (size_exp e2)
    | exp_tapp e2 A1 => 1 + (size_exp e2) + (size_typ A1)
  end.

Fixpoint size_entry (et1 : entry) {struct et1} : nat :=
  match et1 with
    | entry_tvar A1 => 1 + (size_typ A1)
    | entry_var A1 => 1 + (size_typ A1)
  end.


(* *********************************************************************** *)
(** * Degree *)

(** These define only an upper bound, not a strict upper bound. *)

Inductive degree_typ_wrt_typ : nat -> typ -> Prop :=
  | degree_wrt_typ_typ_var_f : forall n1 X1,
    degree_typ_wrt_typ n1 (typ_var_f X1)
  | degree_wrt_typ_typ_var_b : forall n1 n2,
    lt n2 n1 ->
    degree_typ_wrt_typ n1 (typ_var_b n2)
  | degree_wrt_typ_typ_top : forall n1,
    degree_typ_wrt_typ n1 (typ_top)
  | degree_wrt_typ_typ_arr : forall n1 A1 A2,
    degree_typ_wrt_typ n1 A1 ->
    degree_typ_wrt_typ n1 A2 ->
    degree_typ_wrt_typ n1 (typ_arr A1 A2)
  | degree_wrt_typ_typ_all : forall n1 B1 A1,
    degree_typ_wrt_typ n1 B1 ->
    degree_typ_wrt_typ (S n1) A1 ->
    degree_typ_wrt_typ n1 (typ_all B1 A1).

Scheme degree_typ_wrt_typ_ind' := Induction for degree_typ_wrt_typ Sort Prop.

Combined Scheme degree_typ_wrt_typ_mutind from degree_typ_wrt_typ_ind'.

#[export] Hint Constructors degree_typ_wrt_typ : core lngen.

Inductive degree_exp_wrt_typ : nat -> exp -> Prop :=
  | degree_wrt_typ_exp_var_f : forall n1 x1,
    degree_exp_wrt_typ n1 (exp_var_f x1)
  | degree_wrt_typ_exp_var_b : forall n1 n2,
    degree_exp_wrt_typ n1 (exp_var_b n2)
  | degree_wrt_typ_exp_abs : forall n1 A1 e1,
    degree_typ_wrt_typ n1 A1 ->
    degree_exp_wrt_typ n1 e1 ->
    degree_exp_wrt_typ n1 (exp_abs A1 e1)
  | degree_wrt_typ_exp_app : forall n1 e1 e2,
    degree_exp_wrt_typ n1 e1 ->
    degree_exp_wrt_typ n1 e2 ->
    degree_exp_wrt_typ n1 (exp_app e1 e2)
  | degree_wrt_typ_exp_tabs : forall n1 A1 e1,
    degree_typ_wrt_typ n1 A1 ->
    degree_exp_wrt_typ (S n1) e1 ->
    degree_exp_wrt_typ n1 (exp_tabs A1 e1)
  | degree_wrt_typ_exp_tapp : forall n1 e1 A1,
    degree_exp_wrt_typ n1 e1 ->
    degree_typ_wrt_typ n1 A1 ->
    degree_exp_wrt_typ n1 (exp_tapp e1 A1).

Inductive degree_exp_wrt_exp : nat -> exp -> Prop :=
  | degree_wrt_exp_exp_var_f : forall n1 x1,
    degree_exp_wrt_exp n1 (exp_var_f x1)
  | degree_wrt_exp_exp_var_b : forall n1 n2,
    lt n2 n1 ->
    degree_exp_wrt_exp n1 (exp_var_b n2)
  | degree_wrt_exp_exp_abs : forall n1 A1 e1,
    degree_exp_wrt_exp (S n1) e1 ->
    degree_exp_wrt_exp n1 (exp_abs A1 e1)
  | degree_wrt_exp_exp_app : forall n1 e1 e2,
    degree_exp_wrt_exp n1 e1 ->
    degree_exp_wrt_exp n1 e2 ->
    degree_exp_wrt_exp n1 (exp_app e1 e2)
  | degree_wrt_exp_exp_tabs : forall n1 A1 e1,
    degree_exp_wrt_exp n1 e1 ->
    degree_exp_wrt_exp n1 (exp_tabs A1 e1)
  | degree_wrt_exp_exp_tapp : forall n1 e1 A1,
    degree_exp_wrt_exp n1 e1 ->
    degree_exp_wrt_exp n1 (exp_tapp e1 A1).

Scheme degree_exp_wrt_typ_ind' := Induction for degree_exp_wrt_typ Sort Prop.

Combined Scheme degree_exp_wrt_typ_mutind from degree_exp_wrt_typ_ind'.

Scheme degree_exp_wrt_exp_ind' := Induction for degree_exp_wrt_exp Sort Prop.

Combined Scheme degree_exp_wrt_exp_mutind from degree_exp_wrt_exp_ind'.

#[export] Hint Constructors degree_exp_wrt_typ : core lngen.

#[export] Hint Constructors degree_exp_wrt_exp : core lngen.

Inductive degree_entry_wrt_typ : nat -> entry -> Prop :=
  | degree_wrt_typ_entry_tvar : forall n1 A1,
    degree_typ_wrt_typ n1 A1 ->
    degree_entry_wrt_typ n1 (entry_tvar A1)
  | degree_wrt_typ_entry_var : forall n1 A1,
    degree_typ_wrt_typ n1 A1 ->
    degree_entry_wrt_typ n1 (entry_var A1).

Scheme degree_entry_wrt_typ_ind' := Induction for degree_entry_wrt_typ Sort Prop.

Combined Scheme degree_entry_wrt_typ_mutind from degree_entry_wrt_typ_ind'.

#[export] Hint Constructors degree_entry_wrt_typ : core lngen.


(* *********************************************************************** *)
(** * Local closure (version in [Set], induction principles) *)

Inductive lc_set_typ : typ -> Set :=
  | lc_set_typ_var_f : forall X1,
    lc_set_typ (typ_var_f X1)
  | lc_set_typ_top :
    lc_set_typ (typ_top)
  | lc_set_typ_arr : forall A1 A2,
    lc_set_typ A1 ->
    lc_set_typ A2 ->
    lc_set_typ (typ_arr A1 A2)
  | lc_set_typ_all : forall B1 A1,
    lc_set_typ B1 ->
    (forall X1 : typvar, lc_set_typ (open_typ_wrt_typ A1 (typ_var_f X1))) ->
    lc_set_typ (typ_all B1 A1).
Scheme lc_typ_ind' := Induction for lc_typ Sort Prop.

Combined Scheme lc_typ_mutind from lc_typ_ind'.

Scheme lc_set_typ_ind' := Induction for lc_set_typ Sort Prop.

Combined Scheme lc_set_typ_mutind from lc_set_typ_ind'.

Scheme lc_set_typ_rec' := Induction for lc_set_typ Sort Set.

Combined Scheme lc_set_typ_mutrec from lc_set_typ_rec'.

#[export] Hint Constructors lc_typ : core lngen.

#[export] Hint Constructors lc_set_typ : core lngen.

Inductive lc_set_exp : exp -> Set :=
  | lc_set_exp_var_f : forall x1,
    lc_set_exp (exp_var_f x1)
  | lc_set_exp_abs : forall A1 e1,
    lc_set_typ A1 ->
    (forall x1 : expvar, lc_set_exp (open_exp_wrt_exp e1 (exp_var_f x1))) ->
    lc_set_exp (exp_abs A1 e1)
  | lc_set_exp_app : forall e1 e2,
    lc_set_exp e1 ->
    lc_set_exp e2 ->
    lc_set_exp (exp_app e1 e2)
  | lc_set_exp_tabs : forall A1 e1,
    lc_set_typ A1 ->
    (forall X1 : typvar, lc_set_exp (open_exp_wrt_typ e1 (typ_var_f X1))) ->
    lc_set_exp (exp_tabs A1 e1)
  | lc_set_exp_tapp : forall e1 A1,
    lc_set_exp e1 ->
    lc_set_typ A1 ->
    lc_set_exp (exp_tapp e1 A1).
Scheme lc_exp_ind' := Induction for lc_exp Sort Prop.

Combined Scheme lc_exp_mutind from lc_exp_ind'.

Scheme lc_set_exp_ind' := Induction for lc_set_exp Sort Prop.

Combined Scheme lc_set_exp_mutind from lc_set_exp_ind'.

Scheme lc_set_exp_rec' := Induction for lc_set_exp Sort Set.

Combined Scheme lc_set_exp_mutrec from lc_set_exp_rec'.

#[export] Hint Constructors lc_exp : core lngen.

#[export] Hint Constructors lc_set_exp : core lngen.

Inductive lc_set_entry : entry -> Set :=
  | lc_set_entry_tvar : forall A1,
    lc_set_typ A1 ->
    lc_set_entry (entry_tvar A1)
  | lc_set_entry_var : forall A1,
    lc_set_typ A1 ->
    lc_set_entry (entry_var A1).
Scheme lc_entry_ind' := Induction for lc_entry Sort Prop.

Combined Scheme lc_entry_mutind from lc_entry_ind'.

Scheme lc_set_entry_ind' := Induction for lc_set_entry Sort Prop.

Combined Scheme lc_set_entry_mutind from lc_set_entry_ind'.

Scheme lc_set_entry_rec' := Induction for lc_set_entry Sort Set.

Combined Scheme lc_set_entry_mutrec from lc_set_entry_rec'.

#[export] Hint Constructors lc_entry : core lngen.

#[export] Hint Constructors lc_set_entry : core lngen.


(* *********************************************************************** *)
(** * Body *)

Definition body_typ_wrt_typ A1 := forall X1, lc_typ (open_typ_wrt_typ A1 (typ_var_f X1)).

#[export] Hint Unfold body_typ_wrt_typ : core.

Definition body_exp_wrt_typ e1 := forall X1, lc_exp (open_exp_wrt_typ e1 (typ_var_f X1)).

Definition body_exp_wrt_exp e1 := forall x1, lc_exp (open_exp_wrt_exp e1 (exp_var_f x1)).

#[export] Hint Unfold body_exp_wrt_typ : core.

#[export] Hint Unfold body_exp_wrt_exp : core.

Definition body_entry_wrt_typ et1 := forall X1, lc_entry (open_entry_wrt_typ et1 (typ_var_f X1)).

#[export] Hint Unfold body_entry_wrt_typ : core.


(* *********************************************************************** *)
(** * Tactic support *)

(** Additional hint declarations. *)

#[export] Hint Resolve Nat.add_le_mono : lngen.

(** Redefine some tactics. *)

Ltac default_case_split ::=
  first
    [ progress destruct_notin
    | progress destruct_sum
    | progress safe_f_equal
    ].


(* *********************************************************************** *)
(** * Theorems about [size] *)

Ltac default_auto ::= auto with arith lngen; tauto.
Ltac default_autorewrite ::= fail.

(* begin hide *)

Lemma size_typ_min_mutual :
(forall A1, 1 <= size_typ A1).
Proof.
apply_mutual_ind typ_mutind;
default_simp.
Qed.

(* end hide *)

Lemma size_typ_min :
forall A1, 1 <= size_typ A1.
Proof.
pose proof size_typ_min_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve size_typ_min : lngen.

(* begin hide *)

Lemma size_exp_min_mutual :
(forall e1, 1 <= size_exp e1).
Proof.
apply_mutual_ind exp_mutind;
default_simp.
Qed.

(* end hide *)

Lemma size_exp_min :
forall e1, 1 <= size_exp e1.
Proof.
pose proof size_exp_min_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve size_exp_min : lngen.

(* begin hide *)

Lemma size_entry_min_mutual :
(forall et1, 1 <= size_entry et1).
Proof.
apply_mutual_ind entry_mutind;
default_simp.
Qed.

(* end hide *)

Lemma size_entry_min :
forall et1, 1 <= size_entry et1.
Proof.
pose proof size_entry_min_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve size_entry_min : lngen.

(* begin hide *)

Lemma size_typ_close_typ_wrt_typ_rec_mutual :
(forall A1 X1 n1,
  size_typ (close_typ_wrt_typ_rec n1 X1 A1) = size_typ A1).
Proof.
apply_mutual_ind typ_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma size_typ_close_typ_wrt_typ_rec :
forall A1 X1 n1,
  size_typ (close_typ_wrt_typ_rec n1 X1 A1) = size_typ A1.
Proof.
pose proof size_typ_close_typ_wrt_typ_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve size_typ_close_typ_wrt_typ_rec : lngen.
#[export] Hint Rewrite size_typ_close_typ_wrt_typ_rec using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma size_exp_close_exp_wrt_typ_rec_mutual :
(forall e1 X1 n1,
  size_exp (close_exp_wrt_typ_rec n1 X1 e1) = size_exp e1).
Proof.
apply_mutual_ind exp_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma size_exp_close_exp_wrt_typ_rec :
forall e1 X1 n1,
  size_exp (close_exp_wrt_typ_rec n1 X1 e1) = size_exp e1.
Proof.
pose proof size_exp_close_exp_wrt_typ_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve size_exp_close_exp_wrt_typ_rec : lngen.
#[export] Hint Rewrite size_exp_close_exp_wrt_typ_rec using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma size_exp_close_exp_wrt_exp_rec_mutual :
(forall e1 x1 n1,
  size_exp (close_exp_wrt_exp_rec n1 x1 e1) = size_exp e1).
Proof.
apply_mutual_ind exp_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma size_exp_close_exp_wrt_exp_rec :
forall e1 x1 n1,
  size_exp (close_exp_wrt_exp_rec n1 x1 e1) = size_exp e1.
Proof.
pose proof size_exp_close_exp_wrt_exp_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve size_exp_close_exp_wrt_exp_rec : lngen.
#[export] Hint Rewrite size_exp_close_exp_wrt_exp_rec using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma size_entry_close_entry_wrt_typ_rec_mutual :
(forall et1 X1 n1,
  size_entry (close_entry_wrt_typ_rec n1 X1 et1) = size_entry et1).
Proof.
apply_mutual_ind entry_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma size_entry_close_entry_wrt_typ_rec :
forall et1 X1 n1,
  size_entry (close_entry_wrt_typ_rec n1 X1 et1) = size_entry et1.
Proof.
pose proof size_entry_close_entry_wrt_typ_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve size_entry_close_entry_wrt_typ_rec : lngen.
#[export] Hint Rewrite size_entry_close_entry_wrt_typ_rec using solve [auto] : lngen.

(* end hide *)

Lemma size_typ_close_typ_wrt_typ :
forall A1 X1,
  size_typ (close_typ_wrt_typ X1 A1) = size_typ A1.
Proof.
unfold close_typ_wrt_typ; default_simp.
Qed.

#[export] Hint Resolve size_typ_close_typ_wrt_typ : lngen.
#[export] Hint Rewrite size_typ_close_typ_wrt_typ using solve [auto] : lngen.

Lemma size_exp_close_exp_wrt_typ :
forall e1 X1,
  size_exp (close_exp_wrt_typ X1 e1) = size_exp e1.
Proof.
unfold close_exp_wrt_typ; default_simp.
Qed.

#[export] Hint Resolve size_exp_close_exp_wrt_typ : lngen.
#[export] Hint Rewrite size_exp_close_exp_wrt_typ using solve [auto] : lngen.

Lemma size_exp_close_exp_wrt_exp :
forall e1 x1,
  size_exp (close_exp_wrt_exp x1 e1) = size_exp e1.
Proof.
unfold close_exp_wrt_exp; default_simp.
Qed.

#[export] Hint Resolve size_exp_close_exp_wrt_exp : lngen.
#[export] Hint Rewrite size_exp_close_exp_wrt_exp using solve [auto] : lngen.

Lemma size_entry_close_entry_wrt_typ :
forall et1 X1,
  size_entry (close_entry_wrt_typ X1 et1) = size_entry et1.
Proof.
unfold close_entry_wrt_typ; default_simp.
Qed.

#[export] Hint Resolve size_entry_close_entry_wrt_typ : lngen.
#[export] Hint Rewrite size_entry_close_entry_wrt_typ using solve [auto] : lngen.

(* begin hide *)

Lemma size_typ_open_typ_wrt_typ_rec_mutual :
(forall A1 A2 n1,
  size_typ A1 <= size_typ (open_typ_wrt_typ_rec n1 A2 A1)).
Proof.
apply_mutual_ind typ_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma size_typ_open_typ_wrt_typ_rec :
forall A1 A2 n1,
  size_typ A1 <= size_typ (open_typ_wrt_typ_rec n1 A2 A1).
Proof.
pose proof size_typ_open_typ_wrt_typ_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve size_typ_open_typ_wrt_typ_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma size_exp_open_exp_wrt_typ_rec_mutual :
(forall e1 A1 n1,
  size_exp e1 <= size_exp (open_exp_wrt_typ_rec n1 A1 e1)).
Proof.
apply_mutual_ind exp_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma size_exp_open_exp_wrt_typ_rec :
forall e1 A1 n1,
  size_exp e1 <= size_exp (open_exp_wrt_typ_rec n1 A1 e1).
Proof.
pose proof size_exp_open_exp_wrt_typ_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve size_exp_open_exp_wrt_typ_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma size_exp_open_exp_wrt_exp_rec_mutual :
(forall e1 e2 n1,
  size_exp e1 <= size_exp (open_exp_wrt_exp_rec n1 e2 e1)).
Proof.
apply_mutual_ind exp_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma size_exp_open_exp_wrt_exp_rec :
forall e1 e2 n1,
  size_exp e1 <= size_exp (open_exp_wrt_exp_rec n1 e2 e1).
Proof.
pose proof size_exp_open_exp_wrt_exp_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve size_exp_open_exp_wrt_exp_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma size_entry_open_entry_wrt_typ_rec_mutual :
(forall et1 A1 n1,
  size_entry et1 <= size_entry (open_entry_wrt_typ_rec n1 A1 et1)).
Proof.
apply_mutual_ind entry_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma size_entry_open_entry_wrt_typ_rec :
forall et1 A1 n1,
  size_entry et1 <= size_entry (open_entry_wrt_typ_rec n1 A1 et1).
Proof.
pose proof size_entry_open_entry_wrt_typ_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve size_entry_open_entry_wrt_typ_rec : lngen.

(* end hide *)

Lemma size_typ_open_typ_wrt_typ :
forall A1 A2,
  size_typ A1 <= size_typ (open_typ_wrt_typ A1 A2).
Proof.
unfold open_typ_wrt_typ; default_simp.
Qed.

#[export] Hint Resolve size_typ_open_typ_wrt_typ : lngen.

Lemma size_exp_open_exp_wrt_typ :
forall e1 A1,
  size_exp e1 <= size_exp (open_exp_wrt_typ e1 A1).
Proof.
unfold open_exp_wrt_typ; default_simp.
Qed.

#[export] Hint Resolve size_exp_open_exp_wrt_typ : lngen.

Lemma size_exp_open_exp_wrt_exp :
forall e1 e2,
  size_exp e1 <= size_exp (open_exp_wrt_exp e1 e2).
Proof.
unfold open_exp_wrt_exp; default_simp.
Qed.

#[export] Hint Resolve size_exp_open_exp_wrt_exp : lngen.

Lemma size_entry_open_entry_wrt_typ :
forall et1 A1,
  size_entry et1 <= size_entry (open_entry_wrt_typ et1 A1).
Proof.
unfold open_entry_wrt_typ; default_simp.
Qed.

#[export] Hint Resolve size_entry_open_entry_wrt_typ : lngen.

(* begin hide *)

Lemma size_typ_open_typ_wrt_typ_rec_var_mutual :
(forall A1 X1 n1,
  size_typ (open_typ_wrt_typ_rec n1 (typ_var_f X1) A1) = size_typ A1).
Proof.
apply_mutual_ind typ_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma size_typ_open_typ_wrt_typ_rec_var :
forall A1 X1 n1,
  size_typ (open_typ_wrt_typ_rec n1 (typ_var_f X1) A1) = size_typ A1.
Proof.
pose proof size_typ_open_typ_wrt_typ_rec_var_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve size_typ_open_typ_wrt_typ_rec_var : lngen.
#[export] Hint Rewrite size_typ_open_typ_wrt_typ_rec_var using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma size_exp_open_exp_wrt_typ_rec_var_mutual :
(forall e1 X1 n1,
  size_exp (open_exp_wrt_typ_rec n1 (typ_var_f X1) e1) = size_exp e1).
Proof.
apply_mutual_ind exp_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma size_exp_open_exp_wrt_typ_rec_var :
forall e1 X1 n1,
  size_exp (open_exp_wrt_typ_rec n1 (typ_var_f X1) e1) = size_exp e1.
Proof.
pose proof size_exp_open_exp_wrt_typ_rec_var_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve size_exp_open_exp_wrt_typ_rec_var : lngen.
#[export] Hint Rewrite size_exp_open_exp_wrt_typ_rec_var using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma size_exp_open_exp_wrt_exp_rec_var_mutual :
(forall e1 x1 n1,
  size_exp (open_exp_wrt_exp_rec n1 (exp_var_f x1) e1) = size_exp e1).
Proof.
apply_mutual_ind exp_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma size_exp_open_exp_wrt_exp_rec_var :
forall e1 x1 n1,
  size_exp (open_exp_wrt_exp_rec n1 (exp_var_f x1) e1) = size_exp e1.
Proof.
pose proof size_exp_open_exp_wrt_exp_rec_var_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve size_exp_open_exp_wrt_exp_rec_var : lngen.
#[export] Hint Rewrite size_exp_open_exp_wrt_exp_rec_var using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma size_entry_open_entry_wrt_typ_rec_var_mutual :
(forall et1 X1 n1,
  size_entry (open_entry_wrt_typ_rec n1 (typ_var_f X1) et1) = size_entry et1).
Proof.
apply_mutual_ind entry_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma size_entry_open_entry_wrt_typ_rec_var :
forall et1 X1 n1,
  size_entry (open_entry_wrt_typ_rec n1 (typ_var_f X1) et1) = size_entry et1.
Proof.
pose proof size_entry_open_entry_wrt_typ_rec_var_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve size_entry_open_entry_wrt_typ_rec_var : lngen.
#[export] Hint Rewrite size_entry_open_entry_wrt_typ_rec_var using solve [auto] : lngen.

(* end hide *)

Lemma size_typ_open_typ_wrt_typ_var :
forall A1 X1,
  size_typ (open_typ_wrt_typ A1 (typ_var_f X1)) = size_typ A1.
Proof.
unfold open_typ_wrt_typ; default_simp.
Qed.

#[export] Hint Resolve size_typ_open_typ_wrt_typ_var : lngen.
#[export] Hint Rewrite size_typ_open_typ_wrt_typ_var using solve [auto] : lngen.

Lemma size_exp_open_exp_wrt_typ_var :
forall e1 X1,
  size_exp (open_exp_wrt_typ e1 (typ_var_f X1)) = size_exp e1.
Proof.
unfold open_exp_wrt_typ; default_simp.
Qed.

#[export] Hint Resolve size_exp_open_exp_wrt_typ_var : lngen.
#[export] Hint Rewrite size_exp_open_exp_wrt_typ_var using solve [auto] : lngen.

Lemma size_exp_open_exp_wrt_exp_var :
forall e1 x1,
  size_exp (open_exp_wrt_exp e1 (exp_var_f x1)) = size_exp e1.
Proof.
unfold open_exp_wrt_exp; default_simp.
Qed.

#[export] Hint Resolve size_exp_open_exp_wrt_exp_var : lngen.
#[export] Hint Rewrite size_exp_open_exp_wrt_exp_var using solve [auto] : lngen.

Lemma size_entry_open_entry_wrt_typ_var :
forall et1 X1,
  size_entry (open_entry_wrt_typ et1 (typ_var_f X1)) = size_entry et1.
Proof.
unfold open_entry_wrt_typ; default_simp.
Qed.

#[export] Hint Resolve size_entry_open_entry_wrt_typ_var : lngen.
#[export] Hint Rewrite size_entry_open_entry_wrt_typ_var using solve [auto] : lngen.


(* *********************************************************************** *)
(** * Theorems about [degree] *)

Ltac default_auto ::= auto with lngen; tauto.
Ltac default_autorewrite ::= fail.

(* begin hide *)

Lemma degree_typ_wrt_typ_S_mutual :
(forall n1 A1,
  degree_typ_wrt_typ n1 A1 ->
  degree_typ_wrt_typ (S n1) A1).
Proof.
apply_mutual_ind degree_typ_wrt_typ_mutind;
default_simp.
Qed.

(* end hide *)

Lemma degree_typ_wrt_typ_S :
forall n1 A1,
  degree_typ_wrt_typ n1 A1 ->
  degree_typ_wrt_typ (S n1) A1.
Proof.
pose proof degree_typ_wrt_typ_S_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve degree_typ_wrt_typ_S : lngen.

(* begin hide *)

Lemma degree_exp_wrt_typ_S_mutual :
(forall n1 e1,
  degree_exp_wrt_typ n1 e1 ->
  degree_exp_wrt_typ (S n1) e1).
Proof.
apply_mutual_ind degree_exp_wrt_typ_mutind;
default_simp.
Qed.

(* end hide *)

Lemma degree_exp_wrt_typ_S :
forall n1 e1,
  degree_exp_wrt_typ n1 e1 ->
  degree_exp_wrt_typ (S n1) e1.
Proof.
pose proof degree_exp_wrt_typ_S_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve degree_exp_wrt_typ_S : lngen.

(* begin hide *)

Lemma degree_exp_wrt_exp_S_mutual :
(forall n1 e1,
  degree_exp_wrt_exp n1 e1 ->
  degree_exp_wrt_exp (S n1) e1).
Proof.
apply_mutual_ind degree_exp_wrt_exp_mutind;
default_simp.
Qed.

(* end hide *)

Lemma degree_exp_wrt_exp_S :
forall n1 e1,
  degree_exp_wrt_exp n1 e1 ->
  degree_exp_wrt_exp (S n1) e1.
Proof.
pose proof degree_exp_wrt_exp_S_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve degree_exp_wrt_exp_S : lngen.

(* begin hide *)

Lemma degree_entry_wrt_typ_S_mutual :
(forall n1 et1,
  degree_entry_wrt_typ n1 et1 ->
  degree_entry_wrt_typ (S n1) et1).
Proof.
apply_mutual_ind degree_entry_wrt_typ_mutind;
default_simp.
Qed.

(* end hide *)

Lemma degree_entry_wrt_typ_S :
forall n1 et1,
  degree_entry_wrt_typ n1 et1 ->
  degree_entry_wrt_typ (S n1) et1.
Proof.
pose proof degree_entry_wrt_typ_S_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve degree_entry_wrt_typ_S : lngen.

Lemma degree_typ_wrt_typ_O :
forall n1 A1,
  degree_typ_wrt_typ O A1 ->
  degree_typ_wrt_typ n1 A1.
Proof.
induction n1; default_simp.
Qed.

#[export] Hint Resolve degree_typ_wrt_typ_O : lngen.

Lemma degree_exp_wrt_typ_O :
forall n1 e1,
  degree_exp_wrt_typ O e1 ->
  degree_exp_wrt_typ n1 e1.
Proof.
induction n1; default_simp.
Qed.

#[export] Hint Resolve degree_exp_wrt_typ_O : lngen.

Lemma degree_exp_wrt_exp_O :
forall n1 e1,
  degree_exp_wrt_exp O e1 ->
  degree_exp_wrt_exp n1 e1.
Proof.
induction n1; default_simp.
Qed.

#[export] Hint Resolve degree_exp_wrt_exp_O : lngen.

Lemma degree_entry_wrt_typ_O :
forall n1 et1,
  degree_entry_wrt_typ O et1 ->
  degree_entry_wrt_typ n1 et1.
Proof.
induction n1; default_simp.
Qed.

#[export] Hint Resolve degree_entry_wrt_typ_O : lngen.

(* begin hide *)

Lemma degree_typ_wrt_typ_close_typ_wrt_typ_rec_mutual :
(forall A1 X1 n1,
  degree_typ_wrt_typ n1 A1 ->
  degree_typ_wrt_typ (S n1) (close_typ_wrt_typ_rec n1 X1 A1)).
Proof.
apply_mutual_ind typ_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma degree_typ_wrt_typ_close_typ_wrt_typ_rec :
forall A1 X1 n1,
  degree_typ_wrt_typ n1 A1 ->
  degree_typ_wrt_typ (S n1) (close_typ_wrt_typ_rec n1 X1 A1).
Proof.
pose proof degree_typ_wrt_typ_close_typ_wrt_typ_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve degree_typ_wrt_typ_close_typ_wrt_typ_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_exp_wrt_typ_close_exp_wrt_typ_rec_mutual :
(forall e1 X1 n1,
  degree_exp_wrt_typ n1 e1 ->
  degree_exp_wrt_typ (S n1) (close_exp_wrt_typ_rec n1 X1 e1)).
Proof.
apply_mutual_ind exp_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma degree_exp_wrt_typ_close_exp_wrt_typ_rec :
forall e1 X1 n1,
  degree_exp_wrt_typ n1 e1 ->
  degree_exp_wrt_typ (S n1) (close_exp_wrt_typ_rec n1 X1 e1).
Proof.
pose proof degree_exp_wrt_typ_close_exp_wrt_typ_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve degree_exp_wrt_typ_close_exp_wrt_typ_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_exp_wrt_typ_close_exp_wrt_exp_rec_mutual :
(forall e1 x1 n1 n2,
  degree_exp_wrt_typ n2 e1 ->
  degree_exp_wrt_typ n2 (close_exp_wrt_exp_rec n1 x1 e1)).
Proof.
apply_mutual_ind exp_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma degree_exp_wrt_typ_close_exp_wrt_exp_rec :
forall e1 x1 n1 n2,
  degree_exp_wrt_typ n2 e1 ->
  degree_exp_wrt_typ n2 (close_exp_wrt_exp_rec n1 x1 e1).
Proof.
pose proof degree_exp_wrt_typ_close_exp_wrt_exp_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve degree_exp_wrt_typ_close_exp_wrt_exp_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_exp_wrt_exp_close_exp_wrt_typ_rec_mutual :
(forall e1 X1 n1 n2,
  degree_exp_wrt_exp n2 e1 ->
  degree_exp_wrt_exp n2 (close_exp_wrt_typ_rec n1 X1 e1)).
Proof.
apply_mutual_ind exp_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma degree_exp_wrt_exp_close_exp_wrt_typ_rec :
forall e1 X1 n1 n2,
  degree_exp_wrt_exp n2 e1 ->
  degree_exp_wrt_exp n2 (close_exp_wrt_typ_rec n1 X1 e1).
Proof.
pose proof degree_exp_wrt_exp_close_exp_wrt_typ_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve degree_exp_wrt_exp_close_exp_wrt_typ_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_exp_wrt_exp_close_exp_wrt_exp_rec_mutual :
(forall e1 x1 n1,
  degree_exp_wrt_exp n1 e1 ->
  degree_exp_wrt_exp (S n1) (close_exp_wrt_exp_rec n1 x1 e1)).
Proof.
apply_mutual_ind exp_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma degree_exp_wrt_exp_close_exp_wrt_exp_rec :
forall e1 x1 n1,
  degree_exp_wrt_exp n1 e1 ->
  degree_exp_wrt_exp (S n1) (close_exp_wrt_exp_rec n1 x1 e1).
Proof.
pose proof degree_exp_wrt_exp_close_exp_wrt_exp_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve degree_exp_wrt_exp_close_exp_wrt_exp_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_entry_wrt_typ_close_entry_wrt_typ_rec_mutual :
(forall et1 X1 n1,
  degree_entry_wrt_typ n1 et1 ->
  degree_entry_wrt_typ (S n1) (close_entry_wrt_typ_rec n1 X1 et1)).
Proof.
apply_mutual_ind entry_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma degree_entry_wrt_typ_close_entry_wrt_typ_rec :
forall et1 X1 n1,
  degree_entry_wrt_typ n1 et1 ->
  degree_entry_wrt_typ (S n1) (close_entry_wrt_typ_rec n1 X1 et1).
Proof.
pose proof degree_entry_wrt_typ_close_entry_wrt_typ_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve degree_entry_wrt_typ_close_entry_wrt_typ_rec : lngen.

(* end hide *)

Lemma degree_typ_wrt_typ_close_typ_wrt_typ :
forall A1 X1,
  degree_typ_wrt_typ 0 A1 ->
  degree_typ_wrt_typ 1 (close_typ_wrt_typ X1 A1).
Proof.
unfold close_typ_wrt_typ; default_simp.
Qed.

#[export] Hint Resolve degree_typ_wrt_typ_close_typ_wrt_typ : lngen.

Lemma degree_exp_wrt_typ_close_exp_wrt_typ :
forall e1 X1,
  degree_exp_wrt_typ 0 e1 ->
  degree_exp_wrt_typ 1 (close_exp_wrt_typ X1 e1).
Proof.
unfold close_exp_wrt_typ; default_simp.
Qed.

#[export] Hint Resolve degree_exp_wrt_typ_close_exp_wrt_typ : lngen.

Lemma degree_exp_wrt_typ_close_exp_wrt_exp :
forall e1 x1 n1,
  degree_exp_wrt_typ n1 e1 ->
  degree_exp_wrt_typ n1 (close_exp_wrt_exp x1 e1).
Proof.
unfold close_exp_wrt_exp; default_simp.
Qed.

#[export] Hint Resolve degree_exp_wrt_typ_close_exp_wrt_exp : lngen.

Lemma degree_exp_wrt_exp_close_exp_wrt_typ :
forall e1 X1 n1,
  degree_exp_wrt_exp n1 e1 ->
  degree_exp_wrt_exp n1 (close_exp_wrt_typ X1 e1).
Proof.
unfold close_exp_wrt_typ; default_simp.
Qed.

#[export] Hint Resolve degree_exp_wrt_exp_close_exp_wrt_typ : lngen.

Lemma degree_exp_wrt_exp_close_exp_wrt_exp :
forall e1 x1,
  degree_exp_wrt_exp 0 e1 ->
  degree_exp_wrt_exp 1 (close_exp_wrt_exp x1 e1).
Proof.
unfold close_exp_wrt_exp; default_simp.
Qed.

#[export] Hint Resolve degree_exp_wrt_exp_close_exp_wrt_exp : lngen.

Lemma degree_entry_wrt_typ_close_entry_wrt_typ :
forall et1 X1,
  degree_entry_wrt_typ 0 et1 ->
  degree_entry_wrt_typ 1 (close_entry_wrt_typ X1 et1).
Proof.
unfold close_entry_wrt_typ; default_simp.
Qed.

#[export] Hint Resolve degree_entry_wrt_typ_close_entry_wrt_typ : lngen.

(* begin hide *)

Lemma degree_typ_wrt_typ_close_typ_wrt_typ_rec_inv_mutual :
(forall A1 X1 n1,
  degree_typ_wrt_typ (S n1) (close_typ_wrt_typ_rec n1 X1 A1) ->
  degree_typ_wrt_typ n1 A1).
Proof.
apply_mutual_ind typ_mutind;
default_simp; eauto with lngen.
Qed.

(* end hide *)

(* begin hide *)

Lemma degree_typ_wrt_typ_close_typ_wrt_typ_rec_inv :
forall A1 X1 n1,
  degree_typ_wrt_typ (S n1) (close_typ_wrt_typ_rec n1 X1 A1) ->
  degree_typ_wrt_typ n1 A1.
Proof.
pose proof degree_typ_wrt_typ_close_typ_wrt_typ_rec_inv_mutual as H; intuition eauto.
Qed.

#[export] Hint Immediate degree_typ_wrt_typ_close_typ_wrt_typ_rec_inv : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_exp_wrt_typ_close_exp_wrt_typ_rec_inv_mutual :
(forall e1 X1 n1,
  degree_exp_wrt_typ (S n1) (close_exp_wrt_typ_rec n1 X1 e1) ->
  degree_exp_wrt_typ n1 e1).
Proof.
apply_mutual_ind exp_mutind;
default_simp; eauto with lngen.
Qed.

(* end hide *)

(* begin hide *)

Lemma degree_exp_wrt_typ_close_exp_wrt_typ_rec_inv :
forall e1 X1 n1,
  degree_exp_wrt_typ (S n1) (close_exp_wrt_typ_rec n1 X1 e1) ->
  degree_exp_wrt_typ n1 e1.
Proof.
pose proof degree_exp_wrt_typ_close_exp_wrt_typ_rec_inv_mutual as H; intuition eauto.
Qed.

#[export] Hint Immediate degree_exp_wrt_typ_close_exp_wrt_typ_rec_inv : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_exp_wrt_typ_close_exp_wrt_exp_rec_inv_mutual :
(forall e1 x1 n1 n2,
  degree_exp_wrt_typ n2 (close_exp_wrt_exp_rec n1 x1 e1) ->
  degree_exp_wrt_typ n2 e1).
Proof.
apply_mutual_ind exp_mutind;
default_simp; eauto with lngen.
Qed.

(* end hide *)

(* begin hide *)

Lemma degree_exp_wrt_typ_close_exp_wrt_exp_rec_inv :
forall e1 x1 n1 n2,
  degree_exp_wrt_typ n2 (close_exp_wrt_exp_rec n1 x1 e1) ->
  degree_exp_wrt_typ n2 e1.
Proof.
pose proof degree_exp_wrt_typ_close_exp_wrt_exp_rec_inv_mutual as H; intuition eauto.
Qed.

#[export] Hint Immediate degree_exp_wrt_typ_close_exp_wrt_exp_rec_inv : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_exp_wrt_exp_close_exp_wrt_typ_rec_inv_mutual :
(forall e1 X1 n1 n2,
  degree_exp_wrt_exp n2 (close_exp_wrt_typ_rec n1 X1 e1) ->
  degree_exp_wrt_exp n2 e1).
Proof.
apply_mutual_ind exp_mutind;
default_simp; eauto with lngen.
Qed.

(* end hide *)

(* begin hide *)

Lemma degree_exp_wrt_exp_close_exp_wrt_typ_rec_inv :
forall e1 X1 n1 n2,
  degree_exp_wrt_exp n2 (close_exp_wrt_typ_rec n1 X1 e1) ->
  degree_exp_wrt_exp n2 e1.
Proof.
pose proof degree_exp_wrt_exp_close_exp_wrt_typ_rec_inv_mutual as H; intuition eauto.
Qed.

#[export] Hint Immediate degree_exp_wrt_exp_close_exp_wrt_typ_rec_inv : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_exp_wrt_exp_close_exp_wrt_exp_rec_inv_mutual :
(forall e1 x1 n1,
  degree_exp_wrt_exp (S n1) (close_exp_wrt_exp_rec n1 x1 e1) ->
  degree_exp_wrt_exp n1 e1).
Proof.
apply_mutual_ind exp_mutind;
default_simp; eauto with lngen.
Qed.

(* end hide *)

(* begin hide *)

Lemma degree_exp_wrt_exp_close_exp_wrt_exp_rec_inv :
forall e1 x1 n1,
  degree_exp_wrt_exp (S n1) (close_exp_wrt_exp_rec n1 x1 e1) ->
  degree_exp_wrt_exp n1 e1.
Proof.
pose proof degree_exp_wrt_exp_close_exp_wrt_exp_rec_inv_mutual as H; intuition eauto.
Qed.

#[export] Hint Immediate degree_exp_wrt_exp_close_exp_wrt_exp_rec_inv : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_entry_wrt_typ_close_entry_wrt_typ_rec_inv_mutual :
(forall et1 X1 n1,
  degree_entry_wrt_typ (S n1) (close_entry_wrt_typ_rec n1 X1 et1) ->
  degree_entry_wrt_typ n1 et1).
Proof.
apply_mutual_ind entry_mutind;
default_simp; eauto with lngen.
Qed.

(* end hide *)

(* begin hide *)

Lemma degree_entry_wrt_typ_close_entry_wrt_typ_rec_inv :
forall et1 X1 n1,
  degree_entry_wrt_typ (S n1) (close_entry_wrt_typ_rec n1 X1 et1) ->
  degree_entry_wrt_typ n1 et1.
Proof.
pose proof degree_entry_wrt_typ_close_entry_wrt_typ_rec_inv_mutual as H; intuition eauto.
Qed.

#[export] Hint Immediate degree_entry_wrt_typ_close_entry_wrt_typ_rec_inv : lngen.

(* end hide *)

Lemma degree_typ_wrt_typ_close_typ_wrt_typ_inv :
forall A1 X1,
  degree_typ_wrt_typ 1 (close_typ_wrt_typ X1 A1) ->
  degree_typ_wrt_typ 0 A1.
Proof.
unfold close_typ_wrt_typ; eauto with lngen.
Qed.

#[export] Hint Immediate degree_typ_wrt_typ_close_typ_wrt_typ_inv : lngen.

Lemma degree_exp_wrt_typ_close_exp_wrt_typ_inv :
forall e1 X1,
  degree_exp_wrt_typ 1 (close_exp_wrt_typ X1 e1) ->
  degree_exp_wrt_typ 0 e1.
Proof.
unfold close_exp_wrt_typ; eauto with lngen.
Qed.

#[export] Hint Immediate degree_exp_wrt_typ_close_exp_wrt_typ_inv : lngen.

Lemma degree_exp_wrt_typ_close_exp_wrt_exp_inv :
forall e1 x1 n1,
  degree_exp_wrt_typ n1 (close_exp_wrt_exp x1 e1) ->
  degree_exp_wrt_typ n1 e1.
Proof.
unfold close_exp_wrt_exp; eauto with lngen.
Qed.

#[export] Hint Immediate degree_exp_wrt_typ_close_exp_wrt_exp_inv : lngen.

Lemma degree_exp_wrt_exp_close_exp_wrt_typ_inv :
forall e1 X1 n1,
  degree_exp_wrt_exp n1 (close_exp_wrt_typ X1 e1) ->
  degree_exp_wrt_exp n1 e1.
Proof.
unfold close_exp_wrt_typ; eauto with lngen.
Qed.

#[export] Hint Immediate degree_exp_wrt_exp_close_exp_wrt_typ_inv : lngen.

Lemma degree_exp_wrt_exp_close_exp_wrt_exp_inv :
forall e1 x1,
  degree_exp_wrt_exp 1 (close_exp_wrt_exp x1 e1) ->
  degree_exp_wrt_exp 0 e1.
Proof.
unfold close_exp_wrt_exp; eauto with lngen.
Qed.

#[export] Hint Immediate degree_exp_wrt_exp_close_exp_wrt_exp_inv : lngen.

Lemma degree_entry_wrt_typ_close_entry_wrt_typ_inv :
forall et1 X1,
  degree_entry_wrt_typ 1 (close_entry_wrt_typ X1 et1) ->
  degree_entry_wrt_typ 0 et1.
Proof.
unfold close_entry_wrt_typ; eauto with lngen.
Qed.

#[export] Hint Immediate degree_entry_wrt_typ_close_entry_wrt_typ_inv : lngen.

(* begin hide *)

Lemma degree_typ_wrt_typ_open_typ_wrt_typ_rec_mutual :
(forall A1 A2 n1,
  degree_typ_wrt_typ (S n1) A1 ->
  degree_typ_wrt_typ n1 A2 ->
  degree_typ_wrt_typ n1 (open_typ_wrt_typ_rec n1 A2 A1)).
Proof.
apply_mutual_ind typ_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma degree_typ_wrt_typ_open_typ_wrt_typ_rec :
forall A1 A2 n1,
  degree_typ_wrt_typ (S n1) A1 ->
  degree_typ_wrt_typ n1 A2 ->
  degree_typ_wrt_typ n1 (open_typ_wrt_typ_rec n1 A2 A1).
Proof.
pose proof degree_typ_wrt_typ_open_typ_wrt_typ_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve degree_typ_wrt_typ_open_typ_wrt_typ_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_exp_wrt_typ_open_exp_wrt_typ_rec_mutual :
(forall e1 A1 n1,
  degree_exp_wrt_typ (S n1) e1 ->
  degree_typ_wrt_typ n1 A1 ->
  degree_exp_wrt_typ n1 (open_exp_wrt_typ_rec n1 A1 e1)).
Proof.
apply_mutual_ind exp_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma degree_exp_wrt_typ_open_exp_wrt_typ_rec :
forall e1 A1 n1,
  degree_exp_wrt_typ (S n1) e1 ->
  degree_typ_wrt_typ n1 A1 ->
  degree_exp_wrt_typ n1 (open_exp_wrt_typ_rec n1 A1 e1).
Proof.
pose proof degree_exp_wrt_typ_open_exp_wrt_typ_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve degree_exp_wrt_typ_open_exp_wrt_typ_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_exp_wrt_typ_open_exp_wrt_exp_rec_mutual :
(forall e1 e2 n1 n2,
  degree_exp_wrt_typ n1 e1 ->
  degree_exp_wrt_typ n1 e2 ->
  degree_exp_wrt_typ n1 (open_exp_wrt_exp_rec n2 e2 e1)).
Proof.
apply_mutual_ind exp_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma degree_exp_wrt_typ_open_exp_wrt_exp_rec :
forall e1 e2 n1 n2,
  degree_exp_wrt_typ n1 e1 ->
  degree_exp_wrt_typ n1 e2 ->
  degree_exp_wrt_typ n1 (open_exp_wrt_exp_rec n2 e2 e1).
Proof.
pose proof degree_exp_wrt_typ_open_exp_wrt_exp_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve degree_exp_wrt_typ_open_exp_wrt_exp_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_exp_wrt_exp_open_exp_wrt_typ_rec_mutual :
(forall e1 A1 n1 n2,
  degree_exp_wrt_exp n1 e1 ->
  degree_exp_wrt_exp n1 (open_exp_wrt_typ_rec n2 A1 e1)).
Proof.
apply_mutual_ind exp_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma degree_exp_wrt_exp_open_exp_wrt_typ_rec :
forall e1 A1 n1 n2,
  degree_exp_wrt_exp n1 e1 ->
  degree_exp_wrt_exp n1 (open_exp_wrt_typ_rec n2 A1 e1).
Proof.
pose proof degree_exp_wrt_exp_open_exp_wrt_typ_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve degree_exp_wrt_exp_open_exp_wrt_typ_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_exp_wrt_exp_open_exp_wrt_exp_rec_mutual :
(forall e1 e2 n1,
  degree_exp_wrt_exp (S n1) e1 ->
  degree_exp_wrt_exp n1 e2 ->
  degree_exp_wrt_exp n1 (open_exp_wrt_exp_rec n1 e2 e1)).
Proof.
apply_mutual_ind exp_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma degree_exp_wrt_exp_open_exp_wrt_exp_rec :
forall e1 e2 n1,
  degree_exp_wrt_exp (S n1) e1 ->
  degree_exp_wrt_exp n1 e2 ->
  degree_exp_wrt_exp n1 (open_exp_wrt_exp_rec n1 e2 e1).
Proof.
pose proof degree_exp_wrt_exp_open_exp_wrt_exp_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve degree_exp_wrt_exp_open_exp_wrt_exp_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_entry_wrt_typ_open_entry_wrt_typ_rec_mutual :
(forall et1 A1 n1,
  degree_entry_wrt_typ (S n1) et1 ->
  degree_typ_wrt_typ n1 A1 ->
  degree_entry_wrt_typ n1 (open_entry_wrt_typ_rec n1 A1 et1)).
Proof.
apply_mutual_ind entry_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma degree_entry_wrt_typ_open_entry_wrt_typ_rec :
forall et1 A1 n1,
  degree_entry_wrt_typ (S n1) et1 ->
  degree_typ_wrt_typ n1 A1 ->
  degree_entry_wrt_typ n1 (open_entry_wrt_typ_rec n1 A1 et1).
Proof.
pose proof degree_entry_wrt_typ_open_entry_wrt_typ_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve degree_entry_wrt_typ_open_entry_wrt_typ_rec : lngen.

(* end hide *)

Lemma degree_typ_wrt_typ_open_typ_wrt_typ :
forall A1 A2,
  degree_typ_wrt_typ 1 A1 ->
  degree_typ_wrt_typ 0 A2 ->
  degree_typ_wrt_typ 0 (open_typ_wrt_typ A1 A2).
Proof.
unfold open_typ_wrt_typ; default_simp.
Qed.

#[export] Hint Resolve degree_typ_wrt_typ_open_typ_wrt_typ : lngen.

Lemma degree_exp_wrt_typ_open_exp_wrt_typ :
forall e1 A1,
  degree_exp_wrt_typ 1 e1 ->
  degree_typ_wrt_typ 0 A1 ->
  degree_exp_wrt_typ 0 (open_exp_wrt_typ e1 A1).
Proof.
unfold open_exp_wrt_typ; default_simp.
Qed.

#[export] Hint Resolve degree_exp_wrt_typ_open_exp_wrt_typ : lngen.

Lemma degree_exp_wrt_typ_open_exp_wrt_exp :
forall e1 e2 n1,
  degree_exp_wrt_typ n1 e1 ->
  degree_exp_wrt_typ n1 e2 ->
  degree_exp_wrt_typ n1 (open_exp_wrt_exp e1 e2).
Proof.
unfold open_exp_wrt_exp; default_simp.
Qed.

#[export] Hint Resolve degree_exp_wrt_typ_open_exp_wrt_exp : lngen.

Lemma degree_exp_wrt_exp_open_exp_wrt_typ :
forall e1 A1 n1,
  degree_exp_wrt_exp n1 e1 ->
  degree_exp_wrt_exp n1 (open_exp_wrt_typ e1 A1).
Proof.
unfold open_exp_wrt_typ; default_simp.
Qed.

#[export] Hint Resolve degree_exp_wrt_exp_open_exp_wrt_typ : lngen.

Lemma degree_exp_wrt_exp_open_exp_wrt_exp :
forall e1 e2,
  degree_exp_wrt_exp 1 e1 ->
  degree_exp_wrt_exp 0 e2 ->
  degree_exp_wrt_exp 0 (open_exp_wrt_exp e1 e2).
Proof.
unfold open_exp_wrt_exp; default_simp.
Qed.

#[export] Hint Resolve degree_exp_wrt_exp_open_exp_wrt_exp : lngen.

Lemma degree_entry_wrt_typ_open_entry_wrt_typ :
forall et1 A1,
  degree_entry_wrt_typ 1 et1 ->
  degree_typ_wrt_typ 0 A1 ->
  degree_entry_wrt_typ 0 (open_entry_wrt_typ et1 A1).
Proof.
unfold open_entry_wrt_typ; default_simp.
Qed.

#[export] Hint Resolve degree_entry_wrt_typ_open_entry_wrt_typ : lngen.

(* begin hide *)

Lemma degree_typ_wrt_typ_open_typ_wrt_typ_rec_inv_mutual :
(forall A1 A2 n1,
  degree_typ_wrt_typ n1 (open_typ_wrt_typ_rec n1 A2 A1) ->
  degree_typ_wrt_typ (S n1) A1).
Proof.
apply_mutual_ind typ_mutind;
default_simp; eauto with lngen.
Qed.

(* end hide *)

(* begin hide *)

Lemma degree_typ_wrt_typ_open_typ_wrt_typ_rec_inv :
forall A1 A2 n1,
  degree_typ_wrt_typ n1 (open_typ_wrt_typ_rec n1 A2 A1) ->
  degree_typ_wrt_typ (S n1) A1.
Proof.
pose proof degree_typ_wrt_typ_open_typ_wrt_typ_rec_inv_mutual as H; intuition eauto.
Qed.

#[export] Hint Immediate degree_typ_wrt_typ_open_typ_wrt_typ_rec_inv : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_exp_wrt_typ_open_exp_wrt_typ_rec_inv_mutual :
(forall e1 A1 n1,
  degree_exp_wrt_typ n1 (open_exp_wrt_typ_rec n1 A1 e1) ->
  degree_exp_wrt_typ (S n1) e1).
Proof.
apply_mutual_ind exp_mutind;
default_simp; eauto with lngen.
Qed.

(* end hide *)

(* begin hide *)

Lemma degree_exp_wrt_typ_open_exp_wrt_typ_rec_inv :
forall e1 A1 n1,
  degree_exp_wrt_typ n1 (open_exp_wrt_typ_rec n1 A1 e1) ->
  degree_exp_wrt_typ (S n1) e1.
Proof.
pose proof degree_exp_wrt_typ_open_exp_wrt_typ_rec_inv_mutual as H; intuition eauto.
Qed.

#[export] Hint Immediate degree_exp_wrt_typ_open_exp_wrt_typ_rec_inv : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_exp_wrt_typ_open_exp_wrt_exp_rec_inv_mutual :
(forall e1 e2 n1 n2,
  degree_exp_wrt_typ n1 (open_exp_wrt_exp_rec n2 e2 e1) ->
  degree_exp_wrt_typ n1 e1).
Proof.
apply_mutual_ind exp_mutind;
default_simp; eauto with lngen.
Qed.

(* end hide *)

(* begin hide *)

Lemma degree_exp_wrt_typ_open_exp_wrt_exp_rec_inv :
forall e1 e2 n1 n2,
  degree_exp_wrt_typ n1 (open_exp_wrt_exp_rec n2 e2 e1) ->
  degree_exp_wrt_typ n1 e1.
Proof.
pose proof degree_exp_wrt_typ_open_exp_wrt_exp_rec_inv_mutual as H; intuition eauto.
Qed.

#[export] Hint Immediate degree_exp_wrt_typ_open_exp_wrt_exp_rec_inv : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_exp_wrt_exp_open_exp_wrt_typ_rec_inv_mutual :
(forall e1 A1 n1 n2,
  degree_exp_wrt_exp n1 (open_exp_wrt_typ_rec n2 A1 e1) ->
  degree_exp_wrt_exp n1 e1).
Proof.
apply_mutual_ind exp_mutind;
default_simp; eauto with lngen.
Qed.

(* end hide *)

(* begin hide *)

Lemma degree_exp_wrt_exp_open_exp_wrt_typ_rec_inv :
forall e1 A1 n1 n2,
  degree_exp_wrt_exp n1 (open_exp_wrt_typ_rec n2 A1 e1) ->
  degree_exp_wrt_exp n1 e1.
Proof.
pose proof degree_exp_wrt_exp_open_exp_wrt_typ_rec_inv_mutual as H; intuition eauto.
Qed.

#[export] Hint Immediate degree_exp_wrt_exp_open_exp_wrt_typ_rec_inv : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_exp_wrt_exp_open_exp_wrt_exp_rec_inv_mutual :
(forall e1 e2 n1,
  degree_exp_wrt_exp n1 (open_exp_wrt_exp_rec n1 e2 e1) ->
  degree_exp_wrt_exp (S n1) e1).
Proof.
apply_mutual_ind exp_mutind;
default_simp; eauto with lngen.
Qed.

(* end hide *)

(* begin hide *)

Lemma degree_exp_wrt_exp_open_exp_wrt_exp_rec_inv :
forall e1 e2 n1,
  degree_exp_wrt_exp n1 (open_exp_wrt_exp_rec n1 e2 e1) ->
  degree_exp_wrt_exp (S n1) e1.
Proof.
pose proof degree_exp_wrt_exp_open_exp_wrt_exp_rec_inv_mutual as H; intuition eauto.
Qed.

#[export] Hint Immediate degree_exp_wrt_exp_open_exp_wrt_exp_rec_inv : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_entry_wrt_typ_open_entry_wrt_typ_rec_inv_mutual :
(forall et1 A1 n1,
  degree_entry_wrt_typ n1 (open_entry_wrt_typ_rec n1 A1 et1) ->
  degree_entry_wrt_typ (S n1) et1).
Proof.
apply_mutual_ind entry_mutind;
default_simp; eauto with lngen.
Qed.

(* end hide *)

(* begin hide *)

Lemma degree_entry_wrt_typ_open_entry_wrt_typ_rec_inv :
forall et1 A1 n1,
  degree_entry_wrt_typ n1 (open_entry_wrt_typ_rec n1 A1 et1) ->
  degree_entry_wrt_typ (S n1) et1.
Proof.
pose proof degree_entry_wrt_typ_open_entry_wrt_typ_rec_inv_mutual as H; intuition eauto.
Qed.

#[export] Hint Immediate degree_entry_wrt_typ_open_entry_wrt_typ_rec_inv : lngen.

(* end hide *)

Lemma degree_typ_wrt_typ_open_typ_wrt_typ_inv :
forall A1 A2,
  degree_typ_wrt_typ 0 (open_typ_wrt_typ A1 A2) ->
  degree_typ_wrt_typ 1 A1.
Proof.
unfold open_typ_wrt_typ; eauto with lngen.
Qed.

#[export] Hint Immediate degree_typ_wrt_typ_open_typ_wrt_typ_inv : lngen.

Lemma degree_exp_wrt_typ_open_exp_wrt_typ_inv :
forall e1 A1,
  degree_exp_wrt_typ 0 (open_exp_wrt_typ e1 A1) ->
  degree_exp_wrt_typ 1 e1.
Proof.
unfold open_exp_wrt_typ; eauto with lngen.
Qed.

#[export] Hint Immediate degree_exp_wrt_typ_open_exp_wrt_typ_inv : lngen.

Lemma degree_exp_wrt_typ_open_exp_wrt_exp_inv :
forall e1 e2 n1,
  degree_exp_wrt_typ n1 (open_exp_wrt_exp e1 e2) ->
  degree_exp_wrt_typ n1 e1.
Proof.
unfold open_exp_wrt_exp; eauto with lngen.
Qed.

#[export] Hint Immediate degree_exp_wrt_typ_open_exp_wrt_exp_inv : lngen.

Lemma degree_exp_wrt_exp_open_exp_wrt_typ_inv :
forall e1 A1 n1,
  degree_exp_wrt_exp n1 (open_exp_wrt_typ e1 A1) ->
  degree_exp_wrt_exp n1 e1.
Proof.
unfold open_exp_wrt_typ; eauto with lngen.
Qed.

#[export] Hint Immediate degree_exp_wrt_exp_open_exp_wrt_typ_inv : lngen.

Lemma degree_exp_wrt_exp_open_exp_wrt_exp_inv :
forall e1 e2,
  degree_exp_wrt_exp 0 (open_exp_wrt_exp e1 e2) ->
  degree_exp_wrt_exp 1 e1.
Proof.
unfold open_exp_wrt_exp; eauto with lngen.
Qed.

#[export] Hint Immediate degree_exp_wrt_exp_open_exp_wrt_exp_inv : lngen.

Lemma degree_entry_wrt_typ_open_entry_wrt_typ_inv :
forall et1 A1,
  degree_entry_wrt_typ 0 (open_entry_wrt_typ et1 A1) ->
  degree_entry_wrt_typ 1 et1.
Proof.
unfold open_entry_wrt_typ; eauto with lngen.
Qed.

#[export] Hint Immediate degree_entry_wrt_typ_open_entry_wrt_typ_inv : lngen.


(* *********************************************************************** *)
(** * Theorems about [open] and [close] *)

Ltac default_auto ::= auto with lngen brute_force; tauto.
Ltac default_autorewrite ::= fail.

(* begin hide *)

Lemma close_typ_wrt_typ_rec_inj_mutual :
(forall A1 A2 X1 n1,
  close_typ_wrt_typ_rec n1 X1 A1 = close_typ_wrt_typ_rec n1 X1 A2 ->
  A1 = A2).
Proof.
apply_mutual_ind typ_mutind;
intros; match goal with
          | |- _ = ?term => destruct term
        end;
default_simp; eauto with lngen.
Qed.

(* end hide *)

(* begin hide *)

Lemma close_typ_wrt_typ_rec_inj :
forall A1 A2 X1 n1,
  close_typ_wrt_typ_rec n1 X1 A1 = close_typ_wrt_typ_rec n1 X1 A2 ->
  A1 = A2.
Proof.
pose proof close_typ_wrt_typ_rec_inj_mutual as H; intuition eauto.
Qed.

#[export] Hint Immediate close_typ_wrt_typ_rec_inj : lngen.

(* end hide *)

(* begin hide *)

Lemma close_exp_wrt_typ_rec_inj_mutual :
(forall e1 e2 X1 n1,
  close_exp_wrt_typ_rec n1 X1 e1 = close_exp_wrt_typ_rec n1 X1 e2 ->
  e1 = e2).
Proof.
apply_mutual_ind exp_mutind;
intros; match goal with
          | |- _ = ?term => destruct term
        end;
default_simp; eauto with lngen.
Qed.

(* end hide *)

(* begin hide *)

Lemma close_exp_wrt_typ_rec_inj :
forall e1 e2 X1 n1,
  close_exp_wrt_typ_rec n1 X1 e1 = close_exp_wrt_typ_rec n1 X1 e2 ->
  e1 = e2.
Proof.
pose proof close_exp_wrt_typ_rec_inj_mutual as H; intuition eauto.
Qed.

#[export] Hint Immediate close_exp_wrt_typ_rec_inj : lngen.

(* end hide *)

(* begin hide *)

Lemma close_exp_wrt_exp_rec_inj_mutual :
(forall e1 e2 x1 n1,
  close_exp_wrt_exp_rec n1 x1 e1 = close_exp_wrt_exp_rec n1 x1 e2 ->
  e1 = e2).
Proof.
apply_mutual_ind exp_mutind;
intros; match goal with
          | |- _ = ?term => destruct term
        end;
default_simp; eauto with lngen.
Qed.

(* end hide *)

(* begin hide *)

Lemma close_exp_wrt_exp_rec_inj :
forall e1 e2 x1 n1,
  close_exp_wrt_exp_rec n1 x1 e1 = close_exp_wrt_exp_rec n1 x1 e2 ->
  e1 = e2.
Proof.
pose proof close_exp_wrt_exp_rec_inj_mutual as H; intuition eauto.
Qed.

#[export] Hint Immediate close_exp_wrt_exp_rec_inj : lngen.

(* end hide *)

(* begin hide *)

Lemma close_entry_wrt_typ_rec_inj_mutual :
(forall et1 et2 X1 n1,
  close_entry_wrt_typ_rec n1 X1 et1 = close_entry_wrt_typ_rec n1 X1 et2 ->
  et1 = et2).
Proof.
apply_mutual_ind entry_mutind;
intros; match goal with
          | |- _ = ?term => destruct term
        end;
default_simp; eauto with lngen.
Qed.

(* end hide *)

(* begin hide *)

Lemma close_entry_wrt_typ_rec_inj :
forall et1 et2 X1 n1,
  close_entry_wrt_typ_rec n1 X1 et1 = close_entry_wrt_typ_rec n1 X1 et2 ->
  et1 = et2.
Proof.
pose proof close_entry_wrt_typ_rec_inj_mutual as H; intuition eauto.
Qed.

#[export] Hint Immediate close_entry_wrt_typ_rec_inj : lngen.

(* end hide *)

Lemma close_typ_wrt_typ_inj :
forall A1 A2 X1,
  close_typ_wrt_typ X1 A1 = close_typ_wrt_typ X1 A2 ->
  A1 = A2.
Proof.
unfold close_typ_wrt_typ; eauto with lngen.
Qed.

#[export] Hint Immediate close_typ_wrt_typ_inj : lngen.

Lemma close_exp_wrt_typ_inj :
forall e1 e2 X1,
  close_exp_wrt_typ X1 e1 = close_exp_wrt_typ X1 e2 ->
  e1 = e2.
Proof.
unfold close_exp_wrt_typ; eauto with lngen.
Qed.

#[export] Hint Immediate close_exp_wrt_typ_inj : lngen.

Lemma close_exp_wrt_exp_inj :
forall e1 e2 x1,
  close_exp_wrt_exp x1 e1 = close_exp_wrt_exp x1 e2 ->
  e1 = e2.
Proof.
unfold close_exp_wrt_exp; eauto with lngen.
Qed.

#[export] Hint Immediate close_exp_wrt_exp_inj : lngen.

Lemma close_entry_wrt_typ_inj :
forall et1 et2 X1,
  close_entry_wrt_typ X1 et1 = close_entry_wrt_typ X1 et2 ->
  et1 = et2.
Proof.
unfold close_entry_wrt_typ; eauto with lngen.
Qed.

#[export] Hint Immediate close_entry_wrt_typ_inj : lngen.

(* begin hide *)

Lemma close_typ_wrt_typ_rec_open_typ_wrt_typ_rec_mutual :
(forall A1 X1 n1,
  X1 `notin` tvar_in_typ A1 ->
  close_typ_wrt_typ_rec n1 X1 (open_typ_wrt_typ_rec n1 (typ_var_f X1) A1) = A1).
Proof.
apply_mutual_ind typ_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma close_typ_wrt_typ_rec_open_typ_wrt_typ_rec :
forall A1 X1 n1,
  X1 `notin` tvar_in_typ A1 ->
  close_typ_wrt_typ_rec n1 X1 (open_typ_wrt_typ_rec n1 (typ_var_f X1) A1) = A1.
Proof.
pose proof close_typ_wrt_typ_rec_open_typ_wrt_typ_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve close_typ_wrt_typ_rec_open_typ_wrt_typ_rec : lngen.
#[export] Hint Rewrite close_typ_wrt_typ_rec_open_typ_wrt_typ_rec using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma close_exp_wrt_typ_rec_open_exp_wrt_typ_rec_mutual :
(forall e1 X1 n1,
  X1 `notin` tvar_in_exp e1 ->
  close_exp_wrt_typ_rec n1 X1 (open_exp_wrt_typ_rec n1 (typ_var_f X1) e1) = e1).
Proof.
apply_mutual_ind exp_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma close_exp_wrt_typ_rec_open_exp_wrt_typ_rec :
forall e1 X1 n1,
  X1 `notin` tvar_in_exp e1 ->
  close_exp_wrt_typ_rec n1 X1 (open_exp_wrt_typ_rec n1 (typ_var_f X1) e1) = e1.
Proof.
pose proof close_exp_wrt_typ_rec_open_exp_wrt_typ_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve close_exp_wrt_typ_rec_open_exp_wrt_typ_rec : lngen.
#[export] Hint Rewrite close_exp_wrt_typ_rec_open_exp_wrt_typ_rec using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma close_exp_wrt_exp_rec_open_exp_wrt_exp_rec_mutual :
(forall e1 x1 n1,
  x1 `notin` var_in_exp e1 ->
  close_exp_wrt_exp_rec n1 x1 (open_exp_wrt_exp_rec n1 (exp_var_f x1) e1) = e1).
Proof.
apply_mutual_ind exp_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma close_exp_wrt_exp_rec_open_exp_wrt_exp_rec :
forall e1 x1 n1,
  x1 `notin` var_in_exp e1 ->
  close_exp_wrt_exp_rec n1 x1 (open_exp_wrt_exp_rec n1 (exp_var_f x1) e1) = e1.
Proof.
pose proof close_exp_wrt_exp_rec_open_exp_wrt_exp_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve close_exp_wrt_exp_rec_open_exp_wrt_exp_rec : lngen.
#[export] Hint Rewrite close_exp_wrt_exp_rec_open_exp_wrt_exp_rec using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma close_entry_wrt_typ_rec_open_entry_wrt_typ_rec_mutual :
(forall et1 X1 n1,
  X1 `notin` tvar_in_entry et1 ->
  close_entry_wrt_typ_rec n1 X1 (open_entry_wrt_typ_rec n1 (typ_var_f X1) et1) = et1).
Proof.
apply_mutual_ind entry_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma close_entry_wrt_typ_rec_open_entry_wrt_typ_rec :
forall et1 X1 n1,
  X1 `notin` tvar_in_entry et1 ->
  close_entry_wrt_typ_rec n1 X1 (open_entry_wrt_typ_rec n1 (typ_var_f X1) et1) = et1.
Proof.
pose proof close_entry_wrt_typ_rec_open_entry_wrt_typ_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve close_entry_wrt_typ_rec_open_entry_wrt_typ_rec : lngen.
#[export] Hint Rewrite close_entry_wrt_typ_rec_open_entry_wrt_typ_rec using solve [auto] : lngen.

(* end hide *)

Lemma close_typ_wrt_typ_open_typ_wrt_typ :
forall A1 X1,
  X1 `notin` tvar_in_typ A1 ->
  close_typ_wrt_typ X1 (open_typ_wrt_typ A1 (typ_var_f X1)) = A1.
Proof.
unfold close_typ_wrt_typ; unfold open_typ_wrt_typ; default_simp.
Qed.

#[export] Hint Resolve close_typ_wrt_typ_open_typ_wrt_typ : lngen.
#[export] Hint Rewrite close_typ_wrt_typ_open_typ_wrt_typ using solve [auto] : lngen.

Lemma close_exp_wrt_typ_open_exp_wrt_typ :
forall e1 X1,
  X1 `notin` tvar_in_exp e1 ->
  close_exp_wrt_typ X1 (open_exp_wrt_typ e1 (typ_var_f X1)) = e1.
Proof.
unfold close_exp_wrt_typ; unfold open_exp_wrt_typ; default_simp.
Qed.

#[export] Hint Resolve close_exp_wrt_typ_open_exp_wrt_typ : lngen.
#[export] Hint Rewrite close_exp_wrt_typ_open_exp_wrt_typ using solve [auto] : lngen.

Lemma close_exp_wrt_exp_open_exp_wrt_exp :
forall e1 x1,
  x1 `notin` var_in_exp e1 ->
  close_exp_wrt_exp x1 (open_exp_wrt_exp e1 (exp_var_f x1)) = e1.
Proof.
unfold close_exp_wrt_exp; unfold open_exp_wrt_exp; default_simp.
Qed.

#[export] Hint Resolve close_exp_wrt_exp_open_exp_wrt_exp : lngen.
#[export] Hint Rewrite close_exp_wrt_exp_open_exp_wrt_exp using solve [auto] : lngen.

Lemma close_entry_wrt_typ_open_entry_wrt_typ :
forall et1 X1,
  X1 `notin` tvar_in_entry et1 ->
  close_entry_wrt_typ X1 (open_entry_wrt_typ et1 (typ_var_f X1)) = et1.
Proof.
unfold close_entry_wrt_typ; unfold open_entry_wrt_typ; default_simp.
Qed.

#[export] Hint Resolve close_entry_wrt_typ_open_entry_wrt_typ : lngen.
#[export] Hint Rewrite close_entry_wrt_typ_open_entry_wrt_typ using solve [auto] : lngen.

(* begin hide *)

Lemma open_typ_wrt_typ_rec_close_typ_wrt_typ_rec_mutual :
(forall A1 X1 n1,
  open_typ_wrt_typ_rec n1 (typ_var_f X1) (close_typ_wrt_typ_rec n1 X1 A1) = A1).
Proof.
apply_mutual_ind typ_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma open_typ_wrt_typ_rec_close_typ_wrt_typ_rec :
forall A1 X1 n1,
  open_typ_wrt_typ_rec n1 (typ_var_f X1) (close_typ_wrt_typ_rec n1 X1 A1) = A1.
Proof.
pose proof open_typ_wrt_typ_rec_close_typ_wrt_typ_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve open_typ_wrt_typ_rec_close_typ_wrt_typ_rec : lngen.
#[export] Hint Rewrite open_typ_wrt_typ_rec_close_typ_wrt_typ_rec using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma open_exp_wrt_typ_rec_close_exp_wrt_typ_rec_mutual :
(forall e1 X1 n1,
  open_exp_wrt_typ_rec n1 (typ_var_f X1) (close_exp_wrt_typ_rec n1 X1 e1) = e1).
Proof.
apply_mutual_ind exp_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma open_exp_wrt_typ_rec_close_exp_wrt_typ_rec :
forall e1 X1 n1,
  open_exp_wrt_typ_rec n1 (typ_var_f X1) (close_exp_wrt_typ_rec n1 X1 e1) = e1.
Proof.
pose proof open_exp_wrt_typ_rec_close_exp_wrt_typ_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve open_exp_wrt_typ_rec_close_exp_wrt_typ_rec : lngen.
#[export] Hint Rewrite open_exp_wrt_typ_rec_close_exp_wrt_typ_rec using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma open_exp_wrt_exp_rec_close_exp_wrt_exp_rec_mutual :
(forall e1 x1 n1,
  open_exp_wrt_exp_rec n1 (exp_var_f x1) (close_exp_wrt_exp_rec n1 x1 e1) = e1).
Proof.
apply_mutual_ind exp_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma open_exp_wrt_exp_rec_close_exp_wrt_exp_rec :
forall e1 x1 n1,
  open_exp_wrt_exp_rec n1 (exp_var_f x1) (close_exp_wrt_exp_rec n1 x1 e1) = e1.
Proof.
pose proof open_exp_wrt_exp_rec_close_exp_wrt_exp_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve open_exp_wrt_exp_rec_close_exp_wrt_exp_rec : lngen.
#[export] Hint Rewrite open_exp_wrt_exp_rec_close_exp_wrt_exp_rec using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma open_entry_wrt_typ_rec_close_entry_wrt_typ_rec_mutual :
(forall et1 X1 n1,
  open_entry_wrt_typ_rec n1 (typ_var_f X1) (close_entry_wrt_typ_rec n1 X1 et1) = et1).
Proof.
apply_mutual_ind entry_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma open_entry_wrt_typ_rec_close_entry_wrt_typ_rec :
forall et1 X1 n1,
  open_entry_wrt_typ_rec n1 (typ_var_f X1) (close_entry_wrt_typ_rec n1 X1 et1) = et1.
Proof.
pose proof open_entry_wrt_typ_rec_close_entry_wrt_typ_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve open_entry_wrt_typ_rec_close_entry_wrt_typ_rec : lngen.
#[export] Hint Rewrite open_entry_wrt_typ_rec_close_entry_wrt_typ_rec using solve [auto] : lngen.

(* end hide *)

Lemma open_typ_wrt_typ_close_typ_wrt_typ :
forall A1 X1,
  open_typ_wrt_typ (close_typ_wrt_typ X1 A1) (typ_var_f X1) = A1.
Proof.
unfold close_typ_wrt_typ; unfold open_typ_wrt_typ; default_simp.
Qed.

#[export] Hint Resolve open_typ_wrt_typ_close_typ_wrt_typ : lngen.
#[export] Hint Rewrite open_typ_wrt_typ_close_typ_wrt_typ using solve [auto] : lngen.

Lemma open_exp_wrt_typ_close_exp_wrt_typ :
forall e1 X1,
  open_exp_wrt_typ (close_exp_wrt_typ X1 e1) (typ_var_f X1) = e1.
Proof.
unfold close_exp_wrt_typ; unfold open_exp_wrt_typ; default_simp.
Qed.

#[export] Hint Resolve open_exp_wrt_typ_close_exp_wrt_typ : lngen.
#[export] Hint Rewrite open_exp_wrt_typ_close_exp_wrt_typ using solve [auto] : lngen.

Lemma open_exp_wrt_exp_close_exp_wrt_exp :
forall e1 x1,
  open_exp_wrt_exp (close_exp_wrt_exp x1 e1) (exp_var_f x1) = e1.
Proof.
unfold close_exp_wrt_exp; unfold open_exp_wrt_exp; default_simp.
Qed.

#[export] Hint Resolve open_exp_wrt_exp_close_exp_wrt_exp : lngen.
#[export] Hint Rewrite open_exp_wrt_exp_close_exp_wrt_exp using solve [auto] : lngen.

Lemma open_entry_wrt_typ_close_entry_wrt_typ :
forall et1 X1,
  open_entry_wrt_typ (close_entry_wrt_typ X1 et1) (typ_var_f X1) = et1.
Proof.
unfold close_entry_wrt_typ; unfold open_entry_wrt_typ; default_simp.
Qed.

#[export] Hint Resolve open_entry_wrt_typ_close_entry_wrt_typ : lngen.
#[export] Hint Rewrite open_entry_wrt_typ_close_entry_wrt_typ using solve [auto] : lngen.

(* begin hide *)

Lemma open_typ_wrt_typ_rec_inj_mutual :
(forall A2 A1 X1 n1,
  X1 `notin` tvar_in_typ A2 ->
  X1 `notin` tvar_in_typ A1 ->
  open_typ_wrt_typ_rec n1 (typ_var_f X1) A2 = open_typ_wrt_typ_rec n1 (typ_var_f X1) A1 ->
  A2 = A1).
Proof.
apply_mutual_ind typ_mutind;
intros; match goal with
          | |- _ = ?term => destruct term
        end;
default_simp; eauto with lngen.
Qed.

(* end hide *)

(* begin hide *)

Lemma open_typ_wrt_typ_rec_inj :
forall A2 A1 X1 n1,
  X1 `notin` tvar_in_typ A2 ->
  X1 `notin` tvar_in_typ A1 ->
  open_typ_wrt_typ_rec n1 (typ_var_f X1) A2 = open_typ_wrt_typ_rec n1 (typ_var_f X1) A1 ->
  A2 = A1.
Proof.
pose proof open_typ_wrt_typ_rec_inj_mutual as H; intuition eauto.
Qed.

#[export] Hint Immediate open_typ_wrt_typ_rec_inj : lngen.

(* end hide *)

(* begin hide *)

Lemma open_exp_wrt_typ_rec_inj_mutual :
(forall e2 e1 X1 n1,
  X1 `notin` tvar_in_exp e2 ->
  X1 `notin` tvar_in_exp e1 ->
  open_exp_wrt_typ_rec n1 (typ_var_f X1) e2 = open_exp_wrt_typ_rec n1 (typ_var_f X1) e1 ->
  e2 = e1).
Proof.
apply_mutual_ind exp_mutind;
intros; match goal with
          | |- _ = ?term => destruct term
        end;
default_simp; eauto with lngen.
Qed.

(* end hide *)

(* begin hide *)

Lemma open_exp_wrt_typ_rec_inj :
forall e2 e1 X1 n1,
  X1 `notin` tvar_in_exp e2 ->
  X1 `notin` tvar_in_exp e1 ->
  open_exp_wrt_typ_rec n1 (typ_var_f X1) e2 = open_exp_wrt_typ_rec n1 (typ_var_f X1) e1 ->
  e2 = e1.
Proof.
pose proof open_exp_wrt_typ_rec_inj_mutual as H; intuition eauto.
Qed.

#[export] Hint Immediate open_exp_wrt_typ_rec_inj : lngen.

(* end hide *)

(* begin hide *)

Lemma open_exp_wrt_exp_rec_inj_mutual :
(forall e2 e1 x1 n1,
  x1 `notin` var_in_exp e2 ->
  x1 `notin` var_in_exp e1 ->
  open_exp_wrt_exp_rec n1 (exp_var_f x1) e2 = open_exp_wrt_exp_rec n1 (exp_var_f x1) e1 ->
  e2 = e1).
Proof.
apply_mutual_ind exp_mutind;
intros; match goal with
          | |- _ = ?term => destruct term
        end;
default_simp; eauto with lngen.
Qed.

(* end hide *)

(* begin hide *)

Lemma open_exp_wrt_exp_rec_inj :
forall e2 e1 x1 n1,
  x1 `notin` var_in_exp e2 ->
  x1 `notin` var_in_exp e1 ->
  open_exp_wrt_exp_rec n1 (exp_var_f x1) e2 = open_exp_wrt_exp_rec n1 (exp_var_f x1) e1 ->
  e2 = e1.
Proof.
pose proof open_exp_wrt_exp_rec_inj_mutual as H; intuition eauto.
Qed.

#[export] Hint Immediate open_exp_wrt_exp_rec_inj : lngen.

(* end hide *)

(* begin hide *)

Lemma open_entry_wrt_typ_rec_inj_mutual :
(forall et2 et1 X1 n1,
  X1 `notin` tvar_in_entry et2 ->
  X1 `notin` tvar_in_entry et1 ->
  open_entry_wrt_typ_rec n1 (typ_var_f X1) et2 = open_entry_wrt_typ_rec n1 (typ_var_f X1) et1 ->
  et2 = et1).
Proof.
apply_mutual_ind entry_mutind;
intros; match goal with
          | |- _ = ?term => destruct term
        end;
default_simp; eauto with lngen.
Qed.

(* end hide *)

(* begin hide *)

Lemma open_entry_wrt_typ_rec_inj :
forall et2 et1 X1 n1,
  X1 `notin` tvar_in_entry et2 ->
  X1 `notin` tvar_in_entry et1 ->
  open_entry_wrt_typ_rec n1 (typ_var_f X1) et2 = open_entry_wrt_typ_rec n1 (typ_var_f X1) et1 ->
  et2 = et1.
Proof.
pose proof open_entry_wrt_typ_rec_inj_mutual as H; intuition eauto.
Qed.

#[export] Hint Immediate open_entry_wrt_typ_rec_inj : lngen.

(* end hide *)

Lemma open_typ_wrt_typ_inj :
forall A2 A1 X1,
  X1 `notin` tvar_in_typ A2 ->
  X1 `notin` tvar_in_typ A1 ->
  open_typ_wrt_typ A2 (typ_var_f X1) = open_typ_wrt_typ A1 (typ_var_f X1) ->
  A2 = A1.
Proof.
unfold open_typ_wrt_typ; eauto with lngen.
Qed.

#[export] Hint Immediate open_typ_wrt_typ_inj : lngen.

Lemma open_exp_wrt_typ_inj :
forall e2 e1 X1,
  X1 `notin` tvar_in_exp e2 ->
  X1 `notin` tvar_in_exp e1 ->
  open_exp_wrt_typ e2 (typ_var_f X1) = open_exp_wrt_typ e1 (typ_var_f X1) ->
  e2 = e1.
Proof.
unfold open_exp_wrt_typ; eauto with lngen.
Qed.

#[export] Hint Immediate open_exp_wrt_typ_inj : lngen.

Lemma open_exp_wrt_exp_inj :
forall e2 e1 x1,
  x1 `notin` var_in_exp e2 ->
  x1 `notin` var_in_exp e1 ->
  open_exp_wrt_exp e2 (exp_var_f x1) = open_exp_wrt_exp e1 (exp_var_f x1) ->
  e2 = e1.
Proof.
unfold open_exp_wrt_exp; eauto with lngen.
Qed.

#[export] Hint Immediate open_exp_wrt_exp_inj : lngen.

Lemma open_entry_wrt_typ_inj :
forall et2 et1 X1,
  X1 `notin` tvar_in_entry et2 ->
  X1 `notin` tvar_in_entry et1 ->
  open_entry_wrt_typ et2 (typ_var_f X1) = open_entry_wrt_typ et1 (typ_var_f X1) ->
  et2 = et1.
Proof.
unfold open_entry_wrt_typ; eauto with lngen.
Qed.

#[export] Hint Immediate open_entry_wrt_typ_inj : lngen.


(* *********************************************************************** *)
(** * Theorems about [lc] *)

Ltac default_auto ::= auto with lngen brute_force; tauto.
Ltac default_autorewrite ::= autorewrite with lngen.

(* begin hide *)

Lemma degree_typ_wrt_typ_of_lc_typ_mutual :
(forall A1,
  lc_typ A1 ->
  degree_typ_wrt_typ 0 A1).
Proof.
apply_mutual_ind lc_typ_mutind;
intros;
let X1 := fresh "X1" in pick_fresh X1;
repeat (match goal with
          | H1 : _, H2 : _ |- _ => specialize H1 with H2
        end);
default_simp; eauto with lngen.
Qed.

(* end hide *)

Lemma degree_typ_wrt_typ_of_lc_typ :
forall A1,
  lc_typ A1 ->
  degree_typ_wrt_typ 0 A1.
Proof.
pose proof degree_typ_wrt_typ_of_lc_typ_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve degree_typ_wrt_typ_of_lc_typ : lngen.

(* begin hide *)

Lemma degree_exp_wrt_typ_of_lc_exp_mutual :
(forall e1,
  lc_exp e1 ->
  degree_exp_wrt_typ 0 e1).
Proof.
apply_mutual_ind lc_exp_mutind;
intros;
let X1 := fresh "X1" in pick_fresh X1;
let x1 := fresh "x1" in pick_fresh x1;
repeat (match goal with
          | H1 : _, H2 : _ |- _ => specialize H1 with H2
        end);
default_simp; eauto with lngen.
Qed.

(* end hide *)

Lemma degree_exp_wrt_typ_of_lc_exp :
forall e1,
  lc_exp e1 ->
  degree_exp_wrt_typ 0 e1.
Proof.
pose proof degree_exp_wrt_typ_of_lc_exp_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve degree_exp_wrt_typ_of_lc_exp : lngen.

(* begin hide *)

Lemma degree_exp_wrt_exp_of_lc_exp_mutual :
(forall e1,
  lc_exp e1 ->
  degree_exp_wrt_exp 0 e1).
Proof.
apply_mutual_ind lc_exp_mutind;
intros;
let X1 := fresh "X1" in pick_fresh X1;
let x1 := fresh "x1" in pick_fresh x1;
repeat (match goal with
          | H1 : _, H2 : _ |- _ => specialize H1 with H2
        end);
default_simp; eauto with lngen.
Qed.

(* end hide *)

Lemma degree_exp_wrt_exp_of_lc_exp :
forall e1,
  lc_exp e1 ->
  degree_exp_wrt_exp 0 e1.
Proof.
pose proof degree_exp_wrt_exp_of_lc_exp_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve degree_exp_wrt_exp_of_lc_exp : lngen.

(* begin hide *)

Lemma degree_entry_wrt_typ_of_lc_entry_mutual :
(forall et1,
  lc_entry et1 ->
  degree_entry_wrt_typ 0 et1).
Proof.
apply_mutual_ind lc_entry_mutind;
intros;
let X1 := fresh "X1" in pick_fresh X1;
repeat (match goal with
          | H1 : _, H2 : _ |- _ => specialize H1 with H2
        end);
default_simp; eauto with lngen.
Qed.

(* end hide *)

Lemma degree_entry_wrt_typ_of_lc_entry :
forall et1,
  lc_entry et1 ->
  degree_entry_wrt_typ 0 et1.
Proof.
pose proof degree_entry_wrt_typ_of_lc_entry_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve degree_entry_wrt_typ_of_lc_entry : lngen.

(* begin hide *)

Lemma lc_typ_of_degree_size_mutual :
forall i1,
(forall A1,
  size_typ A1 = i1 ->
  degree_typ_wrt_typ 0 A1 ->
  lc_typ A1).
Proof.
intros i1; pattern i1; apply lt_wf_rec;
clear i1; intros i1 H1;
apply_mutual_ind typ_mutind;
default_simp;
(* non-trivial cases *)
constructor; default_simp; eapply_first_lt_hyp;
(* instantiate the size *)
match goal with
  | |- _ = _ => reflexivity
  | _ => idtac
end;
(* everything should be easy now *)
default_simp.
Qed.

(* end hide *)

Lemma lc_typ_of_degree :
forall A1,
  degree_typ_wrt_typ 0 A1 ->
  lc_typ A1.
Proof.
intros A1; intros;
pose proof (lc_typ_of_degree_size_mutual (size_typ A1));
intuition eauto.
Qed.

#[export] Hint Resolve lc_typ_of_degree : lngen.

(* begin hide *)

Lemma lc_exp_of_degree_size_mutual :
forall i1,
(forall e1,
  size_exp e1 = i1 ->
  degree_exp_wrt_typ 0 e1 ->
  degree_exp_wrt_exp 0 e1 ->
  lc_exp e1).
Proof.
intros i1; pattern i1; apply lt_wf_rec;
clear i1; intros i1 H1;
apply_mutual_ind exp_mutind;
default_simp;
(* non-trivial cases *)
constructor; default_simp; eapply_first_lt_hyp;
(* instantiate the size *)
match goal with
  | |- _ = _ => reflexivity
  | _ => idtac
end;
(* everything should be easy now *)
default_simp.
Qed.

(* end hide *)

Lemma lc_exp_of_degree :
forall e1,
  degree_exp_wrt_typ 0 e1 ->
  degree_exp_wrt_exp 0 e1 ->
  lc_exp e1.
Proof.
intros e1; intros;
pose proof (lc_exp_of_degree_size_mutual (size_exp e1));
intuition eauto.
Qed.

#[export] Hint Resolve lc_exp_of_degree : lngen.

(* begin hide *)

Lemma lc_entry_of_degree_size_mutual :
forall i1,
(forall et1,
  size_entry et1 = i1 ->
  degree_entry_wrt_typ 0 et1 ->
  lc_entry et1).
Proof.
intros i1; pattern i1; apply lt_wf_rec;
clear i1; intros i1 H1;
apply_mutual_ind entry_mutind;
default_simp;
(* non-trivial cases *)
constructor; default_simp; eapply_first_lt_hyp;
(* instantiate the size *)
match goal with
  | |- _ = _ => reflexivity
  | _ => idtac
end;
(* everything should be easy now *)
default_simp.
Qed.

(* end hide *)

Lemma lc_entry_of_degree :
forall et1,
  degree_entry_wrt_typ 0 et1 ->
  lc_entry et1.
Proof.
intros et1; intros;
pose proof (lc_entry_of_degree_size_mutual (size_entry et1));
intuition eauto.
Qed.

#[export] Hint Resolve lc_entry_of_degree : lngen.

Ltac typ_lc_exists_tac :=
  repeat (match goal with
            | H : _ |- _ =>
              let J1 := fresh in pose proof H as J1; apply degree_typ_wrt_typ_of_lc_typ in J1; clear H
          end).

Ltac exp_lc_exists_tac :=
  repeat (match goal with
            | H : _ |- _ =>
              let J1 := fresh in pose proof H as J1; apply degree_exp_wrt_typ_of_lc_exp in J1;
              let J2 := fresh in pose proof H as J2; apply degree_exp_wrt_exp_of_lc_exp in J2; clear H
          end).

Ltac entry_lc_exists_tac :=
  repeat (match goal with
            | H : _ |- _ =>
              let J1 := fresh in pose proof H as J1; apply degree_entry_wrt_typ_of_lc_entry in J1; clear H
          end).

Lemma lc_typ_all_exists :
forall X1 B1 A1,
  lc_typ B1 ->
  lc_typ (open_typ_wrt_typ A1 (typ_var_f X1)) ->
  lc_typ (typ_all B1 A1).
Proof.
intros; typ_lc_exists_tac; eauto 6 with lngen.
Qed.

Lemma lc_exp_abs_exists :
forall x1 A1 e1,
  lc_typ A1 ->
  lc_exp (open_exp_wrt_exp e1 (exp_var_f x1)) ->
  lc_exp (exp_abs A1 e1).
Proof.
intros; exp_lc_exists_tac; eauto 6 with lngen.
Qed.

Lemma lc_exp_tabs_exists :
forall X1 A1 e1,
  lc_typ A1 ->
  lc_exp (open_exp_wrt_typ e1 (typ_var_f X1)) ->
  lc_exp (exp_tabs A1 e1).
Proof.
intros; exp_lc_exists_tac; eauto 6 with lngen.
Qed.

#[export] Hint Extern 1 (lc_typ (typ_all _ _)) =>
  let X1 := fresh in
  pick_fresh X1;
  apply (lc_typ_all_exists X1) : core.

#[export] Hint Extern 1 (lc_exp (exp_abs _ _)) =>
  let x1 := fresh in
  pick_fresh x1;
  apply (lc_exp_abs_exists x1) : core.

#[export] Hint Extern 1 (lc_exp (exp_tabs _ _)) =>
  let X1 := fresh in
  pick_fresh X1;
  apply (lc_exp_tabs_exists X1) : core.

Lemma lc_body_typ_wrt_typ :
forall A1 A2,
  body_typ_wrt_typ A1 ->
  lc_typ A2 ->
  lc_typ (open_typ_wrt_typ A1 A2).
Proof.
unfold body_typ_wrt_typ;
default_simp;
let X1 := fresh "x" in
pick_fresh X1;
specialize_all X1;
typ_lc_exists_tac;
eauto 7 with lngen.
Qed.

#[export] Hint Resolve lc_body_typ_wrt_typ : lngen.

Lemma lc_body_exp_wrt_typ :
forall e1 A1,
  body_exp_wrt_typ e1 ->
  lc_typ A1 ->
  lc_exp (open_exp_wrt_typ e1 A1).
Proof.
unfold body_exp_wrt_typ;
default_simp;
let X1 := fresh "x" in
pick_fresh X1;
specialize_all X1;
exp_lc_exists_tac;
eauto 7 with lngen.
Qed.

#[export] Hint Resolve lc_body_exp_wrt_typ : lngen.

Lemma lc_body_exp_wrt_exp :
forall e1 e2,
  body_exp_wrt_exp e1 ->
  lc_exp e2 ->
  lc_exp (open_exp_wrt_exp e1 e2).
Proof.
unfold body_exp_wrt_exp;
default_simp;
let x1 := fresh "x" in
pick_fresh x1;
specialize_all x1;
exp_lc_exists_tac;
eauto 7 with lngen.
Qed.

#[export] Hint Resolve lc_body_exp_wrt_exp : lngen.

Lemma lc_body_entry_wrt_typ :
forall et1 A1,
  body_entry_wrt_typ et1 ->
  lc_typ A1 ->
  lc_entry (open_entry_wrt_typ et1 A1).
Proof.
unfold body_entry_wrt_typ;
default_simp;
let X1 := fresh "x" in
pick_fresh X1;
specialize_all X1;
entry_lc_exists_tac;
eauto 7 with lngen.
Qed.

#[export] Hint Resolve lc_body_entry_wrt_typ : lngen.

Lemma lc_body_typ_all_2 :
forall B1 A1,
  lc_typ (typ_all B1 A1) ->
  body_typ_wrt_typ A1.
Proof.
default_simp.
Qed.

#[export] Hint Resolve lc_body_typ_all_2 : lngen.

Lemma lc_body_exp_abs_2 :
forall A1 e1,
  lc_exp (exp_abs A1 e1) ->
  body_exp_wrt_exp e1.
Proof.
default_simp.
Qed.

#[export] Hint Resolve lc_body_exp_abs_2 : lngen.

Lemma lc_body_exp_tabs_2 :
forall A1 e1,
  lc_exp (exp_tabs A1 e1) ->
  body_exp_wrt_typ e1.
Proof.
default_simp.
Qed.

#[export] Hint Resolve lc_body_exp_tabs_2 : lngen.

(* begin hide *)

Lemma lc_typ_unique_mutual :
(forall A1 (proof2 proof3 : lc_typ A1), proof2 = proof3).
Proof.
apply_mutual_ind lc_typ_mutind;
intros;
let proof1 := fresh "proof1" in
rename_last_into proof1; dependent destruction proof1;
f_equal; default_simp; auto using @functional_extensionality_dep with lngen.
Qed.

(* end hide *)

Lemma lc_typ_unique :
forall A1 (proof2 proof3 : lc_typ A1), proof2 = proof3.
Proof.
pose proof lc_typ_unique_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve lc_typ_unique : lngen.

(* begin hide *)

Lemma lc_exp_unique_mutual :
(forall e1 (proof2 proof3 : lc_exp e1), proof2 = proof3).
Proof.
apply_mutual_ind lc_exp_mutind;
intros;
let proof1 := fresh "proof1" in
rename_last_into proof1; dependent destruction proof1;
f_equal; default_simp; auto using @functional_extensionality_dep with lngen.
Qed.

(* end hide *)

Lemma lc_exp_unique :
forall e1 (proof2 proof3 : lc_exp e1), proof2 = proof3.
Proof.
pose proof lc_exp_unique_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve lc_exp_unique : lngen.

(* begin hide *)

Lemma lc_entry_unique_mutual :
(forall et1 (proof2 proof3 : lc_entry et1), proof2 = proof3).
Proof.
apply_mutual_ind lc_entry_mutind;
intros;
let proof1 := fresh "proof1" in
rename_last_into proof1; dependent destruction proof1;
f_equal; default_simp; auto using @functional_extensionality_dep with lngen.
Qed.

(* end hide *)

Lemma lc_entry_unique :
forall et1 (proof2 proof3 : lc_entry et1), proof2 = proof3.
Proof.
pose proof lc_entry_unique_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve lc_entry_unique : lngen.

(* begin hide *)

Lemma lc_typ_of_lc_set_typ_mutual :
(forall A1, lc_set_typ A1 -> lc_typ A1).
Proof.
apply_mutual_ind lc_set_typ_mutind;
default_simp.
Qed.

(* end hide *)

Lemma lc_typ_of_lc_set_typ :
forall A1, lc_set_typ A1 -> lc_typ A1.
Proof.
pose proof lc_typ_of_lc_set_typ_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve lc_typ_of_lc_set_typ : lngen.

(* begin hide *)

Lemma lc_exp_of_lc_set_exp_mutual :
(forall e1, lc_set_exp e1 -> lc_exp e1).
Proof.
apply_mutual_ind lc_set_exp_mutind;
default_simp.
Qed.

(* end hide *)

Lemma lc_exp_of_lc_set_exp :
forall e1, lc_set_exp e1 -> lc_exp e1.
Proof.
pose proof lc_exp_of_lc_set_exp_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve lc_exp_of_lc_set_exp : lngen.

(* begin hide *)

Lemma lc_entry_of_lc_set_entry_mutual :
(forall et1, lc_set_entry et1 -> lc_entry et1).
Proof.
apply_mutual_ind lc_set_entry_mutind;
default_simp.
Qed.

(* end hide *)

Lemma lc_entry_of_lc_set_entry :
forall et1, lc_set_entry et1 -> lc_entry et1.
Proof.
pose proof lc_entry_of_lc_set_entry_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve lc_entry_of_lc_set_entry : lngen.

(* begin hide *)

Lemma lc_set_typ_of_lc_typ_size_mutual :
forall i1,
(forall A1,
  size_typ A1 = i1 ->
  lc_typ A1 ->
  lc_set_typ A1).
Proof.
intros i1; pattern i1; apply lt_wf_rec;
clear i1; intros i1 H1;
apply_mutual_ind typ_mutrec;
default_simp;
try solve [assert False by default_simp; tauto];
(* non-trivial cases *)
constructor; default_simp;
try first [apply lc_set_typ_of_lc_typ];
default_simp; eapply_first_lt_hyp;
(* instantiate the size *)
match goal with
  | |- _ = _ => reflexivity
  | _ => idtac
end;
(* everything should be easy now *)
default_simp.
Qed.

(* end hide *)

Lemma lc_set_typ_of_lc_typ :
forall A1,
  lc_typ A1 ->
  lc_set_typ A1.
Proof.
intros A1; intros;
pose proof (lc_set_typ_of_lc_typ_size_mutual (size_typ A1));
intuition eauto.
Qed.

#[export] Hint Resolve lc_set_typ_of_lc_typ : lngen.

(* begin hide *)

Lemma lc_set_exp_of_lc_exp_size_mutual :
forall i1,
(forall e1,
  size_exp e1 = i1 ->
  lc_exp e1 ->
  lc_set_exp e1).
Proof.
intros i1; pattern i1; apply lt_wf_rec;
clear i1; intros i1 H1;
apply_mutual_ind exp_mutrec;
default_simp;
try solve [assert False by default_simp; tauto];
(* non-trivial cases *)
constructor; default_simp;
try first [apply lc_set_typ_of_lc_typ
 | apply lc_set_exp_of_lc_exp];
default_simp; eapply_first_lt_hyp;
(* instantiate the size *)
match goal with
  | |- _ = _ => reflexivity
  | _ => idtac
end;
(* everything should be easy now *)
default_simp.
Qed.

(* end hide *)

Lemma lc_set_exp_of_lc_exp :
forall e1,
  lc_exp e1 ->
  lc_set_exp e1.
Proof.
intros e1; intros;
pose proof (lc_set_exp_of_lc_exp_size_mutual (size_exp e1));
intuition eauto.
Qed.

#[export] Hint Resolve lc_set_exp_of_lc_exp : lngen.

(* begin hide *)

Lemma lc_set_entry_of_lc_entry_size_mutual :
forall i1,
(forall et1,
  size_entry et1 = i1 ->
  lc_entry et1 ->
  lc_set_entry et1).
Proof.
intros i1; pattern i1; apply lt_wf_rec;
clear i1; intros i1 H1;
apply_mutual_ind entry_mutrec;
default_simp;
try solve [assert False by default_simp; tauto];
(* non-trivial cases *)
constructor; default_simp;
try first [apply lc_set_typ_of_lc_typ
 | apply lc_set_entry_of_lc_entry];
default_simp; eapply_first_lt_hyp;
(* instantiate the size *)
match goal with
  | |- _ = _ => reflexivity
  | _ => idtac
end;
(* everything should be easy now *)
default_simp.
Qed.

(* end hide *)

Lemma lc_set_entry_of_lc_entry :
forall et1,
  lc_entry et1 ->
  lc_set_entry et1.
Proof.
intros et1; intros;
pose proof (lc_set_entry_of_lc_entry_size_mutual (size_entry et1));
intuition eauto.
Qed.

#[export] Hint Resolve lc_set_entry_of_lc_entry : lngen.


(* *********************************************************************** *)
(** * More theorems about [open] and [close] *)

Ltac default_auto ::= auto with lngen; tauto.
Ltac default_autorewrite ::= fail.

(* begin hide *)

Lemma close_typ_wrt_typ_rec_degree_typ_wrt_typ_mutual :
(forall A1 X1 n1,
  degree_typ_wrt_typ n1 A1 ->
  X1 `notin` tvar_in_typ A1 ->
  close_typ_wrt_typ_rec n1 X1 A1 = A1).
Proof.
apply_mutual_ind typ_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma close_typ_wrt_typ_rec_degree_typ_wrt_typ :
forall A1 X1 n1,
  degree_typ_wrt_typ n1 A1 ->
  X1 `notin` tvar_in_typ A1 ->
  close_typ_wrt_typ_rec n1 X1 A1 = A1.
Proof.
pose proof close_typ_wrt_typ_rec_degree_typ_wrt_typ_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve close_typ_wrt_typ_rec_degree_typ_wrt_typ : lngen.
#[export] Hint Rewrite close_typ_wrt_typ_rec_degree_typ_wrt_typ using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma close_exp_wrt_typ_rec_degree_exp_wrt_typ_mutual :
(forall e1 X1 n1,
  degree_exp_wrt_typ n1 e1 ->
  X1 `notin` tvar_in_exp e1 ->
  close_exp_wrt_typ_rec n1 X1 e1 = e1).
Proof.
apply_mutual_ind exp_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma close_exp_wrt_typ_rec_degree_exp_wrt_typ :
forall e1 X1 n1,
  degree_exp_wrt_typ n1 e1 ->
  X1 `notin` tvar_in_exp e1 ->
  close_exp_wrt_typ_rec n1 X1 e1 = e1.
Proof.
pose proof close_exp_wrt_typ_rec_degree_exp_wrt_typ_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve close_exp_wrt_typ_rec_degree_exp_wrt_typ : lngen.
#[export] Hint Rewrite close_exp_wrt_typ_rec_degree_exp_wrt_typ using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma close_exp_wrt_exp_rec_degree_exp_wrt_exp_mutual :
(forall e1 x1 n1,
  degree_exp_wrt_exp n1 e1 ->
  x1 `notin` var_in_exp e1 ->
  close_exp_wrt_exp_rec n1 x1 e1 = e1).
Proof.
apply_mutual_ind exp_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma close_exp_wrt_exp_rec_degree_exp_wrt_exp :
forall e1 x1 n1,
  degree_exp_wrt_exp n1 e1 ->
  x1 `notin` var_in_exp e1 ->
  close_exp_wrt_exp_rec n1 x1 e1 = e1.
Proof.
pose proof close_exp_wrt_exp_rec_degree_exp_wrt_exp_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve close_exp_wrt_exp_rec_degree_exp_wrt_exp : lngen.
#[export] Hint Rewrite close_exp_wrt_exp_rec_degree_exp_wrt_exp using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma close_entry_wrt_typ_rec_degree_entry_wrt_typ_mutual :
(forall et1 X1 n1,
  degree_entry_wrt_typ n1 et1 ->
  X1 `notin` tvar_in_entry et1 ->
  close_entry_wrt_typ_rec n1 X1 et1 = et1).
Proof.
apply_mutual_ind entry_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma close_entry_wrt_typ_rec_degree_entry_wrt_typ :
forall et1 X1 n1,
  degree_entry_wrt_typ n1 et1 ->
  X1 `notin` tvar_in_entry et1 ->
  close_entry_wrt_typ_rec n1 X1 et1 = et1.
Proof.
pose proof close_entry_wrt_typ_rec_degree_entry_wrt_typ_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve close_entry_wrt_typ_rec_degree_entry_wrt_typ : lngen.
#[export] Hint Rewrite close_entry_wrt_typ_rec_degree_entry_wrt_typ using solve [auto] : lngen.

(* end hide *)

Lemma close_typ_wrt_typ_lc_typ :
forall A1 X1,
  lc_typ A1 ->
  X1 `notin` tvar_in_typ A1 ->
  close_typ_wrt_typ X1 A1 = A1.
Proof.
unfold close_typ_wrt_typ; default_simp.
Qed.

#[export] Hint Resolve close_typ_wrt_typ_lc_typ : lngen.
#[export] Hint Rewrite close_typ_wrt_typ_lc_typ using solve [auto] : lngen.

Lemma close_exp_wrt_typ_lc_exp :
forall e1 X1,
  lc_exp e1 ->
  X1 `notin` tvar_in_exp e1 ->
  close_exp_wrt_typ X1 e1 = e1.
Proof.
unfold close_exp_wrt_typ; default_simp.
Qed.

#[export] Hint Resolve close_exp_wrt_typ_lc_exp : lngen.
#[export] Hint Rewrite close_exp_wrt_typ_lc_exp using solve [auto] : lngen.

Lemma close_exp_wrt_exp_lc_exp :
forall e1 x1,
  lc_exp e1 ->
  x1 `notin` var_in_exp e1 ->
  close_exp_wrt_exp x1 e1 = e1.
Proof.
unfold close_exp_wrt_exp; default_simp.
Qed.

#[export] Hint Resolve close_exp_wrt_exp_lc_exp : lngen.
#[export] Hint Rewrite close_exp_wrt_exp_lc_exp using solve [auto] : lngen.

Lemma close_entry_wrt_typ_lc_entry :
forall et1 X1,
  lc_entry et1 ->
  X1 `notin` tvar_in_entry et1 ->
  close_entry_wrt_typ X1 et1 = et1.
Proof.
unfold close_entry_wrt_typ; default_simp.
Qed.

#[export] Hint Resolve close_entry_wrt_typ_lc_entry : lngen.
#[export] Hint Rewrite close_entry_wrt_typ_lc_entry using solve [auto] : lngen.

(* begin hide *)

Lemma open_typ_wrt_typ_rec_degree_typ_wrt_typ_mutual :
(forall A2 A1 n1,
  degree_typ_wrt_typ n1 A2 ->
  open_typ_wrt_typ_rec n1 A1 A2 = A2).
Proof.
apply_mutual_ind typ_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma open_typ_wrt_typ_rec_degree_typ_wrt_typ :
forall A2 A1 n1,
  degree_typ_wrt_typ n1 A2 ->
  open_typ_wrt_typ_rec n1 A1 A2 = A2.
Proof.
pose proof open_typ_wrt_typ_rec_degree_typ_wrt_typ_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve open_typ_wrt_typ_rec_degree_typ_wrt_typ : lngen.
#[export] Hint Rewrite open_typ_wrt_typ_rec_degree_typ_wrt_typ using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma open_exp_wrt_typ_rec_degree_exp_wrt_typ_mutual :
(forall e1 A1 n1,
  degree_exp_wrt_typ n1 e1 ->
  open_exp_wrt_typ_rec n1 A1 e1 = e1).
Proof.
apply_mutual_ind exp_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma open_exp_wrt_typ_rec_degree_exp_wrt_typ :
forall e1 A1 n1,
  degree_exp_wrt_typ n1 e1 ->
  open_exp_wrt_typ_rec n1 A1 e1 = e1.
Proof.
pose proof open_exp_wrt_typ_rec_degree_exp_wrt_typ_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve open_exp_wrt_typ_rec_degree_exp_wrt_typ : lngen.
#[export] Hint Rewrite open_exp_wrt_typ_rec_degree_exp_wrt_typ using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma open_exp_wrt_exp_rec_degree_exp_wrt_exp_mutual :
(forall e2 e1 n1,
  degree_exp_wrt_exp n1 e2 ->
  open_exp_wrt_exp_rec n1 e1 e2 = e2).
Proof.
apply_mutual_ind exp_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma open_exp_wrt_exp_rec_degree_exp_wrt_exp :
forall e2 e1 n1,
  degree_exp_wrt_exp n1 e2 ->
  open_exp_wrt_exp_rec n1 e1 e2 = e2.
Proof.
pose proof open_exp_wrt_exp_rec_degree_exp_wrt_exp_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve open_exp_wrt_exp_rec_degree_exp_wrt_exp : lngen.
#[export] Hint Rewrite open_exp_wrt_exp_rec_degree_exp_wrt_exp using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma open_entry_wrt_typ_rec_degree_entry_wrt_typ_mutual :
(forall et1 A1 n1,
  degree_entry_wrt_typ n1 et1 ->
  open_entry_wrt_typ_rec n1 A1 et1 = et1).
Proof.
apply_mutual_ind entry_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma open_entry_wrt_typ_rec_degree_entry_wrt_typ :
forall et1 A1 n1,
  degree_entry_wrt_typ n1 et1 ->
  open_entry_wrt_typ_rec n1 A1 et1 = et1.
Proof.
pose proof open_entry_wrt_typ_rec_degree_entry_wrt_typ_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve open_entry_wrt_typ_rec_degree_entry_wrt_typ : lngen.
#[export] Hint Rewrite open_entry_wrt_typ_rec_degree_entry_wrt_typ using solve [auto] : lngen.

(* end hide *)

Lemma open_typ_wrt_typ_lc_typ :
forall A2 A1,
  lc_typ A2 ->
  open_typ_wrt_typ A2 A1 = A2.
Proof.
unfold open_typ_wrt_typ; default_simp.
Qed.

#[export] Hint Resolve open_typ_wrt_typ_lc_typ : lngen.
#[export] Hint Rewrite open_typ_wrt_typ_lc_typ using solve [auto] : lngen.

Lemma open_exp_wrt_typ_lc_exp :
forall e1 A1,
  lc_exp e1 ->
  open_exp_wrt_typ e1 A1 = e1.
Proof.
unfold open_exp_wrt_typ; default_simp.
Qed.

#[export] Hint Resolve open_exp_wrt_typ_lc_exp : lngen.
#[export] Hint Rewrite open_exp_wrt_typ_lc_exp using solve [auto] : lngen.

Lemma open_exp_wrt_exp_lc_exp :
forall e2 e1,
  lc_exp e2 ->
  open_exp_wrt_exp e2 e1 = e2.
Proof.
unfold open_exp_wrt_exp; default_simp.
Qed.

#[export] Hint Resolve open_exp_wrt_exp_lc_exp : lngen.
#[export] Hint Rewrite open_exp_wrt_exp_lc_exp using solve [auto] : lngen.

Lemma open_entry_wrt_typ_lc_entry :
forall et1 A1,
  lc_entry et1 ->
  open_entry_wrt_typ et1 A1 = et1.
Proof.
unfold open_entry_wrt_typ; default_simp.
Qed.

#[export] Hint Resolve open_entry_wrt_typ_lc_entry : lngen.
#[export] Hint Rewrite open_entry_wrt_typ_lc_entry using solve [auto] : lngen.


(* *********************************************************************** *)
(** * Theorems about [fv] *)

Ltac default_auto ::= auto with set lngen; tauto.
Ltac default_autorewrite ::= autorewrite with lngen.

(* begin hide *)

Lemma tvar_in_typ_close_typ_wrt_typ_rec_mutual :
(forall A1 X1 n1,
  tvar_in_typ (close_typ_wrt_typ_rec n1 X1 A1) [=] remove X1 (tvar_in_typ A1)).
Proof.
apply_mutual_ind typ_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

(* begin hide *)

Lemma tvar_in_typ_close_typ_wrt_typ_rec :
forall A1 X1 n1,
  tvar_in_typ (close_typ_wrt_typ_rec n1 X1 A1) [=] remove X1 (tvar_in_typ A1).
Proof.
pose proof tvar_in_typ_close_typ_wrt_typ_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve tvar_in_typ_close_typ_wrt_typ_rec : lngen.
#[export] Hint Rewrite tvar_in_typ_close_typ_wrt_typ_rec using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma tvar_in_exp_close_exp_wrt_typ_rec_mutual :
(forall e1 X1 n1,
  tvar_in_exp (close_exp_wrt_typ_rec n1 X1 e1) [=] remove X1 (tvar_in_exp e1)).
Proof.
apply_mutual_ind exp_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

(* begin hide *)

Lemma tvar_in_exp_close_exp_wrt_typ_rec :
forall e1 X1 n1,
  tvar_in_exp (close_exp_wrt_typ_rec n1 X1 e1) [=] remove X1 (tvar_in_exp e1).
Proof.
pose proof tvar_in_exp_close_exp_wrt_typ_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve tvar_in_exp_close_exp_wrt_typ_rec : lngen.
#[export] Hint Rewrite tvar_in_exp_close_exp_wrt_typ_rec using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma tvar_in_exp_close_exp_wrt_exp_rec_mutual :
(forall e1 x1 n1,
  tvar_in_exp (close_exp_wrt_exp_rec n1 x1 e1) [=] tvar_in_exp e1).
Proof.
apply_mutual_ind exp_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

(* begin hide *)

Lemma tvar_in_exp_close_exp_wrt_exp_rec :
forall e1 x1 n1,
  tvar_in_exp (close_exp_wrt_exp_rec n1 x1 e1) [=] tvar_in_exp e1.
Proof.
pose proof tvar_in_exp_close_exp_wrt_exp_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve tvar_in_exp_close_exp_wrt_exp_rec : lngen.
#[export] Hint Rewrite tvar_in_exp_close_exp_wrt_exp_rec using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma var_in_exp_close_exp_wrt_typ_rec_mutual :
(forall e1 X1 n1,
  var_in_exp (close_exp_wrt_typ_rec n1 X1 e1) [=] var_in_exp e1).
Proof.
apply_mutual_ind exp_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

(* begin hide *)

Lemma var_in_exp_close_exp_wrt_typ_rec :
forall e1 X1 n1,
  var_in_exp (close_exp_wrt_typ_rec n1 X1 e1) [=] var_in_exp e1.
Proof.
pose proof var_in_exp_close_exp_wrt_typ_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve var_in_exp_close_exp_wrt_typ_rec : lngen.
#[export] Hint Rewrite var_in_exp_close_exp_wrt_typ_rec using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma var_in_exp_close_exp_wrt_exp_rec_mutual :
(forall e1 x1 n1,
  var_in_exp (close_exp_wrt_exp_rec n1 x1 e1) [=] remove x1 (var_in_exp e1)).
Proof.
apply_mutual_ind exp_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

(* begin hide *)

Lemma var_in_exp_close_exp_wrt_exp_rec :
forall e1 x1 n1,
  var_in_exp (close_exp_wrt_exp_rec n1 x1 e1) [=] remove x1 (var_in_exp e1).
Proof.
pose proof var_in_exp_close_exp_wrt_exp_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve var_in_exp_close_exp_wrt_exp_rec : lngen.
#[export] Hint Rewrite var_in_exp_close_exp_wrt_exp_rec using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma tvar_in_entry_close_entry_wrt_typ_rec_mutual :
(forall et1 X1 n1,
  tvar_in_entry (close_entry_wrt_typ_rec n1 X1 et1) [=] remove X1 (tvar_in_entry et1)).
Proof.
apply_mutual_ind entry_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

(* begin hide *)

Lemma tvar_in_entry_close_entry_wrt_typ_rec :
forall et1 X1 n1,
  tvar_in_entry (close_entry_wrt_typ_rec n1 X1 et1) [=] remove X1 (tvar_in_entry et1).
Proof.
pose proof tvar_in_entry_close_entry_wrt_typ_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve tvar_in_entry_close_entry_wrt_typ_rec : lngen.
#[export] Hint Rewrite tvar_in_entry_close_entry_wrt_typ_rec using solve [auto] : lngen.

(* end hide *)

Lemma tvar_in_typ_close_typ_wrt_typ :
forall A1 X1,
  tvar_in_typ (close_typ_wrt_typ X1 A1) [=] remove X1 (tvar_in_typ A1).
Proof.
unfold close_typ_wrt_typ; default_simp.
Qed.

#[export] Hint Resolve tvar_in_typ_close_typ_wrt_typ : lngen.
#[export] Hint Rewrite tvar_in_typ_close_typ_wrt_typ using solve [auto] : lngen.

Lemma tvar_in_exp_close_exp_wrt_typ :
forall e1 X1,
  tvar_in_exp (close_exp_wrt_typ X1 e1) [=] remove X1 (tvar_in_exp e1).
Proof.
unfold close_exp_wrt_typ; default_simp.
Qed.

#[export] Hint Resolve tvar_in_exp_close_exp_wrt_typ : lngen.
#[export] Hint Rewrite tvar_in_exp_close_exp_wrt_typ using solve [auto] : lngen.

Lemma tvar_in_exp_close_exp_wrt_exp :
forall e1 x1,
  tvar_in_exp (close_exp_wrt_exp x1 e1) [=] tvar_in_exp e1.
Proof.
unfold close_exp_wrt_exp; default_simp.
Qed.

#[export] Hint Resolve tvar_in_exp_close_exp_wrt_exp : lngen.
#[export] Hint Rewrite tvar_in_exp_close_exp_wrt_exp using solve [auto] : lngen.

Lemma var_in_exp_close_exp_wrt_typ :
forall e1 X1,
  var_in_exp (close_exp_wrt_typ X1 e1) [=] var_in_exp e1.
Proof.
unfold close_exp_wrt_typ; default_simp.
Qed.

#[export] Hint Resolve var_in_exp_close_exp_wrt_typ : lngen.
#[export] Hint Rewrite var_in_exp_close_exp_wrt_typ using solve [auto] : lngen.

Lemma var_in_exp_close_exp_wrt_exp :
forall e1 x1,
  var_in_exp (close_exp_wrt_exp x1 e1) [=] remove x1 (var_in_exp e1).
Proof.
unfold close_exp_wrt_exp; default_simp.
Qed.

#[export] Hint Resolve var_in_exp_close_exp_wrt_exp : lngen.
#[export] Hint Rewrite var_in_exp_close_exp_wrt_exp using solve [auto] : lngen.

Lemma tvar_in_entry_close_entry_wrt_typ :
forall et1 X1,
  tvar_in_entry (close_entry_wrt_typ X1 et1) [=] remove X1 (tvar_in_entry et1).
Proof.
unfold close_entry_wrt_typ; default_simp.
Qed.

#[export] Hint Resolve tvar_in_entry_close_entry_wrt_typ : lngen.
#[export] Hint Rewrite tvar_in_entry_close_entry_wrt_typ using solve [auto] : lngen.

(* begin hide *)

Lemma tvar_in_typ_open_typ_wrt_typ_rec_lower_mutual :
(forall A1 A2 n1,
  tvar_in_typ A1 [<=] tvar_in_typ (open_typ_wrt_typ_rec n1 A2 A1)).
Proof.
apply_mutual_ind typ_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

(* begin hide *)

Lemma tvar_in_typ_open_typ_wrt_typ_rec_lower :
forall A1 A2 n1,
  tvar_in_typ A1 [<=] tvar_in_typ (open_typ_wrt_typ_rec n1 A2 A1).
Proof.
pose proof tvar_in_typ_open_typ_wrt_typ_rec_lower_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve tvar_in_typ_open_typ_wrt_typ_rec_lower : lngen.

(* end hide *)

(* begin hide *)

Lemma tvar_in_exp_open_exp_wrt_typ_rec_lower_mutual :
(forall e1 A1 n1,
  tvar_in_exp e1 [<=] tvar_in_exp (open_exp_wrt_typ_rec n1 A1 e1)).
Proof.
apply_mutual_ind exp_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

(* begin hide *)

Lemma tvar_in_exp_open_exp_wrt_typ_rec_lower :
forall e1 A1 n1,
  tvar_in_exp e1 [<=] tvar_in_exp (open_exp_wrt_typ_rec n1 A1 e1).
Proof.
pose proof tvar_in_exp_open_exp_wrt_typ_rec_lower_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve tvar_in_exp_open_exp_wrt_typ_rec_lower : lngen.

(* end hide *)

(* begin hide *)

Lemma tvar_in_exp_open_exp_wrt_exp_rec_lower_mutual :
(forall e1 e2 n1,
  tvar_in_exp e1 [<=] tvar_in_exp (open_exp_wrt_exp_rec n1 e2 e1)).
Proof.
apply_mutual_ind exp_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

(* begin hide *)

Lemma tvar_in_exp_open_exp_wrt_exp_rec_lower :
forall e1 e2 n1,
  tvar_in_exp e1 [<=] tvar_in_exp (open_exp_wrt_exp_rec n1 e2 e1).
Proof.
pose proof tvar_in_exp_open_exp_wrt_exp_rec_lower_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve tvar_in_exp_open_exp_wrt_exp_rec_lower : lngen.

(* end hide *)

(* begin hide *)

Lemma var_in_exp_open_exp_wrt_typ_rec_lower_mutual :
(forall e1 A1 n1,
  var_in_exp e1 [<=] var_in_exp (open_exp_wrt_typ_rec n1 A1 e1)).
Proof.
apply_mutual_ind exp_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

(* begin hide *)

Lemma var_in_exp_open_exp_wrt_typ_rec_lower :
forall e1 A1 n1,
  var_in_exp e1 [<=] var_in_exp (open_exp_wrt_typ_rec n1 A1 e1).
Proof.
pose proof var_in_exp_open_exp_wrt_typ_rec_lower_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve var_in_exp_open_exp_wrt_typ_rec_lower : lngen.

(* end hide *)

(* begin hide *)

Lemma var_in_exp_open_exp_wrt_exp_rec_lower_mutual :
(forall e1 e2 n1,
  var_in_exp e1 [<=] var_in_exp (open_exp_wrt_exp_rec n1 e2 e1)).
Proof.
apply_mutual_ind exp_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

(* begin hide *)

Lemma var_in_exp_open_exp_wrt_exp_rec_lower :
forall e1 e2 n1,
  var_in_exp e1 [<=] var_in_exp (open_exp_wrt_exp_rec n1 e2 e1).
Proof.
pose proof var_in_exp_open_exp_wrt_exp_rec_lower_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve var_in_exp_open_exp_wrt_exp_rec_lower : lngen.

(* end hide *)

(* begin hide *)

Lemma tvar_in_entry_open_entry_wrt_typ_rec_lower_mutual :
(forall et1 A1 n1,
  tvar_in_entry et1 [<=] tvar_in_entry (open_entry_wrt_typ_rec n1 A1 et1)).
Proof.
apply_mutual_ind entry_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

(* begin hide *)

Lemma tvar_in_entry_open_entry_wrt_typ_rec_lower :
forall et1 A1 n1,
  tvar_in_entry et1 [<=] tvar_in_entry (open_entry_wrt_typ_rec n1 A1 et1).
Proof.
pose proof tvar_in_entry_open_entry_wrt_typ_rec_lower_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve tvar_in_entry_open_entry_wrt_typ_rec_lower : lngen.

(* end hide *)

Lemma tvar_in_typ_open_typ_wrt_typ_lower :
forall A1 A2,
  tvar_in_typ A1 [<=] tvar_in_typ (open_typ_wrt_typ A1 A2).
Proof.
unfold open_typ_wrt_typ; default_simp.
Qed.

#[export] Hint Resolve tvar_in_typ_open_typ_wrt_typ_lower : lngen.

Lemma tvar_in_exp_open_exp_wrt_typ_lower :
forall e1 A1,
  tvar_in_exp e1 [<=] tvar_in_exp (open_exp_wrt_typ e1 A1).
Proof.
unfold open_exp_wrt_typ; default_simp.
Qed.

#[export] Hint Resolve tvar_in_exp_open_exp_wrt_typ_lower : lngen.

Lemma tvar_in_exp_open_exp_wrt_exp_lower :
forall e1 e2,
  tvar_in_exp e1 [<=] tvar_in_exp (open_exp_wrt_exp e1 e2).
Proof.
unfold open_exp_wrt_exp; default_simp.
Qed.

#[export] Hint Resolve tvar_in_exp_open_exp_wrt_exp_lower : lngen.

Lemma var_in_exp_open_exp_wrt_typ_lower :
forall e1 A1,
  var_in_exp e1 [<=] var_in_exp (open_exp_wrt_typ e1 A1).
Proof.
unfold open_exp_wrt_typ; default_simp.
Qed.

#[export] Hint Resolve var_in_exp_open_exp_wrt_typ_lower : lngen.

Lemma var_in_exp_open_exp_wrt_exp_lower :
forall e1 e2,
  var_in_exp e1 [<=] var_in_exp (open_exp_wrt_exp e1 e2).
Proof.
unfold open_exp_wrt_exp; default_simp.
Qed.

#[export] Hint Resolve var_in_exp_open_exp_wrt_exp_lower : lngen.

Lemma tvar_in_entry_open_entry_wrt_typ_lower :
forall et1 A1,
  tvar_in_entry et1 [<=] tvar_in_entry (open_entry_wrt_typ et1 A1).
Proof.
unfold open_entry_wrt_typ; default_simp.
Qed.

#[export] Hint Resolve tvar_in_entry_open_entry_wrt_typ_lower : lngen.

(* begin hide *)

Lemma tvar_in_typ_open_typ_wrt_typ_rec_upper_mutual :
(forall A1 A2 n1,
  tvar_in_typ (open_typ_wrt_typ_rec n1 A2 A1) [<=] tvar_in_typ A2 `union` tvar_in_typ A1).
Proof.
apply_mutual_ind typ_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

(* begin hide *)

Lemma tvar_in_typ_open_typ_wrt_typ_rec_upper :
forall A1 A2 n1,
  tvar_in_typ (open_typ_wrt_typ_rec n1 A2 A1) [<=] tvar_in_typ A2 `union` tvar_in_typ A1.
Proof.
pose proof tvar_in_typ_open_typ_wrt_typ_rec_upper_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve tvar_in_typ_open_typ_wrt_typ_rec_upper : lngen.

(* end hide *)

(* begin hide *)

Lemma tvar_in_exp_open_exp_wrt_typ_rec_upper_mutual :
(forall e1 A1 n1,
  tvar_in_exp (open_exp_wrt_typ_rec n1 A1 e1) [<=] tvar_in_typ A1 `union` tvar_in_exp e1).
Proof.
apply_mutual_ind exp_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

(* begin hide *)

Lemma tvar_in_exp_open_exp_wrt_typ_rec_upper :
forall e1 A1 n1,
  tvar_in_exp (open_exp_wrt_typ_rec n1 A1 e1) [<=] tvar_in_typ A1 `union` tvar_in_exp e1.
Proof.
pose proof tvar_in_exp_open_exp_wrt_typ_rec_upper_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve tvar_in_exp_open_exp_wrt_typ_rec_upper : lngen.

(* end hide *)

(* begin hide *)

Lemma tvar_in_exp_open_exp_wrt_exp_rec_upper_mutual :
(forall e1 e2 n1,
  tvar_in_exp (open_exp_wrt_exp_rec n1 e2 e1) [<=] tvar_in_exp e2 `union` tvar_in_exp e1).
Proof.
apply_mutual_ind exp_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

(* begin hide *)

Lemma tvar_in_exp_open_exp_wrt_exp_rec_upper :
forall e1 e2 n1,
  tvar_in_exp (open_exp_wrt_exp_rec n1 e2 e1) [<=] tvar_in_exp e2 `union` tvar_in_exp e1.
Proof.
pose proof tvar_in_exp_open_exp_wrt_exp_rec_upper_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve tvar_in_exp_open_exp_wrt_exp_rec_upper : lngen.

(* end hide *)

(* begin hide *)

Lemma var_in_exp_open_exp_wrt_typ_rec_upper_mutual :
(forall e1 A1 n1,
  var_in_exp (open_exp_wrt_typ_rec n1 A1 e1) [<=] var_in_exp e1).
Proof.
apply_mutual_ind exp_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

(* begin hide *)

Lemma var_in_exp_open_exp_wrt_typ_rec_upper :
forall e1 A1 n1,
  var_in_exp (open_exp_wrt_typ_rec n1 A1 e1) [<=] var_in_exp e1.
Proof.
pose proof var_in_exp_open_exp_wrt_typ_rec_upper_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve var_in_exp_open_exp_wrt_typ_rec_upper : lngen.

(* end hide *)

(* begin hide *)

Lemma var_in_exp_open_exp_wrt_exp_rec_upper_mutual :
(forall e1 e2 n1,
  var_in_exp (open_exp_wrt_exp_rec n1 e2 e1) [<=] var_in_exp e2 `union` var_in_exp e1).
Proof.
apply_mutual_ind exp_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

(* begin hide *)

Lemma var_in_exp_open_exp_wrt_exp_rec_upper :
forall e1 e2 n1,
  var_in_exp (open_exp_wrt_exp_rec n1 e2 e1) [<=] var_in_exp e2 `union` var_in_exp e1.
Proof.
pose proof var_in_exp_open_exp_wrt_exp_rec_upper_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve var_in_exp_open_exp_wrt_exp_rec_upper : lngen.

(* end hide *)

(* begin hide *)

Lemma tvar_in_entry_open_entry_wrt_typ_rec_upper_mutual :
(forall et1 A1 n1,
  tvar_in_entry (open_entry_wrt_typ_rec n1 A1 et1) [<=] tvar_in_typ A1 `union` tvar_in_entry et1).
Proof.
apply_mutual_ind entry_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

(* begin hide *)

Lemma tvar_in_entry_open_entry_wrt_typ_rec_upper :
forall et1 A1 n1,
  tvar_in_entry (open_entry_wrt_typ_rec n1 A1 et1) [<=] tvar_in_typ A1 `union` tvar_in_entry et1.
Proof.
pose proof tvar_in_entry_open_entry_wrt_typ_rec_upper_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve tvar_in_entry_open_entry_wrt_typ_rec_upper : lngen.

(* end hide *)

Lemma tvar_in_typ_open_typ_wrt_typ_upper :
forall A1 A2,
  tvar_in_typ (open_typ_wrt_typ A1 A2) [<=] tvar_in_typ A2 `union` tvar_in_typ A1.
Proof.
unfold open_typ_wrt_typ; default_simp.
Qed.

#[export] Hint Resolve tvar_in_typ_open_typ_wrt_typ_upper : lngen.

Lemma tvar_in_exp_open_exp_wrt_typ_upper :
forall e1 A1,
  tvar_in_exp (open_exp_wrt_typ e1 A1) [<=] tvar_in_typ A1 `union` tvar_in_exp e1.
Proof.
unfold open_exp_wrt_typ; default_simp.
Qed.

#[export] Hint Resolve tvar_in_exp_open_exp_wrt_typ_upper : lngen.

Lemma tvar_in_exp_open_exp_wrt_exp_upper :
forall e1 e2,
  tvar_in_exp (open_exp_wrt_exp e1 e2) [<=] tvar_in_exp e2 `union` tvar_in_exp e1.
Proof.
unfold open_exp_wrt_exp; default_simp.
Qed.

#[export] Hint Resolve tvar_in_exp_open_exp_wrt_exp_upper : lngen.

Lemma var_in_exp_open_exp_wrt_typ_upper :
forall e1 A1,
  var_in_exp (open_exp_wrt_typ e1 A1) [<=] var_in_exp e1.
Proof.
unfold open_exp_wrt_typ; default_simp.
Qed.

#[export] Hint Resolve var_in_exp_open_exp_wrt_typ_upper : lngen.

Lemma var_in_exp_open_exp_wrt_exp_upper :
forall e1 e2,
  var_in_exp (open_exp_wrt_exp e1 e2) [<=] var_in_exp e2 `union` var_in_exp e1.
Proof.
unfold open_exp_wrt_exp; default_simp.
Qed.

#[export] Hint Resolve var_in_exp_open_exp_wrt_exp_upper : lngen.

Lemma tvar_in_entry_open_entry_wrt_typ_upper :
forall et1 A1,
  tvar_in_entry (open_entry_wrt_typ et1 A1) [<=] tvar_in_typ A1 `union` tvar_in_entry et1.
Proof.
unfold open_entry_wrt_typ; default_simp.
Qed.

#[export] Hint Resolve tvar_in_entry_open_entry_wrt_typ_upper : lngen.

(* begin hide *)

Lemma tvar_in_typ_subst_typ_in_typ_fresh_mutual :
(forall A1 A2 X1,
  X1 `notin` tvar_in_typ A1 ->
  tvar_in_typ (subst_typ_in_typ A2 X1 A1) [=] tvar_in_typ A1).
Proof.
apply_mutual_ind typ_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

Lemma tvar_in_typ_subst_typ_in_typ_fresh :
forall A1 A2 X1,
  X1 `notin` tvar_in_typ A1 ->
  tvar_in_typ (subst_typ_in_typ A2 X1 A1) [=] tvar_in_typ A1.
Proof.
pose proof tvar_in_typ_subst_typ_in_typ_fresh_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve tvar_in_typ_subst_typ_in_typ_fresh : lngen.
#[export] Hint Rewrite tvar_in_typ_subst_typ_in_typ_fresh using solve [auto] : lngen.

(* begin hide *)

Lemma tvar_in_exp_subst_typ_in_exp_fresh_mutual :
(forall e1 A1 X1,
  X1 `notin` tvar_in_exp e1 ->
  tvar_in_exp (subst_typ_in_exp A1 X1 e1) [=] tvar_in_exp e1).
Proof.
apply_mutual_ind exp_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

Lemma tvar_in_exp_subst_typ_in_exp_fresh :
forall e1 A1 X1,
  X1 `notin` tvar_in_exp e1 ->
  tvar_in_exp (subst_typ_in_exp A1 X1 e1) [=] tvar_in_exp e1.
Proof.
pose proof tvar_in_exp_subst_typ_in_exp_fresh_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve tvar_in_exp_subst_typ_in_exp_fresh : lngen.
#[export] Hint Rewrite tvar_in_exp_subst_typ_in_exp_fresh using solve [auto] : lngen.

(* begin hide *)

Lemma tvar_in_exp_subst_exp_in_exp_fresh_mutual :
(forall e1 A1 X1,
  var_in_exp (subst_typ_in_exp A1 X1 e1) [=] var_in_exp e1).
Proof.
apply_mutual_ind exp_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

Lemma tvar_in_exp_subst_exp_in_exp_fresh :
forall e1 A1 X1,
  var_in_exp (subst_typ_in_exp A1 X1 e1) [=] var_in_exp e1.
Proof.
pose proof tvar_in_exp_subst_exp_in_exp_fresh_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve tvar_in_exp_subst_exp_in_exp_fresh : lngen.
#[export] Hint Rewrite tvar_in_exp_subst_exp_in_exp_fresh using solve [auto] : lngen.

(* begin hide *)

Lemma var_in_exp_subst_exp_in_exp_fresh_mutual :
(forall e1 e2 x1,
  x1 `notin` var_in_exp e1 ->
  var_in_exp (subst_exp_in_exp e2 x1 e1) [=] var_in_exp e1).
Proof.
apply_mutual_ind exp_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

Lemma var_in_exp_subst_exp_in_exp_fresh :
forall e1 e2 x1,
  x1 `notin` var_in_exp e1 ->
  var_in_exp (subst_exp_in_exp e2 x1 e1) [=] var_in_exp e1.
Proof.
pose proof var_in_exp_subst_exp_in_exp_fresh_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve var_in_exp_subst_exp_in_exp_fresh : lngen.
#[export] Hint Rewrite var_in_exp_subst_exp_in_exp_fresh using solve [auto] : lngen.

(* begin hide *)

Lemma tvar_in_entry_subst_typ_in_entry_fresh_mutual :
(forall et1 A1 X1,
  X1 `notin` tvar_in_entry et1 ->
  tvar_in_entry (subst_typ_in_entry A1 X1 et1) [=] tvar_in_entry et1).
Proof.
apply_mutual_ind entry_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

Lemma tvar_in_entry_subst_typ_in_entry_fresh :
forall et1 A1 X1,
  X1 `notin` tvar_in_entry et1 ->
  tvar_in_entry (subst_typ_in_entry A1 X1 et1) [=] tvar_in_entry et1.
Proof.
pose proof tvar_in_entry_subst_typ_in_entry_fresh_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve tvar_in_entry_subst_typ_in_entry_fresh : lngen.
#[export] Hint Rewrite tvar_in_entry_subst_typ_in_entry_fresh using solve [auto] : lngen.

(* begin hide *)

Lemma tvar_in_typ_subst_typ_in_typ_lower_mutual :
(forall A1 A2 X1,
  remove X1 (tvar_in_typ A1) [<=] tvar_in_typ (subst_typ_in_typ A2 X1 A1)).
Proof.
apply_mutual_ind typ_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

Lemma tvar_in_typ_subst_typ_in_typ_lower :
forall A1 A2 X1,
  remove X1 (tvar_in_typ A1) [<=] tvar_in_typ (subst_typ_in_typ A2 X1 A1).
Proof.
pose proof tvar_in_typ_subst_typ_in_typ_lower_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve tvar_in_typ_subst_typ_in_typ_lower : lngen.

(* begin hide *)

Lemma tvar_in_exp_subst_typ_in_exp_lower_mutual :
(forall e1 A1 X1,
  remove X1 (tvar_in_exp e1) [<=] tvar_in_exp (subst_typ_in_exp A1 X1 e1)).
Proof.
apply_mutual_ind exp_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

Lemma tvar_in_exp_subst_typ_in_exp_lower :
forall e1 A1 X1,
  remove X1 (tvar_in_exp e1) [<=] tvar_in_exp (subst_typ_in_exp A1 X1 e1).
Proof.
pose proof tvar_in_exp_subst_typ_in_exp_lower_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve tvar_in_exp_subst_typ_in_exp_lower : lngen.

(* begin hide *)

Lemma tvar_in_exp_subst_exp_in_exp_lower_mutual :
(forall e1 e2 x1,
  tvar_in_exp e1 [<=] tvar_in_exp (subst_exp_in_exp e2 x1 e1)).
Proof.
apply_mutual_ind exp_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

Lemma tvar_in_exp_subst_exp_in_exp_lower :
forall e1 e2 x1,
  tvar_in_exp e1 [<=] tvar_in_exp (subst_exp_in_exp e2 x1 e1).
Proof.
pose proof tvar_in_exp_subst_exp_in_exp_lower_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve tvar_in_exp_subst_exp_in_exp_lower : lngen.

(* begin hide *)

Lemma var_in_exp_subst_typ_in_exp_lower_mutual :
(forall e1 A1 X1,
  var_in_exp e1 [<=] var_in_exp (subst_typ_in_exp A1 X1 e1)).
Proof.
apply_mutual_ind exp_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

Lemma var_in_exp_subst_typ_in_exp_lower :
forall e1 A1 X1,
  var_in_exp e1 [<=] var_in_exp (subst_typ_in_exp A1 X1 e1).
Proof.
pose proof var_in_exp_subst_typ_in_exp_lower_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve var_in_exp_subst_typ_in_exp_lower : lngen.

(* begin hide *)

Lemma var_in_exp_subst_exp_in_exp_lower_mutual :
(forall e1 e2 x1,
  remove x1 (var_in_exp e1) [<=] var_in_exp (subst_exp_in_exp e2 x1 e1)).
Proof.
apply_mutual_ind exp_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

Lemma var_in_exp_subst_exp_in_exp_lower :
forall e1 e2 x1,
  remove x1 (var_in_exp e1) [<=] var_in_exp (subst_exp_in_exp e2 x1 e1).
Proof.
pose proof var_in_exp_subst_exp_in_exp_lower_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve var_in_exp_subst_exp_in_exp_lower : lngen.

(* begin hide *)

Lemma tvar_in_entry_subst_typ_in_entry_lower_mutual :
(forall et1 A1 X1,
  remove X1 (tvar_in_entry et1) [<=] tvar_in_entry (subst_typ_in_entry A1 X1 et1)).
Proof.
apply_mutual_ind entry_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

Lemma tvar_in_entry_subst_typ_in_entry_lower :
forall et1 A1 X1,
  remove X1 (tvar_in_entry et1) [<=] tvar_in_entry (subst_typ_in_entry A1 X1 et1).
Proof.
pose proof tvar_in_entry_subst_typ_in_entry_lower_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve tvar_in_entry_subst_typ_in_entry_lower : lngen.

(* begin hide *)

Lemma tvar_in_typ_subst_typ_in_typ_notin_mutual :
(forall A1 A2 X1 X2,
  X2 `notin` tvar_in_typ A1 ->
  X2 `notin` tvar_in_typ A2 ->
  X2 `notin` tvar_in_typ (subst_typ_in_typ A2 X1 A1)).
Proof.
apply_mutual_ind typ_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

Lemma tvar_in_typ_subst_typ_in_typ_notin :
forall A1 A2 X1 X2,
  X2 `notin` tvar_in_typ A1 ->
  X2 `notin` tvar_in_typ A2 ->
  X2 `notin` tvar_in_typ (subst_typ_in_typ A2 X1 A1).
Proof.
pose proof tvar_in_typ_subst_typ_in_typ_notin_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve tvar_in_typ_subst_typ_in_typ_notin : lngen.

(* begin hide *)

Lemma tvar_in_exp_subst_typ_in_exp_notin_mutual :
(forall e1 A1 X1 X2,
  X2 `notin` tvar_in_exp e1 ->
  X2 `notin` tvar_in_typ A1 ->
  X2 `notin` tvar_in_exp (subst_typ_in_exp A1 X1 e1)).
Proof.
apply_mutual_ind exp_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

Lemma tvar_in_exp_subst_typ_in_exp_notin :
forall e1 A1 X1 X2,
  X2 `notin` tvar_in_exp e1 ->
  X2 `notin` tvar_in_typ A1 ->
  X2 `notin` tvar_in_exp (subst_typ_in_exp A1 X1 e1).
Proof.
pose proof tvar_in_exp_subst_typ_in_exp_notin_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve tvar_in_exp_subst_typ_in_exp_notin : lngen.

(* begin hide *)

Lemma tvar_in_exp_subst_exp_in_exp_notin_mutual :
(forall e1 e2 x1 X1,
  X1 `notin` tvar_in_exp e1 ->
  X1 `notin` tvar_in_exp e2 ->
  X1 `notin` tvar_in_exp (subst_exp_in_exp e2 x1 e1)).
Proof.
apply_mutual_ind exp_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

Lemma tvar_in_exp_subst_exp_in_exp_notin :
forall e1 e2 x1 X1,
  X1 `notin` tvar_in_exp e1 ->
  X1 `notin` tvar_in_exp e2 ->
  X1 `notin` tvar_in_exp (subst_exp_in_exp e2 x1 e1).
Proof.
pose proof tvar_in_exp_subst_exp_in_exp_notin_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve tvar_in_exp_subst_exp_in_exp_notin : lngen.

(* begin hide *)

Lemma var_in_exp_subst_typ_in_exp_notin_mutual :
(forall e1 A1 X1 x1,
  x1 `notin` var_in_exp e1 ->
  x1 `notin` var_in_exp (subst_typ_in_exp A1 X1 e1)).
Proof.
apply_mutual_ind exp_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

Lemma var_in_exp_subst_typ_in_exp_notin :
forall e1 A1 X1 x1,
  x1 `notin` var_in_exp e1 ->
  x1 `notin` var_in_exp (subst_typ_in_exp A1 X1 e1).
Proof.
pose proof var_in_exp_subst_typ_in_exp_notin_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve var_in_exp_subst_typ_in_exp_notin : lngen.

(* begin hide *)

Lemma var_in_exp_subst_exp_in_exp_notin_mutual :
(forall e1 e2 x1 x2,
  x2 `notin` var_in_exp e1 ->
  x2 `notin` var_in_exp e2 ->
  x2 `notin` var_in_exp (subst_exp_in_exp e2 x1 e1)).
Proof.
apply_mutual_ind exp_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

Lemma var_in_exp_subst_exp_in_exp_notin :
forall e1 e2 x1 x2,
  x2 `notin` var_in_exp e1 ->
  x2 `notin` var_in_exp e2 ->
  x2 `notin` var_in_exp (subst_exp_in_exp e2 x1 e1).
Proof.
pose proof var_in_exp_subst_exp_in_exp_notin_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve var_in_exp_subst_exp_in_exp_notin : lngen.

(* begin hide *)

Lemma tvar_in_entry_subst_typ_in_entry_notin_mutual :
(forall et1 A1 X1 X2,
  X2 `notin` tvar_in_entry et1 ->
  X2 `notin` tvar_in_typ A1 ->
  X2 `notin` tvar_in_entry (subst_typ_in_entry A1 X1 et1)).
Proof.
apply_mutual_ind entry_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

Lemma tvar_in_entry_subst_typ_in_entry_notin :
forall et1 A1 X1 X2,
  X2 `notin` tvar_in_entry et1 ->
  X2 `notin` tvar_in_typ A1 ->
  X2 `notin` tvar_in_entry (subst_typ_in_entry A1 X1 et1).
Proof.
pose proof tvar_in_entry_subst_typ_in_entry_notin_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve tvar_in_entry_subst_typ_in_entry_notin : lngen.

(* begin hide *)

Lemma tvar_in_typ_subst_typ_in_typ_upper_mutual :
(forall A1 A2 X1,
  tvar_in_typ (subst_typ_in_typ A2 X1 A1) [<=] tvar_in_typ A2 `union` remove X1 (tvar_in_typ A1)).
Proof.
apply_mutual_ind typ_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

Lemma tvar_in_typ_subst_typ_in_typ_upper :
forall A1 A2 X1,
  tvar_in_typ (subst_typ_in_typ A2 X1 A1) [<=] tvar_in_typ A2 `union` remove X1 (tvar_in_typ A1).
Proof.
pose proof tvar_in_typ_subst_typ_in_typ_upper_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve tvar_in_typ_subst_typ_in_typ_upper : lngen.

(* begin hide *)

Lemma tvar_in_exp_subst_typ_in_exp_upper_mutual :
(forall e1 A1 X1,
  tvar_in_exp (subst_typ_in_exp A1 X1 e1) [<=] tvar_in_typ A1 `union` remove X1 (tvar_in_exp e1)).
Proof.
apply_mutual_ind exp_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

Lemma tvar_in_exp_subst_typ_in_exp_upper :
forall e1 A1 X1,
  tvar_in_exp (subst_typ_in_exp A1 X1 e1) [<=] tvar_in_typ A1 `union` remove X1 (tvar_in_exp e1).
Proof.
pose proof tvar_in_exp_subst_typ_in_exp_upper_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve tvar_in_exp_subst_typ_in_exp_upper : lngen.

(* begin hide *)

Lemma tvar_in_exp_subst_exp_in_exp_upper_mutual :
(forall e1 e2 x1,
  tvar_in_exp (subst_exp_in_exp e2 x1 e1) [<=] tvar_in_exp e2 `union` tvar_in_exp e1).
Proof.
apply_mutual_ind exp_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

Lemma tvar_in_exp_subst_exp_in_exp_upper :
forall e1 e2 x1,
  tvar_in_exp (subst_exp_in_exp e2 x1 e1) [<=] tvar_in_exp e2 `union` tvar_in_exp e1.
Proof.
pose proof tvar_in_exp_subst_exp_in_exp_upper_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve tvar_in_exp_subst_exp_in_exp_upper : lngen.

(* begin hide *)

Lemma var_in_exp_subst_typ_in_exp_upper_mutual :
(forall e1 A1 X1,
  var_in_exp (subst_typ_in_exp A1 X1 e1) [<=] var_in_exp e1).
Proof.
apply_mutual_ind exp_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

Lemma var_in_exp_subst_typ_in_exp_upper :
forall e1 A1 X1,
  var_in_exp (subst_typ_in_exp A1 X1 e1) [<=] var_in_exp e1.
Proof.
pose proof var_in_exp_subst_typ_in_exp_upper_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve var_in_exp_subst_typ_in_exp_upper : lngen.

(* begin hide *)

Lemma var_in_exp_subst_exp_in_exp_upper_mutual :
(forall e1 e2 x1,
  var_in_exp (subst_exp_in_exp e2 x1 e1) [<=] var_in_exp e2 `union` remove x1 (var_in_exp e1)).
Proof.
apply_mutual_ind exp_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

Lemma var_in_exp_subst_exp_in_exp_upper :
forall e1 e2 x1,
  var_in_exp (subst_exp_in_exp e2 x1 e1) [<=] var_in_exp e2 `union` remove x1 (var_in_exp e1).
Proof.
pose proof var_in_exp_subst_exp_in_exp_upper_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve var_in_exp_subst_exp_in_exp_upper : lngen.

(* begin hide *)

Lemma tvar_in_entry_subst_typ_in_entry_upper_mutual :
(forall et1 A1 X1,
  tvar_in_entry (subst_typ_in_entry A1 X1 et1) [<=] tvar_in_typ A1 `union` remove X1 (tvar_in_entry et1)).
Proof.
apply_mutual_ind entry_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

Lemma tvar_in_entry_subst_typ_in_entry_upper :
forall et1 A1 X1,
  tvar_in_entry (subst_typ_in_entry A1 X1 et1) [<=] tvar_in_typ A1 `union` remove X1 (tvar_in_entry et1).
Proof.
pose proof tvar_in_entry_subst_typ_in_entry_upper_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve tvar_in_entry_subst_typ_in_entry_upper : lngen.


(* *********************************************************************** *)
(** * Theorems about [subst] *)

Ltac default_auto ::= auto with lngen brute_force; tauto.
Ltac default_autorewrite ::= autorewrite with lngen.

(* begin hide *)

Lemma subst_typ_in_typ_close_typ_wrt_typ_rec_mutual :
(forall A2 A1 X1 X2 n1,
  degree_typ_wrt_typ n1 A1 ->
  X1 <> X2 ->
  X2 `notin` tvar_in_typ A1 ->
  subst_typ_in_typ A1 X1 (close_typ_wrt_typ_rec n1 X2 A2) = close_typ_wrt_typ_rec n1 X2 (subst_typ_in_typ A1 X1 A2)).
Proof.
apply_mutual_ind typ_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_typ_in_typ_close_typ_wrt_typ_rec :
forall A2 A1 X1 X2 n1,
  degree_typ_wrt_typ n1 A1 ->
  X1 <> X2 ->
  X2 `notin` tvar_in_typ A1 ->
  subst_typ_in_typ A1 X1 (close_typ_wrt_typ_rec n1 X2 A2) = close_typ_wrt_typ_rec n1 X2 (subst_typ_in_typ A1 X1 A2).
Proof.
pose proof subst_typ_in_typ_close_typ_wrt_typ_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_typ_in_typ_close_typ_wrt_typ_rec : lngen.

(* begin hide *)

Lemma subst_typ_in_exp_close_exp_wrt_typ_rec_mutual :
(forall e1 A1 X1 X2 n1,
  degree_typ_wrt_typ n1 A1 ->
  X1 <> X2 ->
  X2 `notin` tvar_in_typ A1 ->
  subst_typ_in_exp A1 X1 (close_exp_wrt_typ_rec n1 X2 e1) = close_exp_wrt_typ_rec n1 X2 (subst_typ_in_exp A1 X1 e1)).
Proof.
apply_mutual_ind exp_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_typ_in_exp_close_exp_wrt_typ_rec :
forall e1 A1 X1 X2 n1,
  degree_typ_wrt_typ n1 A1 ->
  X1 <> X2 ->
  X2 `notin` tvar_in_typ A1 ->
  subst_typ_in_exp A1 X1 (close_exp_wrt_typ_rec n1 X2 e1) = close_exp_wrt_typ_rec n1 X2 (subst_typ_in_exp A1 X1 e1).
Proof.
pose proof subst_typ_in_exp_close_exp_wrt_typ_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_typ_in_exp_close_exp_wrt_typ_rec : lngen.

(* begin hide *)

Lemma subst_typ_in_exp_close_exp_wrt_exp_rec_mutual :
(forall e1 A1 x1 X1 n1,
  subst_typ_in_exp A1 x1 (close_exp_wrt_exp_rec n1 X1 e1) = close_exp_wrt_exp_rec n1 X1 (subst_typ_in_exp A1 x1 e1)).
Proof.
apply_mutual_ind exp_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_typ_in_exp_close_exp_wrt_exp_rec :
forall e1 A1 x1 X1 n1,
  subst_typ_in_exp A1 x1 (close_exp_wrt_exp_rec n1 X1 e1) = close_exp_wrt_exp_rec n1 X1 (subst_typ_in_exp A1 x1 e1).
Proof.
pose proof subst_typ_in_exp_close_exp_wrt_exp_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_typ_in_exp_close_exp_wrt_exp_rec : lngen.

(* begin hide *)

Lemma subst_exp_in_exp_close_exp_wrt_typ_rec_mutual :
(forall e2 e1 X1 x1 n1,
  degree_exp_wrt_typ n1 e1 ->
  x1 `notin` tvar_in_exp e1 ->
  subst_exp_in_exp e1 X1 (close_exp_wrt_typ_rec n1 x1 e2) = close_exp_wrt_typ_rec n1 x1 (subst_exp_in_exp e1 X1 e2)).
Proof.
apply_mutual_ind exp_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_exp_in_exp_close_exp_wrt_typ_rec :
forall e2 e1 X1 x1 n1,
  degree_exp_wrt_typ n1 e1 ->
  x1 `notin` tvar_in_exp e1 ->
  subst_exp_in_exp e1 X1 (close_exp_wrt_typ_rec n1 x1 e2) = close_exp_wrt_typ_rec n1 x1 (subst_exp_in_exp e1 X1 e2).
Proof.
pose proof subst_exp_in_exp_close_exp_wrt_typ_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_exp_in_exp_close_exp_wrt_typ_rec : lngen.

(* begin hide *)

Lemma subst_exp_in_exp_close_exp_wrt_exp_rec_mutual :
(forall e2 e1 x1 x2 n1,
  degree_exp_wrt_exp n1 e1 ->
  x1 <> x2 ->
  x2 `notin` var_in_exp e1 ->
  subst_exp_in_exp e1 x1 (close_exp_wrt_exp_rec n1 x2 e2) = close_exp_wrt_exp_rec n1 x2 (subst_exp_in_exp e1 x1 e2)).
Proof.
apply_mutual_ind exp_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_exp_in_exp_close_exp_wrt_exp_rec :
forall e2 e1 x1 x2 n1,
  degree_exp_wrt_exp n1 e1 ->
  x1 <> x2 ->
  x2 `notin` var_in_exp e1 ->
  subst_exp_in_exp e1 x1 (close_exp_wrt_exp_rec n1 x2 e2) = close_exp_wrt_exp_rec n1 x2 (subst_exp_in_exp e1 x1 e2).
Proof.
pose proof subst_exp_in_exp_close_exp_wrt_exp_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_exp_in_exp_close_exp_wrt_exp_rec : lngen.

(* begin hide *)

Lemma subst_typ_in_entry_close_entry_wrt_typ_rec_mutual :
(forall et1 A1 X1 X2 n1,
  degree_typ_wrt_typ n1 A1 ->
  X1 <> X2 ->
  X2 `notin` tvar_in_typ A1 ->
  subst_typ_in_entry A1 X1 (close_entry_wrt_typ_rec n1 X2 et1) = close_entry_wrt_typ_rec n1 X2 (subst_typ_in_entry A1 X1 et1)).
Proof.
apply_mutual_ind entry_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_typ_in_entry_close_entry_wrt_typ_rec :
forall et1 A1 X1 X2 n1,
  degree_typ_wrt_typ n1 A1 ->
  X1 <> X2 ->
  X2 `notin` tvar_in_typ A1 ->
  subst_typ_in_entry A1 X1 (close_entry_wrt_typ_rec n1 X2 et1) = close_entry_wrt_typ_rec n1 X2 (subst_typ_in_entry A1 X1 et1).
Proof.
pose proof subst_typ_in_entry_close_entry_wrt_typ_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_typ_in_entry_close_entry_wrt_typ_rec : lngen.

Lemma subst_typ_in_typ_close_typ_wrt_typ :
forall A2 A1 X1 X2,
  lc_typ A1 ->  X1 <> X2 ->
  X2 `notin` tvar_in_typ A1 ->
  subst_typ_in_typ A1 X1 (close_typ_wrt_typ X2 A2) = close_typ_wrt_typ X2 (subst_typ_in_typ A1 X1 A2).
Proof.
unfold close_typ_wrt_typ; default_simp.
Qed.

#[export] Hint Resolve subst_typ_in_typ_close_typ_wrt_typ : lngen.

Lemma subst_typ_in_exp_close_exp_wrt_typ :
forall e1 A1 X1 X2,
  lc_typ A1 ->  X1 <> X2 ->
  X2 `notin` tvar_in_typ A1 ->
  subst_typ_in_exp A1 X1 (close_exp_wrt_typ X2 e1) = close_exp_wrt_typ X2 (subst_typ_in_exp A1 X1 e1).
Proof.
unfold close_exp_wrt_typ; default_simp.
Qed.

#[export] Hint Resolve subst_typ_in_exp_close_exp_wrt_typ : lngen.

Lemma subst_typ_in_exp_close_exp_wrt_exp :
forall e1 A1 x1 X1,
  lc_typ A1 ->  subst_typ_in_exp A1 x1 (close_exp_wrt_exp X1 e1) = close_exp_wrt_exp X1 (subst_typ_in_exp A1 x1 e1).
Proof.
unfold close_exp_wrt_exp; default_simp.
Qed.

#[export] Hint Resolve subst_typ_in_exp_close_exp_wrt_exp : lngen.

Lemma subst_exp_in_exp_close_exp_wrt_typ :
forall e2 e1 X1 x1,
  lc_exp e1 ->  x1 `notin` tvar_in_exp e1 ->
  subst_exp_in_exp e1 X1 (close_exp_wrt_typ x1 e2) = close_exp_wrt_typ x1 (subst_exp_in_exp e1 X1 e2).
Proof.
unfold close_exp_wrt_typ; default_simp.
Qed.

#[export] Hint Resolve subst_exp_in_exp_close_exp_wrt_typ : lngen.

Lemma subst_exp_in_exp_close_exp_wrt_exp :
forall e2 e1 x1 x2,
  lc_exp e1 ->  x1 <> x2 ->
  x2 `notin` var_in_exp e1 ->
  subst_exp_in_exp e1 x1 (close_exp_wrt_exp x2 e2) = close_exp_wrt_exp x2 (subst_exp_in_exp e1 x1 e2).
Proof.
unfold close_exp_wrt_exp; default_simp.
Qed.

#[export] Hint Resolve subst_exp_in_exp_close_exp_wrt_exp : lngen.

Lemma subst_typ_in_entry_close_entry_wrt_typ :
forall et1 A1 X1 X2,
  lc_typ A1 ->  X1 <> X2 ->
  X2 `notin` tvar_in_typ A1 ->
  subst_typ_in_entry A1 X1 (close_entry_wrt_typ X2 et1) = close_entry_wrt_typ X2 (subst_typ_in_entry A1 X1 et1).
Proof.
unfold close_entry_wrt_typ; default_simp.
Qed.

#[export] Hint Resolve subst_typ_in_entry_close_entry_wrt_typ : lngen.

(* begin hide *)

Lemma subst_typ_in_typ_degree_typ_wrt_typ_mutual :
(forall A1 A2 X1 n1,
  degree_typ_wrt_typ n1 A1 ->
  degree_typ_wrt_typ n1 A2 ->
  degree_typ_wrt_typ n1 (subst_typ_in_typ A2 X1 A1)).
Proof.
apply_mutual_ind typ_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_typ_in_typ_degree_typ_wrt_typ :
forall A1 A2 X1 n1,
  degree_typ_wrt_typ n1 A1 ->
  degree_typ_wrt_typ n1 A2 ->
  degree_typ_wrt_typ n1 (subst_typ_in_typ A2 X1 A1).
Proof.
pose proof subst_typ_in_typ_degree_typ_wrt_typ_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_typ_in_typ_degree_typ_wrt_typ : lngen.

(* begin hide *)

Lemma subst_typ_in_exp_degree_exp_wrt_typ_mutual :
(forall e1 A1 X1 n1,
  degree_exp_wrt_typ n1 e1 ->
  degree_typ_wrt_typ n1 A1 ->
  degree_exp_wrt_typ n1 (subst_typ_in_exp A1 X1 e1)).
Proof.
apply_mutual_ind exp_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_typ_in_exp_degree_exp_wrt_typ :
forall e1 A1 X1 n1,
  degree_exp_wrt_typ n1 e1 ->
  degree_typ_wrt_typ n1 A1 ->
  degree_exp_wrt_typ n1 (subst_typ_in_exp A1 X1 e1).
Proof.
pose proof subst_typ_in_exp_degree_exp_wrt_typ_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_typ_in_exp_degree_exp_wrt_typ : lngen.

(* begin hide *)

Lemma subst_typ_in_exp_degree_exp_wrt_exp_mutual :
(forall e1 A1 X1 n1,
  degree_exp_wrt_exp n1 e1 ->
  degree_exp_wrt_exp n1 (subst_typ_in_exp A1 X1 e1)).
Proof.
apply_mutual_ind exp_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_typ_in_exp_degree_exp_wrt_exp :
forall e1 A1 X1 n1,
  degree_exp_wrt_exp n1 e1 ->
  degree_exp_wrt_exp n1 (subst_typ_in_exp A1 X1 e1).
Proof.
pose proof subst_typ_in_exp_degree_exp_wrt_exp_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_typ_in_exp_degree_exp_wrt_exp : lngen.

(* begin hide *)

Lemma subst_exp_in_exp_degree_exp_wrt_typ_mutual :
(forall e1 e2 x1 n1,
  degree_exp_wrt_typ n1 e1 ->
  degree_exp_wrt_typ n1 e2 ->
  degree_exp_wrt_typ n1 (subst_exp_in_exp e2 x1 e1)).
Proof.
apply_mutual_ind exp_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_exp_in_exp_degree_exp_wrt_typ :
forall e1 e2 x1 n1,
  degree_exp_wrt_typ n1 e1 ->
  degree_exp_wrt_typ n1 e2 ->
  degree_exp_wrt_typ n1 (subst_exp_in_exp e2 x1 e1).
Proof.
pose proof subst_exp_in_exp_degree_exp_wrt_typ_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_exp_in_exp_degree_exp_wrt_typ : lngen.

(* begin hide *)

Lemma subst_exp_in_exp_degree_exp_wrt_exp_mutual :
(forall e1 e2 x1 n1,
  degree_exp_wrt_exp n1 e1 ->
  degree_exp_wrt_exp n1 e2 ->
  degree_exp_wrt_exp n1 (subst_exp_in_exp e2 x1 e1)).
Proof.
apply_mutual_ind exp_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_exp_in_exp_degree_exp_wrt_exp :
forall e1 e2 x1 n1,
  degree_exp_wrt_exp n1 e1 ->
  degree_exp_wrt_exp n1 e2 ->
  degree_exp_wrt_exp n1 (subst_exp_in_exp e2 x1 e1).
Proof.
pose proof subst_exp_in_exp_degree_exp_wrt_exp_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_exp_in_exp_degree_exp_wrt_exp : lngen.

(* begin hide *)

Lemma subst_typ_in_entry_degree_entry_wrt_typ_mutual :
(forall et1 A1 X1 n1,
  degree_entry_wrt_typ n1 et1 ->
  degree_typ_wrt_typ n1 A1 ->
  degree_entry_wrt_typ n1 (subst_typ_in_entry A1 X1 et1)).
Proof.
apply_mutual_ind entry_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_typ_in_entry_degree_entry_wrt_typ :
forall et1 A1 X1 n1,
  degree_entry_wrt_typ n1 et1 ->
  degree_typ_wrt_typ n1 A1 ->
  degree_entry_wrt_typ n1 (subst_typ_in_entry A1 X1 et1).
Proof.
pose proof subst_typ_in_entry_degree_entry_wrt_typ_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_typ_in_entry_degree_entry_wrt_typ : lngen.

(* begin hide *)

Lemma subst_typ_in_typ_fresh_eq_mutual :
(forall A2 A1 X1,
  X1 `notin` tvar_in_typ A2 ->
  subst_typ_in_typ A1 X1 A2 = A2).
Proof.
apply_mutual_ind typ_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_typ_in_typ_fresh_eq :
forall A2 A1 X1,
  X1 `notin` tvar_in_typ A2 ->
  subst_typ_in_typ A1 X1 A2 = A2.
Proof.
pose proof subst_typ_in_typ_fresh_eq_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_typ_in_typ_fresh_eq : lngen.
#[export] Hint Rewrite subst_typ_in_typ_fresh_eq using solve [auto] : lngen.

(* begin hide *)

Lemma subst_typ_in_exp_fresh_eq_mutual :
(forall e1 A1 X1,
  X1 `notin` tvar_in_exp e1 ->
  subst_typ_in_exp A1 X1 e1 = e1).
Proof.
apply_mutual_ind exp_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_typ_in_exp_fresh_eq :
forall e1 A1 X1,
  X1 `notin` tvar_in_exp e1 ->
  subst_typ_in_exp A1 X1 e1 = e1.
Proof.
pose proof subst_typ_in_exp_fresh_eq_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_typ_in_exp_fresh_eq : lngen.
#[export] Hint Rewrite subst_typ_in_exp_fresh_eq using solve [auto] : lngen.

(* begin hide *)

Lemma subst_exp_in_exp_fresh_eq_mutual :
(forall e2 e1 x1,
  x1 `notin` var_in_exp e2 ->
  subst_exp_in_exp e1 x1 e2 = e2).
Proof.
apply_mutual_ind exp_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_exp_in_exp_fresh_eq :
forall e2 e1 x1,
  x1 `notin` var_in_exp e2 ->
  subst_exp_in_exp e1 x1 e2 = e2.
Proof.
pose proof subst_exp_in_exp_fresh_eq_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_exp_in_exp_fresh_eq : lngen.
#[export] Hint Rewrite subst_exp_in_exp_fresh_eq using solve [auto] : lngen.

(* begin hide *)

Lemma subst_typ_in_entry_fresh_eq_mutual :
(forall et1 A1 X1,
  X1 `notin` tvar_in_entry et1 ->
  subst_typ_in_entry A1 X1 et1 = et1).
Proof.
apply_mutual_ind entry_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_typ_in_entry_fresh_eq :
forall et1 A1 X1,
  X1 `notin` tvar_in_entry et1 ->
  subst_typ_in_entry A1 X1 et1 = et1.
Proof.
pose proof subst_typ_in_entry_fresh_eq_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_typ_in_entry_fresh_eq : lngen.
#[export] Hint Rewrite subst_typ_in_entry_fresh_eq using solve [auto] : lngen.

(* begin hide *)

Lemma subst_typ_in_typ_fresh_same_mutual :
(forall A2 A1 X1,
  X1 `notin` tvar_in_typ A1 ->
  X1 `notin` tvar_in_typ (subst_typ_in_typ A1 X1 A2)).
Proof.
apply_mutual_ind typ_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_typ_in_typ_fresh_same :
forall A2 A1 X1,
  X1 `notin` tvar_in_typ A1 ->
  X1 `notin` tvar_in_typ (subst_typ_in_typ A1 X1 A2).
Proof.
pose proof subst_typ_in_typ_fresh_same_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_typ_in_typ_fresh_same : lngen.

(* begin hide *)

Lemma subst_typ_in_exp_fresh_same_mutual :
(forall e1 A1 X1,
  X1 `notin` tvar_in_typ A1 ->
  X1 `notin` tvar_in_exp (subst_typ_in_exp A1 X1 e1)).
Proof.
apply_mutual_ind exp_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_typ_in_exp_fresh_same :
forall e1 A1 X1,
  X1 `notin` tvar_in_typ A1 ->
  X1 `notin` tvar_in_exp (subst_typ_in_exp A1 X1 e1).
Proof.
pose proof subst_typ_in_exp_fresh_same_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_typ_in_exp_fresh_same : lngen.

(* begin hide *)

Lemma subst_exp_in_exp_fresh_same_mutual :
(forall e2 e1 x1,
  x1 `notin` var_in_exp e1 ->
  x1 `notin` var_in_exp (subst_exp_in_exp e1 x1 e2)).
Proof.
apply_mutual_ind exp_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_exp_in_exp_fresh_same :
forall e2 e1 x1,
  x1 `notin` var_in_exp e1 ->
  x1 `notin` var_in_exp (subst_exp_in_exp e1 x1 e2).
Proof.
pose proof subst_exp_in_exp_fresh_same_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_exp_in_exp_fresh_same : lngen.

(* begin hide *)

Lemma subst_typ_in_entry_fresh_same_mutual :
(forall et1 A1 X1,
  X1 `notin` tvar_in_typ A1 ->
  X1 `notin` tvar_in_entry (subst_typ_in_entry A1 X1 et1)).
Proof.
apply_mutual_ind entry_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_typ_in_entry_fresh_same :
forall et1 A1 X1,
  X1 `notin` tvar_in_typ A1 ->
  X1 `notin` tvar_in_entry (subst_typ_in_entry A1 X1 et1).
Proof.
pose proof subst_typ_in_entry_fresh_same_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_typ_in_entry_fresh_same : lngen.

(* begin hide *)

Lemma subst_typ_in_typ_fresh_mutual :
(forall A2 A1 X1 X2,
  X1 `notin` tvar_in_typ A2 ->
  X1 `notin` tvar_in_typ A1 ->
  X1 `notin` tvar_in_typ (subst_typ_in_typ A1 X2 A2)).
Proof.
apply_mutual_ind typ_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_typ_in_typ_fresh :
forall A2 A1 X1 X2,
  X1 `notin` tvar_in_typ A2 ->
  X1 `notin` tvar_in_typ A1 ->
  X1 `notin` tvar_in_typ (subst_typ_in_typ A1 X2 A2).
Proof.
pose proof subst_typ_in_typ_fresh_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_typ_in_typ_fresh : lngen.

(* begin hide *)

Lemma subst_typ_in_exp_fresh_mutual :
(forall e1 A1 X1 X2,
  X1 `notin` tvar_in_exp e1 ->
  X1 `notin` tvar_in_typ A1 ->
  X1 `notin` tvar_in_exp (subst_typ_in_exp A1 X2 e1)).
Proof.
apply_mutual_ind exp_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_typ_in_exp_fresh :
forall e1 A1 X1 X2,
  X1 `notin` tvar_in_exp e1 ->
  X1 `notin` tvar_in_typ A1 ->
  X1 `notin` tvar_in_exp (subst_typ_in_exp A1 X2 e1).
Proof.
pose proof subst_typ_in_exp_fresh_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_typ_in_exp_fresh : lngen.

(* begin hide *)

Lemma subst_exp_in_exp_fresh_mutual :
(forall e2 e1 x1 x2,
  x1 `notin` var_in_exp e2 ->
  x1 `notin` var_in_exp e1 ->
  x1 `notin` var_in_exp (subst_exp_in_exp e1 x2 e2)).
Proof.
apply_mutual_ind exp_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_exp_in_exp_fresh :
forall e2 e1 x1 x2,
  x1 `notin` var_in_exp e2 ->
  x1 `notin` var_in_exp e1 ->
  x1 `notin` var_in_exp (subst_exp_in_exp e1 x2 e2).
Proof.
pose proof subst_exp_in_exp_fresh_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_exp_in_exp_fresh : lngen.

(* begin hide *)

Lemma subst_typ_in_entry_fresh_mutual :
(forall et1 A1 X1 X2,
  X1 `notin` tvar_in_entry et1 ->
  X1 `notin` tvar_in_typ A1 ->
  X1 `notin` tvar_in_entry (subst_typ_in_entry A1 X2 et1)).
Proof.
apply_mutual_ind entry_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_typ_in_entry_fresh :
forall et1 A1 X1 X2,
  X1 `notin` tvar_in_entry et1 ->
  X1 `notin` tvar_in_typ A1 ->
  X1 `notin` tvar_in_entry (subst_typ_in_entry A1 X2 et1).
Proof.
pose proof subst_typ_in_entry_fresh_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_typ_in_entry_fresh : lngen.

Lemma subst_typ_in_typ_lc_typ :
forall A1 A2 X1,
  lc_typ A1 ->
  lc_typ A2 ->
  lc_typ (subst_typ_in_typ A2 X1 A1).
Proof.
default_simp.
Qed.

#[export] Hint Resolve subst_typ_in_typ_lc_typ : lngen.

Lemma subst_typ_in_exp_lc_exp :
forall e1 A1 X1,
  lc_exp e1 ->
  lc_typ A1 ->
  lc_exp (subst_typ_in_exp A1 X1 e1).
Proof.
default_simp.
Qed.

#[export] Hint Resolve subst_typ_in_exp_lc_exp : lngen.

Lemma subst_exp_in_exp_lc_exp :
forall e1 e2 x1,
  lc_exp e1 ->
  lc_exp e2 ->
  lc_exp (subst_exp_in_exp e2 x1 e1).
Proof.
default_simp.
Qed.

#[export] Hint Resolve subst_exp_in_exp_lc_exp : lngen.

Lemma subst_typ_in_entry_lc_entry :
forall et1 A1 X1,
  lc_entry et1 ->
  lc_typ A1 ->
  lc_entry (subst_typ_in_entry A1 X1 et1).
Proof.
default_simp.
Qed.

#[export] Hint Resolve subst_typ_in_entry_lc_entry : lngen.

(* begin hide *)

Lemma subst_typ_in_typ_open_typ_wrt_typ_rec_mutual :
(forall A3 A1 A2 X1 n1,
  lc_typ A1 ->
  subst_typ_in_typ A1 X1 (open_typ_wrt_typ_rec n1 A2 A3) = open_typ_wrt_typ_rec n1 (subst_typ_in_typ A1 X1 A2) (subst_typ_in_typ A1 X1 A3)).
Proof.
apply_mutual_ind typ_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma subst_typ_in_typ_open_typ_wrt_typ_rec :
forall A3 A1 A2 X1 n1,
  lc_typ A1 ->
  subst_typ_in_typ A1 X1 (open_typ_wrt_typ_rec n1 A2 A3) = open_typ_wrt_typ_rec n1 (subst_typ_in_typ A1 X1 A2) (subst_typ_in_typ A1 X1 A3).
Proof.
pose proof subst_typ_in_typ_open_typ_wrt_typ_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_typ_in_typ_open_typ_wrt_typ_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma subst_typ_in_exp_open_exp_wrt_typ_rec_mutual :
(forall e1 A1 A2 X1 n1,
  lc_typ A1 ->
  subst_typ_in_exp A1 X1 (open_exp_wrt_typ_rec n1 A2 e1) = open_exp_wrt_typ_rec n1 (subst_typ_in_typ A1 X1 A2) (subst_typ_in_exp A1 X1 e1)).
Proof.
apply_mutual_ind exp_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma subst_typ_in_exp_open_exp_wrt_typ_rec :
forall e1 A1 A2 X1 n1,
  lc_typ A1 ->
  subst_typ_in_exp A1 X1 (open_exp_wrt_typ_rec n1 A2 e1) = open_exp_wrt_typ_rec n1 (subst_typ_in_typ A1 X1 A2) (subst_typ_in_exp A1 X1 e1).
Proof.
pose proof subst_typ_in_exp_open_exp_wrt_typ_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_typ_in_exp_open_exp_wrt_typ_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma subst_typ_in_exp_open_exp_wrt_exp_rec_mutual :
(forall e2 A1 e1 X1 n1,
  subst_typ_in_exp A1 X1 (open_exp_wrt_exp_rec n1 e1 e2) = open_exp_wrt_exp_rec n1 (subst_typ_in_exp A1 X1 e1) (subst_typ_in_exp A1 X1 e2)).
Proof.
apply_mutual_ind exp_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma subst_typ_in_exp_open_exp_wrt_exp_rec :
forall e2 A1 e1 X1 n1,
  subst_typ_in_exp A1 X1 (open_exp_wrt_exp_rec n1 e1 e2) = open_exp_wrt_exp_rec n1 (subst_typ_in_exp A1 X1 e1) (subst_typ_in_exp A1 X1 e2).
Proof.
pose proof subst_typ_in_exp_open_exp_wrt_exp_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_typ_in_exp_open_exp_wrt_exp_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma subst_exp_in_exp_open_exp_wrt_typ_rec_mutual :
(forall e2 e1 A1 x1 n1,
  lc_exp e1 ->
  subst_exp_in_exp e1 x1 (open_exp_wrt_typ_rec n1 A1 e2) = open_exp_wrt_typ_rec n1 A1 (subst_exp_in_exp e1 x1 e2)).
Proof.
apply_mutual_ind exp_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma subst_exp_in_exp_open_exp_wrt_typ_rec :
forall e2 e1 A1 x1 n1,
  lc_exp e1 ->
  subst_exp_in_exp e1 x1 (open_exp_wrt_typ_rec n1 A1 e2) = open_exp_wrt_typ_rec n1 A1 (subst_exp_in_exp e1 x1 e2).
Proof.
pose proof subst_exp_in_exp_open_exp_wrt_typ_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_exp_in_exp_open_exp_wrt_typ_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma subst_exp_in_exp_open_exp_wrt_exp_rec_mutual :
(forall e3 e1 e2 x1 n1,
  lc_exp e1 ->
  subst_exp_in_exp e1 x1 (open_exp_wrt_exp_rec n1 e2 e3) = open_exp_wrt_exp_rec n1 (subst_exp_in_exp e1 x1 e2) (subst_exp_in_exp e1 x1 e3)).
Proof.
apply_mutual_ind exp_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma subst_exp_in_exp_open_exp_wrt_exp_rec :
forall e3 e1 e2 x1 n1,
  lc_exp e1 ->
  subst_exp_in_exp e1 x1 (open_exp_wrt_exp_rec n1 e2 e3) = open_exp_wrt_exp_rec n1 (subst_exp_in_exp e1 x1 e2) (subst_exp_in_exp e1 x1 e3).
Proof.
pose proof subst_exp_in_exp_open_exp_wrt_exp_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_exp_in_exp_open_exp_wrt_exp_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma subst_typ_in_entry_open_entry_wrt_typ_rec_mutual :
(forall et1 A1 A2 X1 n1,
  lc_typ A1 ->
  subst_typ_in_entry A1 X1 (open_entry_wrt_typ_rec n1 A2 et1) = open_entry_wrt_typ_rec n1 (subst_typ_in_typ A1 X1 A2) (subst_typ_in_entry A1 X1 et1)).
Proof.
apply_mutual_ind entry_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma subst_typ_in_entry_open_entry_wrt_typ_rec :
forall et1 A1 A2 X1 n1,
  lc_typ A1 ->
  subst_typ_in_entry A1 X1 (open_entry_wrt_typ_rec n1 A2 et1) = open_entry_wrt_typ_rec n1 (subst_typ_in_typ A1 X1 A2) (subst_typ_in_entry A1 X1 et1).
Proof.
pose proof subst_typ_in_entry_open_entry_wrt_typ_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_typ_in_entry_open_entry_wrt_typ_rec : lngen.

(* end hide *)

Lemma subst_typ_in_typ_open_typ_wrt_typ :
forall A3 A1 A2 X1,
  lc_typ A1 ->
  subst_typ_in_typ A1 X1 (open_typ_wrt_typ A3 A2) = open_typ_wrt_typ (subst_typ_in_typ A1 X1 A3) (subst_typ_in_typ A1 X1 A2).
Proof.
unfold open_typ_wrt_typ; default_simp.
Qed.

#[export] Hint Resolve subst_typ_in_typ_open_typ_wrt_typ : lngen.

Lemma subst_typ_in_exp_open_exp_wrt_typ :
forall e1 A1 A2 X1,
  lc_typ A1 ->
  subst_typ_in_exp A1 X1 (open_exp_wrt_typ e1 A2) = open_exp_wrt_typ (subst_typ_in_exp A1 X1 e1) (subst_typ_in_typ A1 X1 A2).
Proof.
unfold open_exp_wrt_typ; default_simp.
Qed.

#[export] Hint Resolve subst_typ_in_exp_open_exp_wrt_typ : lngen.

Lemma subst_typ_in_exp_open_exp_wrt_exp :
forall e2 A1 e1 X1,
  subst_typ_in_exp A1 X1 (open_exp_wrt_exp e2 e1) = open_exp_wrt_exp (subst_typ_in_exp A1 X1 e2) (subst_typ_in_exp A1 X1 e1).
Proof.
unfold open_exp_wrt_exp; default_simp.
Qed.

#[export] Hint Resolve subst_typ_in_exp_open_exp_wrt_exp : lngen.

Lemma subst_exp_in_exp_open_exp_wrt_typ :
forall e2 e1 A1 x1,
  lc_exp e1 ->
  subst_exp_in_exp e1 x1 (open_exp_wrt_typ e2 A1) = open_exp_wrt_typ (subst_exp_in_exp e1 x1 e2) A1.
Proof.
unfold open_exp_wrt_typ; default_simp.
Qed.

#[export] Hint Resolve subst_exp_in_exp_open_exp_wrt_typ : lngen.

Lemma subst_exp_in_exp_open_exp_wrt_exp :
forall e3 e1 e2 x1,
  lc_exp e1 ->
  subst_exp_in_exp e1 x1 (open_exp_wrt_exp e3 e2) = open_exp_wrt_exp (subst_exp_in_exp e1 x1 e3) (subst_exp_in_exp e1 x1 e2).
Proof.
unfold open_exp_wrt_exp; default_simp.
Qed.

#[export] Hint Resolve subst_exp_in_exp_open_exp_wrt_exp : lngen.

Lemma subst_typ_in_entry_open_entry_wrt_typ :
forall et1 A1 A2 X1,
  lc_typ A1 ->
  subst_typ_in_entry A1 X1 (open_entry_wrt_typ et1 A2) = open_entry_wrt_typ (subst_typ_in_entry A1 X1 et1) (subst_typ_in_typ A1 X1 A2).
Proof.
unfold open_entry_wrt_typ; default_simp.
Qed.

#[export] Hint Resolve subst_typ_in_entry_open_entry_wrt_typ : lngen.

Lemma subst_typ_in_typ_open_typ_wrt_typ_var :
forall A2 A1 X1 X2,
  X1 <> X2 ->
  lc_typ A1 ->
  open_typ_wrt_typ (subst_typ_in_typ A1 X1 A2) (typ_var_f X2) = subst_typ_in_typ A1 X1 (open_typ_wrt_typ A2 (typ_var_f X2)).
Proof.
intros; rewrite subst_typ_in_typ_open_typ_wrt_typ; default_simp.
Qed.

#[export] Hint Resolve subst_typ_in_typ_open_typ_wrt_typ_var : lngen.

Lemma subst_typ_in_exp_open_exp_wrt_typ_var :
forall e1 A1 X1 X2,
  X1 <> X2 ->
  lc_typ A1 ->
  open_exp_wrt_typ (subst_typ_in_exp A1 X1 e1) (typ_var_f X2) = subst_typ_in_exp A1 X1 (open_exp_wrt_typ e1 (typ_var_f X2)).
Proof.
intros; rewrite subst_typ_in_exp_open_exp_wrt_typ; default_simp.
Qed.

#[export] Hint Resolve subst_typ_in_exp_open_exp_wrt_typ_var : lngen.

Lemma subst_typ_in_exp_open_exp_wrt_exp_var :
forall e1 A1 X1 x1,
  open_exp_wrt_exp (subst_typ_in_exp A1 X1 e1) (exp_var_f x1) = subst_typ_in_exp A1 X1 (open_exp_wrt_exp e1 (exp_var_f x1)).
Proof.
intros; rewrite subst_typ_in_exp_open_exp_wrt_exp; default_simp.
Qed.

#[export] Hint Resolve subst_typ_in_exp_open_exp_wrt_exp_var : lngen.

Lemma subst_exp_in_exp_open_exp_wrt_typ_var :
forall e2 e1 x1 X1,
  lc_exp e1 ->
  open_exp_wrt_typ (subst_exp_in_exp e1 x1 e2) (typ_var_f X1) = subst_exp_in_exp e1 x1 (open_exp_wrt_typ e2 (typ_var_f X1)).
Proof.
intros; rewrite subst_exp_in_exp_open_exp_wrt_typ; default_simp.
Qed.

#[export] Hint Resolve subst_exp_in_exp_open_exp_wrt_typ_var : lngen.

Lemma subst_exp_in_exp_open_exp_wrt_exp_var :
forall e2 e1 x1 x2,
  x1 <> x2 ->
  lc_exp e1 ->
  open_exp_wrt_exp (subst_exp_in_exp e1 x1 e2) (exp_var_f x2) = subst_exp_in_exp e1 x1 (open_exp_wrt_exp e2 (exp_var_f x2)).
Proof.
intros; rewrite subst_exp_in_exp_open_exp_wrt_exp; default_simp.
Qed.

#[export] Hint Resolve subst_exp_in_exp_open_exp_wrt_exp_var : lngen.

Lemma subst_typ_in_entry_open_entry_wrt_typ_var :
forall et1 A1 X1 X2,
  X1 <> X2 ->
  lc_typ A1 ->
  open_entry_wrt_typ (subst_typ_in_entry A1 X1 et1) (typ_var_f X2) = subst_typ_in_entry A1 X1 (open_entry_wrt_typ et1 (typ_var_f X2)).
Proof.
intros; rewrite subst_typ_in_entry_open_entry_wrt_typ; default_simp.
Qed.

#[export] Hint Resolve subst_typ_in_entry_open_entry_wrt_typ_var : lngen.

(* begin hide *)

Lemma subst_typ_in_typ_spec_rec_mutual :
(forall A1 A2 X1 n1,
  subst_typ_in_typ A2 X1 A1 = open_typ_wrt_typ_rec n1 A2 (close_typ_wrt_typ_rec n1 X1 A1)).
Proof.
apply_mutual_ind typ_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma subst_typ_in_typ_spec_rec :
forall A1 A2 X1 n1,
  subst_typ_in_typ A2 X1 A1 = open_typ_wrt_typ_rec n1 A2 (close_typ_wrt_typ_rec n1 X1 A1).
Proof.
pose proof subst_typ_in_typ_spec_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_typ_in_typ_spec_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma subst_typ_in_exp_spec_rec_mutual :
(forall e1 A1 X1 n1,
  subst_typ_in_exp A1 X1 e1 = open_exp_wrt_typ_rec n1 A1 (close_exp_wrt_typ_rec n1 X1 e1)).
Proof.
apply_mutual_ind exp_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma subst_typ_in_exp_spec_rec :
forall e1 A1 X1 n1,
  subst_typ_in_exp A1 X1 e1 = open_exp_wrt_typ_rec n1 A1 (close_exp_wrt_typ_rec n1 X1 e1).
Proof.
pose proof subst_typ_in_exp_spec_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_typ_in_exp_spec_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma subst_exp_in_exp_spec_rec_mutual :
(forall e1 e2 x1 n1,
  subst_exp_in_exp e2 x1 e1 = open_exp_wrt_exp_rec n1 e2 (close_exp_wrt_exp_rec n1 x1 e1)).
Proof.
apply_mutual_ind exp_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma subst_exp_in_exp_spec_rec :
forall e1 e2 x1 n1,
  subst_exp_in_exp e2 x1 e1 = open_exp_wrt_exp_rec n1 e2 (close_exp_wrt_exp_rec n1 x1 e1).
Proof.
pose proof subst_exp_in_exp_spec_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_exp_in_exp_spec_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma subst_typ_in_entry_spec_rec_mutual :
(forall et1 A1 X1 n1,
  subst_typ_in_entry A1 X1 et1 = open_entry_wrt_typ_rec n1 A1 (close_entry_wrt_typ_rec n1 X1 et1)).
Proof.
apply_mutual_ind entry_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma subst_typ_in_entry_spec_rec :
forall et1 A1 X1 n1,
  subst_typ_in_entry A1 X1 et1 = open_entry_wrt_typ_rec n1 A1 (close_entry_wrt_typ_rec n1 X1 et1).
Proof.
pose proof subst_typ_in_entry_spec_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_typ_in_entry_spec_rec : lngen.

(* end hide *)

Lemma subst_typ_in_typ_spec :
forall A1 A2 X1,
  subst_typ_in_typ A2 X1 A1 = open_typ_wrt_typ (close_typ_wrt_typ X1 A1) A2.
Proof.
unfold close_typ_wrt_typ; unfold open_typ_wrt_typ; default_simp.
Qed.

#[export] Hint Resolve subst_typ_in_typ_spec : lngen.

Lemma subst_typ_in_exp_spec :
forall e1 A1 X1,
  subst_typ_in_exp A1 X1 e1 = open_exp_wrt_typ (close_exp_wrt_typ X1 e1) A1.
Proof.
unfold close_exp_wrt_typ; unfold open_exp_wrt_typ; default_simp.
Qed.

#[export] Hint Resolve subst_typ_in_exp_spec : lngen.

Lemma subst_exp_in_exp_spec :
forall e1 e2 x1,
  subst_exp_in_exp e2 x1 e1 = open_exp_wrt_exp (close_exp_wrt_exp x1 e1) e2.
Proof.
unfold close_exp_wrt_exp; unfold open_exp_wrt_exp; default_simp.
Qed.

#[export] Hint Resolve subst_exp_in_exp_spec : lngen.

Lemma subst_typ_in_entry_spec :
forall et1 A1 X1,
  subst_typ_in_entry A1 X1 et1 = open_entry_wrt_typ (close_entry_wrt_typ X1 et1) A1.
Proof.
unfold close_entry_wrt_typ; unfold open_entry_wrt_typ; default_simp.
Qed.

#[export] Hint Resolve subst_typ_in_entry_spec : lngen.

(* begin hide *)

Lemma subst_typ_in_typ_subst_typ_in_typ_mutual :
(forall A1 A2 A3 X2 X1,
  X2 `notin` tvar_in_typ A2 ->
  X2 <> X1 ->
  subst_typ_in_typ A2 X1 (subst_typ_in_typ A3 X2 A1) = subst_typ_in_typ (subst_typ_in_typ A2 X1 A3) X2 (subst_typ_in_typ A2 X1 A1)).
Proof.
apply_mutual_ind typ_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_typ_in_typ_subst_typ_in_typ :
forall A1 A2 A3 X2 X1,
  X2 `notin` tvar_in_typ A2 ->
  X2 <> X1 ->
  subst_typ_in_typ A2 X1 (subst_typ_in_typ A3 X2 A1) = subst_typ_in_typ (subst_typ_in_typ A2 X1 A3) X2 (subst_typ_in_typ A2 X1 A1).
Proof.
pose proof subst_typ_in_typ_subst_typ_in_typ_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_typ_in_typ_subst_typ_in_typ : lngen.

(* begin hide *)

Lemma subst_typ_in_exp_subst_typ_in_exp_mutual :
(forall e1 A1 A2 X2 X1,
  X2 `notin` tvar_in_typ A1 ->
  X2 <> X1 ->
  subst_typ_in_exp A1 X1 (subst_typ_in_exp A2 X2 e1) = subst_typ_in_exp (subst_typ_in_typ A1 X1 A2) X2 (subst_typ_in_exp A1 X1 e1)).
Proof.
apply_mutual_ind exp_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_typ_in_exp_subst_typ_in_exp :
forall e1 A1 A2 X2 X1,
  X2 `notin` tvar_in_typ A1 ->
  X2 <> X1 ->
  subst_typ_in_exp A1 X1 (subst_typ_in_exp A2 X2 e1) = subst_typ_in_exp (subst_typ_in_typ A1 X1 A2) X2 (subst_typ_in_exp A1 X1 e1).
Proof.
pose proof subst_typ_in_exp_subst_typ_in_exp_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_typ_in_exp_subst_typ_in_exp : lngen.

(* begin hide *)

Lemma subst_typ_in_exp_subst_exp_in_exp_mutual :
(forall e1 A1 e2 x1 X1,
  subst_typ_in_exp A1 X1 (subst_exp_in_exp e2 x1 e1) = subst_exp_in_exp (subst_typ_in_exp A1 X1 e2) x1 (subst_typ_in_exp A1 X1 e1)).
Proof.
apply_mutual_ind exp_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_typ_in_exp_subst_exp_in_exp :
forall e1 A1 e2 x1 X1,
  subst_typ_in_exp A1 X1 (subst_exp_in_exp e2 x1 e1) = subst_exp_in_exp (subst_typ_in_exp A1 X1 e2) x1 (subst_typ_in_exp A1 X1 e1).
Proof.
pose proof subst_typ_in_exp_subst_exp_in_exp_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_typ_in_exp_subst_exp_in_exp : lngen.

(* begin hide *)

Lemma subst_exp_in_exp_subst_typ_in_exp_mutual :
(forall e1 e2 A1 X1 x1,
  X1 `notin` tvar_in_exp e2 ->
  subst_exp_in_exp e2 x1 (subst_typ_in_exp A1 X1 e1) = subst_typ_in_exp A1 X1 (subst_exp_in_exp e2 x1 e1)).
Proof.
apply_mutual_ind exp_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_exp_in_exp_subst_typ_in_exp :
forall e1 e2 A1 X1 x1,
  X1 `notin` tvar_in_exp e2 ->
  subst_exp_in_exp e2 x1 (subst_typ_in_exp A1 X1 e1) = subst_typ_in_exp A1 X1 (subst_exp_in_exp e2 x1 e1).
Proof.
pose proof subst_exp_in_exp_subst_typ_in_exp_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_exp_in_exp_subst_typ_in_exp : lngen.

(* begin hide *)

Lemma subst_exp_in_exp_subst_exp_in_exp_mutual :
(forall e1 e2 e3 x2 x1,
  x2 `notin` var_in_exp e2 ->
  x2 <> x1 ->
  subst_exp_in_exp e2 x1 (subst_exp_in_exp e3 x2 e1) = subst_exp_in_exp (subst_exp_in_exp e2 x1 e3) x2 (subst_exp_in_exp e2 x1 e1)).
Proof.
apply_mutual_ind exp_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_exp_in_exp_subst_exp_in_exp :
forall e1 e2 e3 x2 x1,
  x2 `notin` var_in_exp e2 ->
  x2 <> x1 ->
  subst_exp_in_exp e2 x1 (subst_exp_in_exp e3 x2 e1) = subst_exp_in_exp (subst_exp_in_exp e2 x1 e3) x2 (subst_exp_in_exp e2 x1 e1).
Proof.
pose proof subst_exp_in_exp_subst_exp_in_exp_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_exp_in_exp_subst_exp_in_exp : lngen.

(* begin hide *)

Lemma subst_typ_in_entry_subst_typ_in_entry_mutual :
(forall et1 A1 A2 X2 X1,
  X2 `notin` tvar_in_typ A1 ->
  X2 <> X1 ->
  subst_typ_in_entry A1 X1 (subst_typ_in_entry A2 X2 et1) = subst_typ_in_entry (subst_typ_in_typ A1 X1 A2) X2 (subst_typ_in_entry A1 X1 et1)).
Proof.
apply_mutual_ind entry_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_typ_in_entry_subst_typ_in_entry :
forall et1 A1 A2 X2 X1,
  X2 `notin` tvar_in_typ A1 ->
  X2 <> X1 ->
  subst_typ_in_entry A1 X1 (subst_typ_in_entry A2 X2 et1) = subst_typ_in_entry (subst_typ_in_typ A1 X1 A2) X2 (subst_typ_in_entry A1 X1 et1).
Proof.
pose proof subst_typ_in_entry_subst_typ_in_entry_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_typ_in_entry_subst_typ_in_entry : lngen.

(* begin hide *)

Lemma subst_typ_in_typ_close_typ_wrt_typ_rec_open_typ_wrt_typ_rec_mutual :
(forall A2 A1 X1 X2 n1,
  X2 `notin` tvar_in_typ A2 ->
  X2 `notin` tvar_in_typ A1 ->
  X2 <> X1 ->
  degree_typ_wrt_typ n1 A1 ->
  subst_typ_in_typ A1 X1 A2 = close_typ_wrt_typ_rec n1 X2 (subst_typ_in_typ A1 X1 (open_typ_wrt_typ_rec n1 (typ_var_f X2) A2))).
Proof.
apply_mutual_ind typ_mutrec;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma subst_typ_in_typ_close_typ_wrt_typ_rec_open_typ_wrt_typ_rec :
forall A2 A1 X1 X2 n1,
  X2 `notin` tvar_in_typ A2 ->
  X2 `notin` tvar_in_typ A1 ->
  X2 <> X1 ->
  degree_typ_wrt_typ n1 A1 ->
  subst_typ_in_typ A1 X1 A2 = close_typ_wrt_typ_rec n1 X2 (subst_typ_in_typ A1 X1 (open_typ_wrt_typ_rec n1 (typ_var_f X2) A2)).
Proof.
pose proof subst_typ_in_typ_close_typ_wrt_typ_rec_open_typ_wrt_typ_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_typ_in_typ_close_typ_wrt_typ_rec_open_typ_wrt_typ_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma subst_typ_in_exp_close_exp_wrt_typ_rec_open_exp_wrt_typ_rec_mutual :
(forall e1 A1 X1 X2 n1,
  X2 `notin` tvar_in_exp e1 ->
  X2 `notin` tvar_in_typ A1 ->
  X2 <> X1 ->
  degree_typ_wrt_typ n1 A1 ->
  subst_typ_in_exp A1 X1 e1 = close_exp_wrt_typ_rec n1 X2 (subst_typ_in_exp A1 X1 (open_exp_wrt_typ_rec n1 (typ_var_f X2) e1))).
Proof.
apply_mutual_ind exp_mutrec;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma subst_typ_in_exp_close_exp_wrt_typ_rec_open_exp_wrt_typ_rec :
forall e1 A1 X1 X2 n1,
  X2 `notin` tvar_in_exp e1 ->
  X2 `notin` tvar_in_typ A1 ->
  X2 <> X1 ->
  degree_typ_wrt_typ n1 A1 ->
  subst_typ_in_exp A1 X1 e1 = close_exp_wrt_typ_rec n1 X2 (subst_typ_in_exp A1 X1 (open_exp_wrt_typ_rec n1 (typ_var_f X2) e1)).
Proof.
pose proof subst_typ_in_exp_close_exp_wrt_typ_rec_open_exp_wrt_typ_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_typ_in_exp_close_exp_wrt_typ_rec_open_exp_wrt_typ_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma subst_typ_in_exp_close_exp_wrt_exp_rec_open_exp_wrt_exp_rec_mutual :
(forall e1 A1 X1 x1 n1,
  x1 `notin` var_in_exp e1 ->
  subst_typ_in_exp A1 X1 e1 = close_exp_wrt_exp_rec n1 x1 (subst_typ_in_exp A1 X1 (open_exp_wrt_exp_rec n1 (exp_var_f x1) e1))).
Proof.
apply_mutual_ind exp_mutrec;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma subst_typ_in_exp_close_exp_wrt_exp_rec_open_exp_wrt_exp_rec :
forall e1 A1 X1 x1 n1,
  x1 `notin` var_in_exp e1 ->
  subst_typ_in_exp A1 X1 e1 = close_exp_wrt_exp_rec n1 x1 (subst_typ_in_exp A1 X1 (open_exp_wrt_exp_rec n1 (exp_var_f x1) e1)).
Proof.
pose proof subst_typ_in_exp_close_exp_wrt_exp_rec_open_exp_wrt_exp_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_typ_in_exp_close_exp_wrt_exp_rec_open_exp_wrt_exp_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma subst_exp_in_exp_close_exp_wrt_typ_rec_open_exp_wrt_typ_rec_mutual :
(forall e2 e1 x1 X1 n1,
  X1 `notin` tvar_in_exp e2 ->
  X1 `notin` tvar_in_exp e1 ->
  degree_exp_wrt_typ n1 e1 ->
  subst_exp_in_exp e1 x1 e2 = close_exp_wrt_typ_rec n1 X1 (subst_exp_in_exp e1 x1 (open_exp_wrt_typ_rec n1 (typ_var_f X1) e2))).
Proof.
apply_mutual_ind exp_mutrec;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma subst_exp_in_exp_close_exp_wrt_typ_rec_open_exp_wrt_typ_rec :
forall e2 e1 x1 X1 n1,
  X1 `notin` tvar_in_exp e2 ->
  X1 `notin` tvar_in_exp e1 ->
  degree_exp_wrt_typ n1 e1 ->
  subst_exp_in_exp e1 x1 e2 = close_exp_wrt_typ_rec n1 X1 (subst_exp_in_exp e1 x1 (open_exp_wrt_typ_rec n1 (typ_var_f X1) e2)).
Proof.
pose proof subst_exp_in_exp_close_exp_wrt_typ_rec_open_exp_wrt_typ_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_exp_in_exp_close_exp_wrt_typ_rec_open_exp_wrt_typ_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma subst_exp_in_exp_close_exp_wrt_exp_rec_open_exp_wrt_exp_rec_mutual :
(forall e2 e1 x1 x2 n1,
  x2 `notin` var_in_exp e2 ->
  x2 `notin` var_in_exp e1 ->
  x2 <> x1 ->
  degree_exp_wrt_exp n1 e1 ->
  subst_exp_in_exp e1 x1 e2 = close_exp_wrt_exp_rec n1 x2 (subst_exp_in_exp e1 x1 (open_exp_wrt_exp_rec n1 (exp_var_f x2) e2))).
Proof.
apply_mutual_ind exp_mutrec;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma subst_exp_in_exp_close_exp_wrt_exp_rec_open_exp_wrt_exp_rec :
forall e2 e1 x1 x2 n1,
  x2 `notin` var_in_exp e2 ->
  x2 `notin` var_in_exp e1 ->
  x2 <> x1 ->
  degree_exp_wrt_exp n1 e1 ->
  subst_exp_in_exp e1 x1 e2 = close_exp_wrt_exp_rec n1 x2 (subst_exp_in_exp e1 x1 (open_exp_wrt_exp_rec n1 (exp_var_f x2) e2)).
Proof.
pose proof subst_exp_in_exp_close_exp_wrt_exp_rec_open_exp_wrt_exp_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_exp_in_exp_close_exp_wrt_exp_rec_open_exp_wrt_exp_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma subst_typ_in_entry_close_entry_wrt_typ_rec_open_entry_wrt_typ_rec_mutual :
(forall et1 A1 X1 X2 n1,
  X2 `notin` tvar_in_entry et1 ->
  X2 `notin` tvar_in_typ A1 ->
  X2 <> X1 ->
  degree_typ_wrt_typ n1 A1 ->
  subst_typ_in_entry A1 X1 et1 = close_entry_wrt_typ_rec n1 X2 (subst_typ_in_entry A1 X1 (open_entry_wrt_typ_rec n1 (typ_var_f X2) et1))).
Proof.
apply_mutual_ind entry_mutrec;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma subst_typ_in_entry_close_entry_wrt_typ_rec_open_entry_wrt_typ_rec :
forall et1 A1 X1 X2 n1,
  X2 `notin` tvar_in_entry et1 ->
  X2 `notin` tvar_in_typ A1 ->
  X2 <> X1 ->
  degree_typ_wrt_typ n1 A1 ->
  subst_typ_in_entry A1 X1 et1 = close_entry_wrt_typ_rec n1 X2 (subst_typ_in_entry A1 X1 (open_entry_wrt_typ_rec n1 (typ_var_f X2) et1)).
Proof.
pose proof subst_typ_in_entry_close_entry_wrt_typ_rec_open_entry_wrt_typ_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_typ_in_entry_close_entry_wrt_typ_rec_open_entry_wrt_typ_rec : lngen.

(* end hide *)

Lemma subst_typ_in_typ_close_typ_wrt_typ_open_typ_wrt_typ :
forall A2 A1 X1 X2,
  X2 `notin` tvar_in_typ A2 ->
  X2 `notin` tvar_in_typ A1 ->
  X2 <> X1 ->
  lc_typ A1 ->
  subst_typ_in_typ A1 X1 A2 = close_typ_wrt_typ X2 (subst_typ_in_typ A1 X1 (open_typ_wrt_typ A2 (typ_var_f X2))).
Proof.
unfold close_typ_wrt_typ; unfold open_typ_wrt_typ; default_simp.
Qed.

#[export] Hint Resolve subst_typ_in_typ_close_typ_wrt_typ_open_typ_wrt_typ : lngen.

Lemma subst_typ_in_exp_close_exp_wrt_typ_open_exp_wrt_typ :
forall e1 A1 X1 X2,
  X2 `notin` tvar_in_exp e1 ->
  X2 `notin` tvar_in_typ A1 ->
  X2 <> X1 ->
  lc_typ A1 ->
  subst_typ_in_exp A1 X1 e1 = close_exp_wrt_typ X2 (subst_typ_in_exp A1 X1 (open_exp_wrt_typ e1 (typ_var_f X2))).
Proof.
unfold close_exp_wrt_typ; unfold open_exp_wrt_typ; default_simp.
Qed.

#[export] Hint Resolve subst_typ_in_exp_close_exp_wrt_typ_open_exp_wrt_typ : lngen.

Lemma subst_typ_in_exp_close_exp_wrt_exp_open_exp_wrt_exp :
forall e1 A1 X1 x1,
  x1 `notin` var_in_exp e1 ->
  lc_typ A1 ->
  subst_typ_in_exp A1 X1 e1 = close_exp_wrt_exp x1 (subst_typ_in_exp A1 X1 (open_exp_wrt_exp e1 (exp_var_f x1))).
Proof.
unfold close_exp_wrt_exp; unfold open_exp_wrt_exp; default_simp.
Qed.

#[export] Hint Resolve subst_typ_in_exp_close_exp_wrt_exp_open_exp_wrt_exp : lngen.

Lemma subst_exp_in_exp_close_exp_wrt_typ_open_exp_wrt_typ :
forall e2 e1 x1 X1,
  X1 `notin` tvar_in_exp e2 ->
  X1 `notin` tvar_in_exp e1 ->
  lc_exp e1 ->
  subst_exp_in_exp e1 x1 e2 = close_exp_wrt_typ X1 (subst_exp_in_exp e1 x1 (open_exp_wrt_typ e2 (typ_var_f X1))).
Proof.
unfold close_exp_wrt_typ; unfold open_exp_wrt_typ; default_simp.
Qed.

#[export] Hint Resolve subst_exp_in_exp_close_exp_wrt_typ_open_exp_wrt_typ : lngen.

Lemma subst_exp_in_exp_close_exp_wrt_exp_open_exp_wrt_exp :
forall e2 e1 x1 x2,
  x2 `notin` var_in_exp e2 ->
  x2 `notin` var_in_exp e1 ->
  x2 <> x1 ->
  lc_exp e1 ->
  subst_exp_in_exp e1 x1 e2 = close_exp_wrt_exp x2 (subst_exp_in_exp e1 x1 (open_exp_wrt_exp e2 (exp_var_f x2))).
Proof.
unfold close_exp_wrt_exp; unfold open_exp_wrt_exp; default_simp.
Qed.

#[export] Hint Resolve subst_exp_in_exp_close_exp_wrt_exp_open_exp_wrt_exp : lngen.

Lemma subst_typ_in_entry_close_entry_wrt_typ_open_entry_wrt_typ :
forall et1 A1 X1 X2,
  X2 `notin` tvar_in_entry et1 ->
  X2 `notin` tvar_in_typ A1 ->
  X2 <> X1 ->
  lc_typ A1 ->
  subst_typ_in_entry A1 X1 et1 = close_entry_wrt_typ X2 (subst_typ_in_entry A1 X1 (open_entry_wrt_typ et1 (typ_var_f X2))).
Proof.
unfold close_entry_wrt_typ; unfold open_entry_wrt_typ; default_simp.
Qed.

#[export] Hint Resolve subst_typ_in_entry_close_entry_wrt_typ_open_entry_wrt_typ : lngen.

Lemma subst_typ_in_typ_typ_all :
forall X2 B1 A2 A1 X1,
  lc_typ A1 ->
  X2 `notin` tvar_in_typ A1 `union` tvar_in_typ A2 `union` singleton X1 ->
  subst_typ_in_typ A1 X1 (typ_all B1 A2) = typ_all (subst_typ_in_typ A1 X1 B1) (close_typ_wrt_typ X2 (subst_typ_in_typ A1 X1 (open_typ_wrt_typ A2 (typ_var_f X2)))).
Proof.
default_simp.
Qed.

#[export] Hint Resolve subst_typ_in_typ_typ_all : lngen.

Lemma subst_typ_in_exp_exp_abs :
forall x1 A2 e1 A1 X1,
  lc_typ A1 ->
  x1 `notin` var_in_exp e1 ->
  subst_typ_in_exp A1 X1 (exp_abs A2 e1) = exp_abs (subst_typ_in_typ A1 X1 A2) (close_exp_wrt_exp x1 (subst_typ_in_exp A1 X1 (open_exp_wrt_exp e1 (exp_var_f x1)))).
Proof.
default_simp.
Qed.

#[export] Hint Resolve subst_typ_in_exp_exp_abs : lngen.

Lemma subst_typ_in_exp_exp_tabs :
forall X2 A2 e1 A1 X1,
  lc_typ A1 ->
  X2 `notin` tvar_in_typ A1 `union` tvar_in_exp e1 `union` singleton X1 ->
  subst_typ_in_exp A1 X1 (exp_tabs A2 e1) = exp_tabs (subst_typ_in_typ A1 X1 A2) (close_exp_wrt_typ X2 (subst_typ_in_exp A1 X1 (open_exp_wrt_typ e1 (typ_var_f X2)))).
Proof.
default_simp.
Qed.

#[export] Hint Resolve subst_typ_in_exp_exp_tabs : lngen.

Lemma subst_exp_in_exp_exp_abs :
forall x2 A1 e2 e1 x1,
  lc_exp e1 ->
  x2 `notin` var_in_exp e1 `union` var_in_exp e2 `union` singleton x1 ->
  subst_exp_in_exp e1 x1 (exp_abs A1 e2) = exp_abs (A1) (close_exp_wrt_exp x2 (subst_exp_in_exp e1 x1 (open_exp_wrt_exp e2 (exp_var_f x2)))).
Proof.
default_simp.
Qed.

#[export] Hint Resolve subst_exp_in_exp_exp_abs : lngen.

Lemma subst_exp_in_exp_exp_tabs :
forall X1 A1 e2 e1 x1,
  lc_exp e1 ->
  X1 `notin` tvar_in_exp e1 `union` tvar_in_exp e2 ->
  subst_exp_in_exp e1 x1 (exp_tabs A1 e2) = exp_tabs (A1) (close_exp_wrt_typ X1 (subst_exp_in_exp e1 x1 (open_exp_wrt_typ e2 (typ_var_f X1)))).
Proof.
default_simp.
Qed.

#[export] Hint Resolve subst_exp_in_exp_exp_tabs : lngen.

(* begin hide *)

Lemma subst_typ_in_typ_intro_rec_mutual :
(forall A1 X1 A2 n1,
  X1 `notin` tvar_in_typ A1 ->
  open_typ_wrt_typ_rec n1 A2 A1 = subst_typ_in_typ A2 X1 (open_typ_wrt_typ_rec n1 (typ_var_f X1) A1)).
Proof.
apply_mutual_ind typ_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_typ_in_typ_intro_rec :
forall A1 X1 A2 n1,
  X1 `notin` tvar_in_typ A1 ->
  open_typ_wrt_typ_rec n1 A2 A1 = subst_typ_in_typ A2 X1 (open_typ_wrt_typ_rec n1 (typ_var_f X1) A1).
Proof.
pose proof subst_typ_in_typ_intro_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_typ_in_typ_intro_rec : lngen.
#[export] Hint Rewrite subst_typ_in_typ_intro_rec using solve [auto] : lngen.

(* begin hide *)

Lemma subst_typ_in_exp_intro_rec_mutual :
(forall e1 X1 A1 n1,
  X1 `notin` tvar_in_exp e1 ->
  open_exp_wrt_typ_rec n1 A1 e1 = subst_typ_in_exp A1 X1 (open_exp_wrt_typ_rec n1 (typ_var_f X1) e1)).
Proof.
apply_mutual_ind exp_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_typ_in_exp_intro_rec :
forall e1 X1 A1 n1,
  X1 `notin` tvar_in_exp e1 ->
  open_exp_wrt_typ_rec n1 A1 e1 = subst_typ_in_exp A1 X1 (open_exp_wrt_typ_rec n1 (typ_var_f X1) e1).
Proof.
pose proof subst_typ_in_exp_intro_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_typ_in_exp_intro_rec : lngen.
#[export] Hint Rewrite subst_typ_in_exp_intro_rec using solve [auto] : lngen.

(* begin hide *)

Lemma subst_exp_in_exp_intro_rec_mutual :
(forall e1 x1 e2 n1,
  x1 `notin` var_in_exp e1 ->
  open_exp_wrt_exp_rec n1 e2 e1 = subst_exp_in_exp e2 x1 (open_exp_wrt_exp_rec n1 (exp_var_f x1) e1)).
Proof.
apply_mutual_ind exp_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_exp_in_exp_intro_rec :
forall e1 x1 e2 n1,
  x1 `notin` var_in_exp e1 ->
  open_exp_wrt_exp_rec n1 e2 e1 = subst_exp_in_exp e2 x1 (open_exp_wrt_exp_rec n1 (exp_var_f x1) e1).
Proof.
pose proof subst_exp_in_exp_intro_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_exp_in_exp_intro_rec : lngen.
#[export] Hint Rewrite subst_exp_in_exp_intro_rec using solve [auto] : lngen.

(* begin hide *)

Lemma subst_typ_in_entry_intro_rec_mutual :
(forall et1 X1 A1 n1,
  X1 `notin` tvar_in_entry et1 ->
  open_entry_wrt_typ_rec n1 A1 et1 = subst_typ_in_entry A1 X1 (open_entry_wrt_typ_rec n1 (typ_var_f X1) et1)).
Proof.
apply_mutual_ind entry_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_typ_in_entry_intro_rec :
forall et1 X1 A1 n1,
  X1 `notin` tvar_in_entry et1 ->
  open_entry_wrt_typ_rec n1 A1 et1 = subst_typ_in_entry A1 X1 (open_entry_wrt_typ_rec n1 (typ_var_f X1) et1).
Proof.
pose proof subst_typ_in_entry_intro_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_typ_in_entry_intro_rec : lngen.
#[export] Hint Rewrite subst_typ_in_entry_intro_rec using solve [auto] : lngen.

Lemma subst_typ_in_typ_intro :
forall X1 A1 A2,
  X1 `notin` tvar_in_typ A1 ->
  open_typ_wrt_typ A1 A2 = subst_typ_in_typ A2 X1 (open_typ_wrt_typ A1 (typ_var_f X1)).
Proof.
unfold open_typ_wrt_typ; default_simp.
Qed.

#[export] Hint Resolve subst_typ_in_typ_intro : lngen.

Lemma subst_typ_in_exp_intro :
forall X1 e1 A1,
  X1 `notin` tvar_in_exp e1 ->
  open_exp_wrt_typ e1 A1 = subst_typ_in_exp A1 X1 (open_exp_wrt_typ e1 (typ_var_f X1)).
Proof.
unfold open_exp_wrt_typ; default_simp.
Qed.

#[export] Hint Resolve subst_typ_in_exp_intro : lngen.

Lemma subst_exp_in_exp_intro :
forall x1 e1 e2,
  x1 `notin` var_in_exp e1 ->
  open_exp_wrt_exp e1 e2 = subst_exp_in_exp e2 x1 (open_exp_wrt_exp e1 (exp_var_f x1)).
Proof.
unfold open_exp_wrt_exp; default_simp.
Qed.

#[export] Hint Resolve subst_exp_in_exp_intro : lngen.

Lemma subst_typ_in_entry_intro :
forall X1 et1 A1,
  X1 `notin` tvar_in_entry et1 ->
  open_entry_wrt_typ et1 A1 = subst_typ_in_entry A1 X1 (open_entry_wrt_typ et1 (typ_var_f X1)).
Proof.
unfold open_entry_wrt_typ; default_simp.
Qed.

#[export] Hint Resolve subst_typ_in_entry_intro : lngen.


(* *********************************************************************** *)
(** * "Restore" tactics *)

Ltac default_auto ::= auto; tauto.
Ltac default_autorewrite ::= fail.
