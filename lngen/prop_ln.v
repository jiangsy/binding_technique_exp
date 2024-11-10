Require Import Coq.Arith.Wf_nat.
Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.Program.Equality.

Require Export Metalib.Metatheory.
Require Export Metalib.LibLNgen.

Require Export binder.lngen.def.

Local Set Warnings "-non-recursive". 

(** NOTE: Auxiliary theorems are hidden in generated documentation.
    In general, there is a [_rec] version of every lemma involving
    [open] and [close]. *)


(* *********************************************************************** *)
(** * Induction principles for nonterminals *)

Scheme ftyp_ind' := Induction for ftyp Sort Prop.

Combined Scheme ftyp_mutind from ftyp_ind'.

Scheme ftyp_rec' := Induction for ftyp Sort Set.

Combined Scheme ftyp_mutrec from ftyp_rec'.

Scheme fexp_ind' := Induction for fexp Sort Prop.

Combined Scheme fexp_mutind from fexp_ind'.

Scheme fexp_rec' := Induction for fexp Sort Set.

Combined Scheme fexp_mutrec from fexp_rec'.


(* *********************************************************************** *)
(** * Close *)

Fixpoint close_ftyp_wrt_ftyp_rec (n1 : nat) (X1 : typvar) (A1 : ftyp) {struct A1} : ftyp :=
  match A1 with
    | ftyp_var_f X2 => if (X1 == X2) then (ftyp_var_b n1) else (ftyp_var_f X2)
    | ftyp_var_b n2 => if (lt_ge_dec n2 n1) then (ftyp_var_b n2) else (ftyp_var_b (S n2))
    | ftyp_arr A2 A3 => ftyp_arr (close_ftyp_wrt_ftyp_rec n1 X1 A2) (close_ftyp_wrt_ftyp_rec n1 X1 A3)
    | ftyp_all A2 => ftyp_all (close_ftyp_wrt_ftyp_rec (S n1) X1 A2)
  end.

Definition close_ftyp_wrt_ftyp X1 A1 := close_ftyp_wrt_ftyp_rec 0 X1 A1.

Fixpoint close_fexp_wrt_ftyp_rec (n1 : nat) (X1 : typvar) (e1 : fexp) {struct e1} : fexp :=
  match e1 with
    | fexp_var_f x1 => fexp_var_f x1
    | fexp_var_b n2 => fexp_var_b n2
    | fexp_abs A1 e2 => fexp_abs (close_ftyp_wrt_ftyp_rec n1 X1 A1) (close_fexp_wrt_ftyp_rec n1 X1 e2)
    | fexp_app e2 e3 => fexp_app (close_fexp_wrt_ftyp_rec n1 X1 e2) (close_fexp_wrt_ftyp_rec n1 X1 e3)
    | fexp_tabs e2 => fexp_tabs (close_fexp_wrt_ftyp_rec (S n1) X1 e2)
    | fexp_tapp e2 A1 => fexp_tapp (close_fexp_wrt_ftyp_rec n1 X1 e2) (close_ftyp_wrt_ftyp_rec n1 X1 A1)
  end.

Fixpoint close_fexp_wrt_fexp_rec (n1 : nat) (x1 : expvar) (e1 : fexp) {struct e1} : fexp :=
  match e1 with
    | fexp_var_f x2 => if (x1 == x2) then (fexp_var_b n1) else (fexp_var_f x2)
    | fexp_var_b n2 => if (lt_ge_dec n2 n1) then (fexp_var_b n2) else (fexp_var_b (S n2))
    | fexp_abs A1 e2 => fexp_abs A1 (close_fexp_wrt_fexp_rec (S n1) x1 e2)
    | fexp_app e2 e3 => fexp_app (close_fexp_wrt_fexp_rec n1 x1 e2) (close_fexp_wrt_fexp_rec n1 x1 e3)
    | fexp_tabs e2 => fexp_tabs (close_fexp_wrt_fexp_rec n1 x1 e2)
    | fexp_tapp e2 A1 => fexp_tapp (close_fexp_wrt_fexp_rec n1 x1 e2) A1
  end.

Definition close_fexp_wrt_ftyp X1 e1 := close_fexp_wrt_ftyp_rec 0 X1 e1.

Definition close_fexp_wrt_fexp x1 e1 := close_fexp_wrt_fexp_rec 0 x1 e1.


(* *********************************************************************** *)
(** * Size *)

Fixpoint size_ftyp (A1 : ftyp) {struct A1} : nat :=
  match A1 with
    | ftyp_var_f X1 => 1
    | ftyp_var_b n1 => 1
    | ftyp_arr A2 A3 => 1 + (size_ftyp A2) + (size_ftyp A3)
    | ftyp_all A2 => 1 + (size_ftyp A2)
  end.

Fixpoint size_fexp (e1 : fexp) {struct e1} : nat :=
  match e1 with
    | fexp_var_f x1 => 1
    | fexp_var_b n1 => 1
    | fexp_abs A1 e2 => 1 + (size_ftyp A1) + (size_fexp e2)
    | fexp_app e2 e3 => 1 + (size_fexp e2) + (size_fexp e3)
    | fexp_tabs e2 => 1 + (size_fexp e2)
    | fexp_tapp e2 A1 => 1 + (size_fexp e2) + (size_ftyp A1)
  end.


(* *********************************************************************** *)
(** * Degree *)

(** These define only an upper bound, not a strict upper bound. *)

Inductive degree_ftyp_wrt_ftyp : nat -> ftyp -> Prop :=
  | degree_wrt_ftyp_ftyp_var_f : forall n1 X1,
    degree_ftyp_wrt_ftyp n1 (ftyp_var_f X1)
  | degree_wrt_ftyp_ftyp_var_b : forall n1 n2,
    lt n2 n1 ->
    degree_ftyp_wrt_ftyp n1 (ftyp_var_b n2)
  | degree_wrt_ftyp_ftyp_arr : forall n1 A1 A2,
    degree_ftyp_wrt_ftyp n1 A1 ->
    degree_ftyp_wrt_ftyp n1 A2 ->
    degree_ftyp_wrt_ftyp n1 (ftyp_arr A1 A2)
  | degree_wrt_ftyp_ftyp_all : forall n1 A1,
    degree_ftyp_wrt_ftyp (S n1) A1 ->
    degree_ftyp_wrt_ftyp n1 (ftyp_all A1).

Scheme degree_ftyp_wrt_ftyp_ind' := Induction for degree_ftyp_wrt_ftyp Sort Prop.

Combined Scheme degree_ftyp_wrt_ftyp_mutind from degree_ftyp_wrt_ftyp_ind'.

#[export] Hint Constructors degree_ftyp_wrt_ftyp : core lngen.

Inductive degree_fexp_wrt_ftyp : nat -> fexp -> Prop :=
  | degree_wrt_ftyp_fexp_var_f : forall n1 x1,
    degree_fexp_wrt_ftyp n1 (fexp_var_f x1)
  | degree_wrt_ftyp_fexp_var_b : forall n1 n2,
    degree_fexp_wrt_ftyp n1 (fexp_var_b n2)
  | degree_wrt_ftyp_fexp_abs : forall n1 A1 e1,
    degree_ftyp_wrt_ftyp n1 A1 ->
    degree_fexp_wrt_ftyp n1 e1 ->
    degree_fexp_wrt_ftyp n1 (fexp_abs A1 e1)
  | degree_wrt_ftyp_fexp_app : forall n1 e1 e2,
    degree_fexp_wrt_ftyp n1 e1 ->
    degree_fexp_wrt_ftyp n1 e2 ->
    degree_fexp_wrt_ftyp n1 (fexp_app e1 e2)
  | degree_wrt_ftyp_fexp_tabs : forall n1 e1,
    degree_fexp_wrt_ftyp (S n1) e1 ->
    degree_fexp_wrt_ftyp n1 (fexp_tabs e1)
  | degree_wrt_ftyp_fexp_tapp : forall n1 e1 A1,
    degree_fexp_wrt_ftyp n1 e1 ->
    degree_ftyp_wrt_ftyp n1 A1 ->
    degree_fexp_wrt_ftyp n1 (fexp_tapp e1 A1).

Inductive degree_fexp_wrt_fexp : nat -> fexp -> Prop :=
  | degree_wrt_fexp_fexp_var_f : forall n1 x1,
    degree_fexp_wrt_fexp n1 (fexp_var_f x1)
  | degree_wrt_fexp_fexp_var_b : forall n1 n2,
    lt n2 n1 ->
    degree_fexp_wrt_fexp n1 (fexp_var_b n2)
  | degree_wrt_fexp_fexp_abs : forall n1 A1 e1,
    degree_fexp_wrt_fexp (S n1) e1 ->
    degree_fexp_wrt_fexp n1 (fexp_abs A1 e1)
  | degree_wrt_fexp_fexp_app : forall n1 e1 e2,
    degree_fexp_wrt_fexp n1 e1 ->
    degree_fexp_wrt_fexp n1 e2 ->
    degree_fexp_wrt_fexp n1 (fexp_app e1 e2)
  | degree_wrt_fexp_fexp_tabs : forall n1 e1,
    degree_fexp_wrt_fexp n1 e1 ->
    degree_fexp_wrt_fexp n1 (fexp_tabs e1)
  | degree_wrt_fexp_fexp_tapp : forall n1 e1 A1,
    degree_fexp_wrt_fexp n1 e1 ->
    degree_fexp_wrt_fexp n1 (fexp_tapp e1 A1).

Scheme degree_fexp_wrt_ftyp_ind' := Induction for degree_fexp_wrt_ftyp Sort Prop.

Combined Scheme degree_fexp_wrt_ftyp_mutind from degree_fexp_wrt_ftyp_ind'.

Scheme degree_fexp_wrt_fexp_ind' := Induction for degree_fexp_wrt_fexp Sort Prop.

Combined Scheme degree_fexp_wrt_fexp_mutind from degree_fexp_wrt_fexp_ind'.

#[export] Hint Constructors degree_fexp_wrt_ftyp : core lngen.

#[export] Hint Constructors degree_fexp_wrt_fexp : core lngen.


(* *********************************************************************** *)
(** * Local closure (version in [Set], induction principles) *)

Inductive lc_set_ftyp : ftyp -> Set :=
  | lc_set_ftyp_var_f : forall X1,
    lc_set_ftyp (ftyp_var_f X1)
  | lc_set_ftyp_arr : forall A1 A2,
    lc_set_ftyp A1 ->
    lc_set_ftyp A2 ->
    lc_set_ftyp (ftyp_arr A1 A2)
  | lc_set_ftyp_all : forall A1,
    (forall X1 : typvar, lc_set_ftyp (open_ftyp_wrt_ftyp A1 (ftyp_var_f X1))) ->
    lc_set_ftyp (ftyp_all A1).
Scheme lc_ftyp_ind' := Induction for lc_ftyp Sort Prop.

Combined Scheme lc_ftyp_mutind from lc_ftyp_ind'.

Scheme lc_set_ftyp_ind' := Induction for lc_set_ftyp Sort Prop.

Combined Scheme lc_set_ftyp_mutind from lc_set_ftyp_ind'.

Scheme lc_set_ftyp_rec' := Induction for lc_set_ftyp Sort Set.

Combined Scheme lc_set_ftyp_mutrec from lc_set_ftyp_rec'.

#[export] Hint Constructors lc_ftyp : core lngen.

#[export] Hint Constructors lc_set_ftyp : core lngen.

Inductive lc_set_fexp : fexp -> Set :=
  | lc_set_fexp_var_f : forall x1,
    lc_set_fexp (fexp_var_f x1)
  | lc_set_fexp_abs : forall A1 e1,
    lc_set_ftyp A1 ->
    (forall x1 : expvar, lc_set_fexp (open_fexp_wrt_fexp e1 (fexp_var_f x1))) ->
    lc_set_fexp (fexp_abs A1 e1)
  | lc_set_fexp_app : forall e1 e2,
    lc_set_fexp e1 ->
    lc_set_fexp e2 ->
    lc_set_fexp (fexp_app e1 e2)
  | lc_set_fexp_tabs : forall e1,
    (forall X1 : typvar, lc_set_fexp (open_fexp_wrt_ftyp e1 (ftyp_var_f X1))) ->
    lc_set_fexp (fexp_tabs e1)
  | lc_set_fexp_tapp : forall e1 A1,
    lc_set_fexp e1 ->
    lc_set_ftyp A1 ->
    lc_set_fexp (fexp_tapp e1 A1).
Scheme lc_fexp_ind' := Induction for lc_fexp Sort Prop.

Combined Scheme lc_fexp_mutind from lc_fexp_ind'.

Scheme lc_set_fexp_ind' := Induction for lc_set_fexp Sort Prop.

Combined Scheme lc_set_fexp_mutind from lc_set_fexp_ind'.

Scheme lc_set_fexp_rec' := Induction for lc_set_fexp Sort Set.

Combined Scheme lc_set_fexp_mutrec from lc_set_fexp_rec'.

#[export] Hint Constructors lc_fexp : core lngen.

#[export] Hint Constructors lc_set_fexp : core lngen.


(* *********************************************************************** *)
(** * Body *)

Definition body_ftyp_wrt_ftyp A1 := forall X1, lc_ftyp (open_ftyp_wrt_ftyp A1 (ftyp_var_f X1)).

#[export] Hint Unfold body_ftyp_wrt_ftyp : core.

Definition body_fexp_wrt_ftyp e1 := forall X1, lc_fexp (open_fexp_wrt_ftyp e1 (ftyp_var_f X1)).

Definition body_fexp_wrt_fexp e1 := forall x1, lc_fexp (open_fexp_wrt_fexp e1 (fexp_var_f x1)).

#[export] Hint Unfold body_fexp_wrt_ftyp : core.

#[export] Hint Unfold body_fexp_wrt_fexp : core.


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

Lemma size_ftyp_min_mutual :
(forall A1, 1 <= size_ftyp A1).
Proof.
apply_mutual_ind ftyp_mutind;
default_simp.
Qed.

(* end hide *)

Lemma size_ftyp_min :
forall A1, 1 <= size_ftyp A1.
Proof.
pose proof size_ftyp_min_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve size_ftyp_min : lngen.

(* begin hide *)

Lemma size_fexp_min_mutual :
(forall e1, 1 <= size_fexp e1).
Proof.
apply_mutual_ind fexp_mutind;
default_simp.
Qed.

(* end hide *)

Lemma size_fexp_min :
forall e1, 1 <= size_fexp e1.
Proof.
pose proof size_fexp_min_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve size_fexp_min : lngen.

(* begin hide *)

Lemma size_ftyp_close_ftyp_wrt_ftyp_rec_mutual :
(forall A1 X1 n1,
  size_ftyp (close_ftyp_wrt_ftyp_rec n1 X1 A1) = size_ftyp A1).
Proof.
apply_mutual_ind ftyp_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma size_ftyp_close_ftyp_wrt_ftyp_rec :
forall A1 X1 n1,
  size_ftyp (close_ftyp_wrt_ftyp_rec n1 X1 A1) = size_ftyp A1.
Proof.
pose proof size_ftyp_close_ftyp_wrt_ftyp_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve size_ftyp_close_ftyp_wrt_ftyp_rec : lngen.
#[export] Hint Rewrite size_ftyp_close_ftyp_wrt_ftyp_rec using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma size_fexp_close_fexp_wrt_ftyp_rec_mutual :
(forall e1 X1 n1,
  size_fexp (close_fexp_wrt_ftyp_rec n1 X1 e1) = size_fexp e1).
Proof.
apply_mutual_ind fexp_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma size_fexp_close_fexp_wrt_ftyp_rec :
forall e1 X1 n1,
  size_fexp (close_fexp_wrt_ftyp_rec n1 X1 e1) = size_fexp e1.
Proof.
pose proof size_fexp_close_fexp_wrt_ftyp_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve size_fexp_close_fexp_wrt_ftyp_rec : lngen.
#[export] Hint Rewrite size_fexp_close_fexp_wrt_ftyp_rec using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma size_fexp_close_fexp_wrt_fexp_rec_mutual :
(forall e1 x1 n1,
  size_fexp (close_fexp_wrt_fexp_rec n1 x1 e1) = size_fexp e1).
Proof.
apply_mutual_ind fexp_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma size_fexp_close_fexp_wrt_fexp_rec :
forall e1 x1 n1,
  size_fexp (close_fexp_wrt_fexp_rec n1 x1 e1) = size_fexp e1.
Proof.
pose proof size_fexp_close_fexp_wrt_fexp_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve size_fexp_close_fexp_wrt_fexp_rec : lngen.
#[export] Hint Rewrite size_fexp_close_fexp_wrt_fexp_rec using solve [auto] : lngen.

(* end hide *)

Lemma size_ftyp_close_ftyp_wrt_ftyp :
forall A1 X1,
  size_ftyp (close_ftyp_wrt_ftyp X1 A1) = size_ftyp A1.
Proof.
unfold close_ftyp_wrt_ftyp; default_simp.
Qed.

#[export] Hint Resolve size_ftyp_close_ftyp_wrt_ftyp : lngen.
#[export] Hint Rewrite size_ftyp_close_ftyp_wrt_ftyp using solve [auto] : lngen.

Lemma size_fexp_close_fexp_wrt_ftyp :
forall e1 X1,
  size_fexp (close_fexp_wrt_ftyp X1 e1) = size_fexp e1.
Proof.
unfold close_fexp_wrt_ftyp; default_simp.
Qed.

#[export] Hint Resolve size_fexp_close_fexp_wrt_ftyp : lngen.
#[export] Hint Rewrite size_fexp_close_fexp_wrt_ftyp using solve [auto] : lngen.

Lemma size_fexp_close_fexp_wrt_fexp :
forall e1 x1,
  size_fexp (close_fexp_wrt_fexp x1 e1) = size_fexp e1.
Proof.
unfold close_fexp_wrt_fexp; default_simp.
Qed.

#[export] Hint Resolve size_fexp_close_fexp_wrt_fexp : lngen.
#[export] Hint Rewrite size_fexp_close_fexp_wrt_fexp using solve [auto] : lngen.

(* begin hide *)

Lemma size_ftyp_open_ftyp_wrt_ftyp_rec_mutual :
(forall A1 A2 n1,
  size_ftyp A1 <= size_ftyp (open_ftyp_wrt_ftyp_rec n1 A2 A1)).
Proof.
apply_mutual_ind ftyp_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma size_ftyp_open_ftyp_wrt_ftyp_rec :
forall A1 A2 n1,
  size_ftyp A1 <= size_ftyp (open_ftyp_wrt_ftyp_rec n1 A2 A1).
Proof.
pose proof size_ftyp_open_ftyp_wrt_ftyp_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve size_ftyp_open_ftyp_wrt_ftyp_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma size_fexp_open_fexp_wrt_ftyp_rec_mutual :
(forall e1 A1 n1,
  size_fexp e1 <= size_fexp (open_fexp_wrt_ftyp_rec n1 A1 e1)).
Proof.
apply_mutual_ind fexp_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma size_fexp_open_fexp_wrt_ftyp_rec :
forall e1 A1 n1,
  size_fexp e1 <= size_fexp (open_fexp_wrt_ftyp_rec n1 A1 e1).
Proof.
pose proof size_fexp_open_fexp_wrt_ftyp_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve size_fexp_open_fexp_wrt_ftyp_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma size_fexp_open_fexp_wrt_fexp_rec_mutual :
(forall e1 e2 n1,
  size_fexp e1 <= size_fexp (open_fexp_wrt_fexp_rec n1 e2 e1)).
Proof.
apply_mutual_ind fexp_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma size_fexp_open_fexp_wrt_fexp_rec :
forall e1 e2 n1,
  size_fexp e1 <= size_fexp (open_fexp_wrt_fexp_rec n1 e2 e1).
Proof.
pose proof size_fexp_open_fexp_wrt_fexp_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve size_fexp_open_fexp_wrt_fexp_rec : lngen.

(* end hide *)

Lemma size_ftyp_open_ftyp_wrt_ftyp :
forall A1 A2,
  size_ftyp A1 <= size_ftyp (open_ftyp_wrt_ftyp A1 A2).
Proof.
unfold open_ftyp_wrt_ftyp; default_simp.
Qed.

#[export] Hint Resolve size_ftyp_open_ftyp_wrt_ftyp : lngen.

Lemma size_fexp_open_fexp_wrt_ftyp :
forall e1 A1,
  size_fexp e1 <= size_fexp (open_fexp_wrt_ftyp e1 A1).
Proof.
unfold open_fexp_wrt_ftyp; default_simp.
Qed.

#[export] Hint Resolve size_fexp_open_fexp_wrt_ftyp : lngen.

Lemma size_fexp_open_fexp_wrt_fexp :
forall e1 e2,
  size_fexp e1 <= size_fexp (open_fexp_wrt_fexp e1 e2).
Proof.
unfold open_fexp_wrt_fexp; default_simp.
Qed.

#[export] Hint Resolve size_fexp_open_fexp_wrt_fexp : lngen.

(* begin hide *)

Lemma size_ftyp_open_ftyp_wrt_ftyp_rec_var_mutual :
(forall A1 X1 n1,
  size_ftyp (open_ftyp_wrt_ftyp_rec n1 (ftyp_var_f X1) A1) = size_ftyp A1).
Proof.
apply_mutual_ind ftyp_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma size_ftyp_open_ftyp_wrt_ftyp_rec_var :
forall A1 X1 n1,
  size_ftyp (open_ftyp_wrt_ftyp_rec n1 (ftyp_var_f X1) A1) = size_ftyp A1.
Proof.
pose proof size_ftyp_open_ftyp_wrt_ftyp_rec_var_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve size_ftyp_open_ftyp_wrt_ftyp_rec_var : lngen.
#[export] Hint Rewrite size_ftyp_open_ftyp_wrt_ftyp_rec_var using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma size_fexp_open_fexp_wrt_ftyp_rec_var_mutual :
(forall e1 X1 n1,
  size_fexp (open_fexp_wrt_ftyp_rec n1 (ftyp_var_f X1) e1) = size_fexp e1).
Proof.
apply_mutual_ind fexp_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma size_fexp_open_fexp_wrt_ftyp_rec_var :
forall e1 X1 n1,
  size_fexp (open_fexp_wrt_ftyp_rec n1 (ftyp_var_f X1) e1) = size_fexp e1.
Proof.
pose proof size_fexp_open_fexp_wrt_ftyp_rec_var_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve size_fexp_open_fexp_wrt_ftyp_rec_var : lngen.
#[export] Hint Rewrite size_fexp_open_fexp_wrt_ftyp_rec_var using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma size_fexp_open_fexp_wrt_fexp_rec_var_mutual :
(forall e1 x1 n1,
  size_fexp (open_fexp_wrt_fexp_rec n1 (fexp_var_f x1) e1) = size_fexp e1).
Proof.
apply_mutual_ind fexp_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma size_fexp_open_fexp_wrt_fexp_rec_var :
forall e1 x1 n1,
  size_fexp (open_fexp_wrt_fexp_rec n1 (fexp_var_f x1) e1) = size_fexp e1.
Proof.
pose proof size_fexp_open_fexp_wrt_fexp_rec_var_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve size_fexp_open_fexp_wrt_fexp_rec_var : lngen.
#[export] Hint Rewrite size_fexp_open_fexp_wrt_fexp_rec_var using solve [auto] : lngen.

(* end hide *)

Lemma size_ftyp_open_ftyp_wrt_ftyp_var :
forall A1 X1,
  size_ftyp (open_ftyp_wrt_ftyp A1 (ftyp_var_f X1)) = size_ftyp A1.
Proof.
unfold open_ftyp_wrt_ftyp; default_simp.
Qed.

#[export] Hint Resolve size_ftyp_open_ftyp_wrt_ftyp_var : lngen.
#[export] Hint Rewrite size_ftyp_open_ftyp_wrt_ftyp_var using solve [auto] : lngen.

Lemma size_fexp_open_fexp_wrt_ftyp_var :
forall e1 X1,
  size_fexp (open_fexp_wrt_ftyp e1 (ftyp_var_f X1)) = size_fexp e1.
Proof.
unfold open_fexp_wrt_ftyp; default_simp.
Qed.

#[export] Hint Resolve size_fexp_open_fexp_wrt_ftyp_var : lngen.
#[export] Hint Rewrite size_fexp_open_fexp_wrt_ftyp_var using solve [auto] : lngen.

Lemma size_fexp_open_fexp_wrt_fexp_var :
forall e1 x1,
  size_fexp (open_fexp_wrt_fexp e1 (fexp_var_f x1)) = size_fexp e1.
Proof.
unfold open_fexp_wrt_fexp; default_simp.
Qed.

#[export] Hint Resolve size_fexp_open_fexp_wrt_fexp_var : lngen.
#[export] Hint Rewrite size_fexp_open_fexp_wrt_fexp_var using solve [auto] : lngen.


(* *********************************************************************** *)
(** * Theorems about [degree] *)

Ltac default_auto ::= auto with lngen; tauto.
Ltac default_autorewrite ::= fail.

(* begin hide *)

Lemma degree_ftyp_wrt_ftyp_S_mutual :
(forall n1 A1,
  degree_ftyp_wrt_ftyp n1 A1 ->
  degree_ftyp_wrt_ftyp (S n1) A1).
Proof.
apply_mutual_ind degree_ftyp_wrt_ftyp_mutind;
default_simp.
Qed.

(* end hide *)

Lemma degree_ftyp_wrt_ftyp_S :
forall n1 A1,
  degree_ftyp_wrt_ftyp n1 A1 ->
  degree_ftyp_wrt_ftyp (S n1) A1.
Proof.
pose proof degree_ftyp_wrt_ftyp_S_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve degree_ftyp_wrt_ftyp_S : lngen.

(* begin hide *)

Lemma degree_fexp_wrt_ftyp_S_mutual :
(forall n1 e1,
  degree_fexp_wrt_ftyp n1 e1 ->
  degree_fexp_wrt_ftyp (S n1) e1).
Proof.
apply_mutual_ind degree_fexp_wrt_ftyp_mutind;
default_simp.
Qed.

(* end hide *)

Lemma degree_fexp_wrt_ftyp_S :
forall n1 e1,
  degree_fexp_wrt_ftyp n1 e1 ->
  degree_fexp_wrt_ftyp (S n1) e1.
Proof.
pose proof degree_fexp_wrt_ftyp_S_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve degree_fexp_wrt_ftyp_S : lngen.

(* begin hide *)

Lemma degree_fexp_wrt_fexp_S_mutual :
(forall n1 e1,
  degree_fexp_wrt_fexp n1 e1 ->
  degree_fexp_wrt_fexp (S n1) e1).
Proof.
apply_mutual_ind degree_fexp_wrt_fexp_mutind;
default_simp.
Qed.

(* end hide *)

Lemma degree_fexp_wrt_fexp_S :
forall n1 e1,
  degree_fexp_wrt_fexp n1 e1 ->
  degree_fexp_wrt_fexp (S n1) e1.
Proof.
pose proof degree_fexp_wrt_fexp_S_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve degree_fexp_wrt_fexp_S : lngen.

Lemma degree_ftyp_wrt_ftyp_O :
forall n1 A1,
  degree_ftyp_wrt_ftyp O A1 ->
  degree_ftyp_wrt_ftyp n1 A1.
Proof.
induction n1; default_simp.
Qed.

#[export] Hint Resolve degree_ftyp_wrt_ftyp_O : lngen.

Lemma degree_fexp_wrt_ftyp_O :
forall n1 e1,
  degree_fexp_wrt_ftyp O e1 ->
  degree_fexp_wrt_ftyp n1 e1.
Proof.
induction n1; default_simp.
Qed.

#[export] Hint Resolve degree_fexp_wrt_ftyp_O : lngen.

Lemma degree_fexp_wrt_fexp_O :
forall n1 e1,
  degree_fexp_wrt_fexp O e1 ->
  degree_fexp_wrt_fexp n1 e1.
Proof.
induction n1; default_simp.
Qed.

#[export] Hint Resolve degree_fexp_wrt_fexp_O : lngen.

(* begin hide *)

Lemma degree_ftyp_wrt_ftyp_close_ftyp_wrt_ftyp_rec_mutual :
(forall A1 X1 n1,
  degree_ftyp_wrt_ftyp n1 A1 ->
  degree_ftyp_wrt_ftyp (S n1) (close_ftyp_wrt_ftyp_rec n1 X1 A1)).
Proof.
apply_mutual_ind ftyp_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma degree_ftyp_wrt_ftyp_close_ftyp_wrt_ftyp_rec :
forall A1 X1 n1,
  degree_ftyp_wrt_ftyp n1 A1 ->
  degree_ftyp_wrt_ftyp (S n1) (close_ftyp_wrt_ftyp_rec n1 X1 A1).
Proof.
pose proof degree_ftyp_wrt_ftyp_close_ftyp_wrt_ftyp_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve degree_ftyp_wrt_ftyp_close_ftyp_wrt_ftyp_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_fexp_wrt_ftyp_close_fexp_wrt_ftyp_rec_mutual :
(forall e1 X1 n1,
  degree_fexp_wrt_ftyp n1 e1 ->
  degree_fexp_wrt_ftyp (S n1) (close_fexp_wrt_ftyp_rec n1 X1 e1)).
Proof.
apply_mutual_ind fexp_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma degree_fexp_wrt_ftyp_close_fexp_wrt_ftyp_rec :
forall e1 X1 n1,
  degree_fexp_wrt_ftyp n1 e1 ->
  degree_fexp_wrt_ftyp (S n1) (close_fexp_wrt_ftyp_rec n1 X1 e1).
Proof.
pose proof degree_fexp_wrt_ftyp_close_fexp_wrt_ftyp_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve degree_fexp_wrt_ftyp_close_fexp_wrt_ftyp_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_fexp_wrt_ftyp_close_fexp_wrt_fexp_rec_mutual :
(forall e1 x1 n1 n2,
  degree_fexp_wrt_ftyp n2 e1 ->
  degree_fexp_wrt_ftyp n2 (close_fexp_wrt_fexp_rec n1 x1 e1)).
Proof.
apply_mutual_ind fexp_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma degree_fexp_wrt_ftyp_close_fexp_wrt_fexp_rec :
forall e1 x1 n1 n2,
  degree_fexp_wrt_ftyp n2 e1 ->
  degree_fexp_wrt_ftyp n2 (close_fexp_wrt_fexp_rec n1 x1 e1).
Proof.
pose proof degree_fexp_wrt_ftyp_close_fexp_wrt_fexp_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve degree_fexp_wrt_ftyp_close_fexp_wrt_fexp_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_fexp_wrt_fexp_close_fexp_wrt_ftyp_rec_mutual :
(forall e1 X1 n1 n2,
  degree_fexp_wrt_fexp n2 e1 ->
  degree_fexp_wrt_fexp n2 (close_fexp_wrt_ftyp_rec n1 X1 e1)).
Proof.
apply_mutual_ind fexp_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma degree_fexp_wrt_fexp_close_fexp_wrt_ftyp_rec :
forall e1 X1 n1 n2,
  degree_fexp_wrt_fexp n2 e1 ->
  degree_fexp_wrt_fexp n2 (close_fexp_wrt_ftyp_rec n1 X1 e1).
Proof.
pose proof degree_fexp_wrt_fexp_close_fexp_wrt_ftyp_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve degree_fexp_wrt_fexp_close_fexp_wrt_ftyp_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_fexp_wrt_fexp_close_fexp_wrt_fexp_rec_mutual :
(forall e1 x1 n1,
  degree_fexp_wrt_fexp n1 e1 ->
  degree_fexp_wrt_fexp (S n1) (close_fexp_wrt_fexp_rec n1 x1 e1)).
Proof.
apply_mutual_ind fexp_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma degree_fexp_wrt_fexp_close_fexp_wrt_fexp_rec :
forall e1 x1 n1,
  degree_fexp_wrt_fexp n1 e1 ->
  degree_fexp_wrt_fexp (S n1) (close_fexp_wrt_fexp_rec n1 x1 e1).
Proof.
pose proof degree_fexp_wrt_fexp_close_fexp_wrt_fexp_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve degree_fexp_wrt_fexp_close_fexp_wrt_fexp_rec : lngen.

(* end hide *)

Lemma degree_ftyp_wrt_ftyp_close_ftyp_wrt_ftyp :
forall A1 X1,
  degree_ftyp_wrt_ftyp 0 A1 ->
  degree_ftyp_wrt_ftyp 1 (close_ftyp_wrt_ftyp X1 A1).
Proof.
unfold close_ftyp_wrt_ftyp; default_simp.
Qed.

#[export] Hint Resolve degree_ftyp_wrt_ftyp_close_ftyp_wrt_ftyp : lngen.

Lemma degree_fexp_wrt_ftyp_close_fexp_wrt_ftyp :
forall e1 X1,
  degree_fexp_wrt_ftyp 0 e1 ->
  degree_fexp_wrt_ftyp 1 (close_fexp_wrt_ftyp X1 e1).
Proof.
unfold close_fexp_wrt_ftyp; default_simp.
Qed.

#[export] Hint Resolve degree_fexp_wrt_ftyp_close_fexp_wrt_ftyp : lngen.

Lemma degree_fexp_wrt_ftyp_close_fexp_wrt_fexp :
forall e1 x1 n1,
  degree_fexp_wrt_ftyp n1 e1 ->
  degree_fexp_wrt_ftyp n1 (close_fexp_wrt_fexp x1 e1).
Proof.
unfold close_fexp_wrt_fexp; default_simp.
Qed.

#[export] Hint Resolve degree_fexp_wrt_ftyp_close_fexp_wrt_fexp : lngen.

Lemma degree_fexp_wrt_fexp_close_fexp_wrt_ftyp :
forall e1 X1 n1,
  degree_fexp_wrt_fexp n1 e1 ->
  degree_fexp_wrt_fexp n1 (close_fexp_wrt_ftyp X1 e1).
Proof.
unfold close_fexp_wrt_ftyp; default_simp.
Qed.

#[export] Hint Resolve degree_fexp_wrt_fexp_close_fexp_wrt_ftyp : lngen.

Lemma degree_fexp_wrt_fexp_close_fexp_wrt_fexp :
forall e1 x1,
  degree_fexp_wrt_fexp 0 e1 ->
  degree_fexp_wrt_fexp 1 (close_fexp_wrt_fexp x1 e1).
Proof.
unfold close_fexp_wrt_fexp; default_simp.
Qed.

#[export] Hint Resolve degree_fexp_wrt_fexp_close_fexp_wrt_fexp : lngen.

(* begin hide *)

Lemma degree_ftyp_wrt_ftyp_close_ftyp_wrt_ftyp_rec_inv_mutual :
(forall A1 X1 n1,
  degree_ftyp_wrt_ftyp (S n1) (close_ftyp_wrt_ftyp_rec n1 X1 A1) ->
  degree_ftyp_wrt_ftyp n1 A1).
Proof.
apply_mutual_ind ftyp_mutind;
default_simp; eauto with lngen.
Qed.

(* end hide *)

(* begin hide *)

Lemma degree_ftyp_wrt_ftyp_close_ftyp_wrt_ftyp_rec_inv :
forall A1 X1 n1,
  degree_ftyp_wrt_ftyp (S n1) (close_ftyp_wrt_ftyp_rec n1 X1 A1) ->
  degree_ftyp_wrt_ftyp n1 A1.
Proof.
pose proof degree_ftyp_wrt_ftyp_close_ftyp_wrt_ftyp_rec_inv_mutual as H; intuition eauto.
Qed.

#[export] Hint Immediate degree_ftyp_wrt_ftyp_close_ftyp_wrt_ftyp_rec_inv : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_fexp_wrt_ftyp_close_fexp_wrt_ftyp_rec_inv_mutual :
(forall e1 X1 n1,
  degree_fexp_wrt_ftyp (S n1) (close_fexp_wrt_ftyp_rec n1 X1 e1) ->
  degree_fexp_wrt_ftyp n1 e1).
Proof.
apply_mutual_ind fexp_mutind;
default_simp; eauto with lngen.
Qed.

(* end hide *)

(* begin hide *)

Lemma degree_fexp_wrt_ftyp_close_fexp_wrt_ftyp_rec_inv :
forall e1 X1 n1,
  degree_fexp_wrt_ftyp (S n1) (close_fexp_wrt_ftyp_rec n1 X1 e1) ->
  degree_fexp_wrt_ftyp n1 e1.
Proof.
pose proof degree_fexp_wrt_ftyp_close_fexp_wrt_ftyp_rec_inv_mutual as H; intuition eauto.
Qed.

#[export] Hint Immediate degree_fexp_wrt_ftyp_close_fexp_wrt_ftyp_rec_inv : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_fexp_wrt_ftyp_close_fexp_wrt_fexp_rec_inv_mutual :
(forall e1 x1 n1 n2,
  degree_fexp_wrt_ftyp n2 (close_fexp_wrt_fexp_rec n1 x1 e1) ->
  degree_fexp_wrt_ftyp n2 e1).
Proof.
apply_mutual_ind fexp_mutind;
default_simp; eauto with lngen.
Qed.

(* end hide *)

(* begin hide *)

Lemma degree_fexp_wrt_ftyp_close_fexp_wrt_fexp_rec_inv :
forall e1 x1 n1 n2,
  degree_fexp_wrt_ftyp n2 (close_fexp_wrt_fexp_rec n1 x1 e1) ->
  degree_fexp_wrt_ftyp n2 e1.
Proof.
pose proof degree_fexp_wrt_ftyp_close_fexp_wrt_fexp_rec_inv_mutual as H; intuition eauto.
Qed.

#[export] Hint Immediate degree_fexp_wrt_ftyp_close_fexp_wrt_fexp_rec_inv : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_fexp_wrt_fexp_close_fexp_wrt_ftyp_rec_inv_mutual :
(forall e1 X1 n1 n2,
  degree_fexp_wrt_fexp n2 (close_fexp_wrt_ftyp_rec n1 X1 e1) ->
  degree_fexp_wrt_fexp n2 e1).
Proof.
apply_mutual_ind fexp_mutind;
default_simp; eauto with lngen.
Qed.

(* end hide *)

(* begin hide *)

Lemma degree_fexp_wrt_fexp_close_fexp_wrt_ftyp_rec_inv :
forall e1 X1 n1 n2,
  degree_fexp_wrt_fexp n2 (close_fexp_wrt_ftyp_rec n1 X1 e1) ->
  degree_fexp_wrt_fexp n2 e1.
Proof.
pose proof degree_fexp_wrt_fexp_close_fexp_wrt_ftyp_rec_inv_mutual as H; intuition eauto.
Qed.

#[export] Hint Immediate degree_fexp_wrt_fexp_close_fexp_wrt_ftyp_rec_inv : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_fexp_wrt_fexp_close_fexp_wrt_fexp_rec_inv_mutual :
(forall e1 x1 n1,
  degree_fexp_wrt_fexp (S n1) (close_fexp_wrt_fexp_rec n1 x1 e1) ->
  degree_fexp_wrt_fexp n1 e1).
Proof.
apply_mutual_ind fexp_mutind;
default_simp; eauto with lngen.
Qed.

(* end hide *)

(* begin hide *)

Lemma degree_fexp_wrt_fexp_close_fexp_wrt_fexp_rec_inv :
forall e1 x1 n1,
  degree_fexp_wrt_fexp (S n1) (close_fexp_wrt_fexp_rec n1 x1 e1) ->
  degree_fexp_wrt_fexp n1 e1.
Proof.
pose proof degree_fexp_wrt_fexp_close_fexp_wrt_fexp_rec_inv_mutual as H; intuition eauto.
Qed.

#[export] Hint Immediate degree_fexp_wrt_fexp_close_fexp_wrt_fexp_rec_inv : lngen.

(* end hide *)

Lemma degree_ftyp_wrt_ftyp_close_ftyp_wrt_ftyp_inv :
forall A1 X1,
  degree_ftyp_wrt_ftyp 1 (close_ftyp_wrt_ftyp X1 A1) ->
  degree_ftyp_wrt_ftyp 0 A1.
Proof.
unfold close_ftyp_wrt_ftyp; eauto with lngen.
Qed.

#[export] Hint Immediate degree_ftyp_wrt_ftyp_close_ftyp_wrt_ftyp_inv : lngen.

Lemma degree_fexp_wrt_ftyp_close_fexp_wrt_ftyp_inv :
forall e1 X1,
  degree_fexp_wrt_ftyp 1 (close_fexp_wrt_ftyp X1 e1) ->
  degree_fexp_wrt_ftyp 0 e1.
Proof.
unfold close_fexp_wrt_ftyp; eauto with lngen.
Qed.

#[export] Hint Immediate degree_fexp_wrt_ftyp_close_fexp_wrt_ftyp_inv : lngen.

Lemma degree_fexp_wrt_ftyp_close_fexp_wrt_fexp_inv :
forall e1 x1 n1,
  degree_fexp_wrt_ftyp n1 (close_fexp_wrt_fexp x1 e1) ->
  degree_fexp_wrt_ftyp n1 e1.
Proof.
unfold close_fexp_wrt_fexp; eauto with lngen.
Qed.

#[export] Hint Immediate degree_fexp_wrt_ftyp_close_fexp_wrt_fexp_inv : lngen.

Lemma degree_fexp_wrt_fexp_close_fexp_wrt_ftyp_inv :
forall e1 X1 n1,
  degree_fexp_wrt_fexp n1 (close_fexp_wrt_ftyp X1 e1) ->
  degree_fexp_wrt_fexp n1 e1.
Proof.
unfold close_fexp_wrt_ftyp; eauto with lngen.
Qed.

#[export] Hint Immediate degree_fexp_wrt_fexp_close_fexp_wrt_ftyp_inv : lngen.

Lemma degree_fexp_wrt_fexp_close_fexp_wrt_fexp_inv :
forall e1 x1,
  degree_fexp_wrt_fexp 1 (close_fexp_wrt_fexp x1 e1) ->
  degree_fexp_wrt_fexp 0 e1.
Proof.
unfold close_fexp_wrt_fexp; eauto with lngen.
Qed.

#[export] Hint Immediate degree_fexp_wrt_fexp_close_fexp_wrt_fexp_inv : lngen.

(* begin hide *)

Lemma degree_ftyp_wrt_ftyp_open_ftyp_wrt_ftyp_rec_mutual :
(forall A1 A2 n1,
  degree_ftyp_wrt_ftyp (S n1) A1 ->
  degree_ftyp_wrt_ftyp n1 A2 ->
  degree_ftyp_wrt_ftyp n1 (open_ftyp_wrt_ftyp_rec n1 A2 A1)).
Proof.
apply_mutual_ind ftyp_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma degree_ftyp_wrt_ftyp_open_ftyp_wrt_ftyp_rec :
forall A1 A2 n1,
  degree_ftyp_wrt_ftyp (S n1) A1 ->
  degree_ftyp_wrt_ftyp n1 A2 ->
  degree_ftyp_wrt_ftyp n1 (open_ftyp_wrt_ftyp_rec n1 A2 A1).
Proof.
pose proof degree_ftyp_wrt_ftyp_open_ftyp_wrt_ftyp_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve degree_ftyp_wrt_ftyp_open_ftyp_wrt_ftyp_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_fexp_wrt_ftyp_open_fexp_wrt_ftyp_rec_mutual :
(forall e1 A1 n1,
  degree_fexp_wrt_ftyp (S n1) e1 ->
  degree_ftyp_wrt_ftyp n1 A1 ->
  degree_fexp_wrt_ftyp n1 (open_fexp_wrt_ftyp_rec n1 A1 e1)).
Proof.
apply_mutual_ind fexp_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma degree_fexp_wrt_ftyp_open_fexp_wrt_ftyp_rec :
forall e1 A1 n1,
  degree_fexp_wrt_ftyp (S n1) e1 ->
  degree_ftyp_wrt_ftyp n1 A1 ->
  degree_fexp_wrt_ftyp n1 (open_fexp_wrt_ftyp_rec n1 A1 e1).
Proof.
pose proof degree_fexp_wrt_ftyp_open_fexp_wrt_ftyp_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve degree_fexp_wrt_ftyp_open_fexp_wrt_ftyp_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_fexp_wrt_ftyp_open_fexp_wrt_fexp_rec_mutual :
(forall e1 e2 n1 n2,
  degree_fexp_wrt_ftyp n1 e1 ->
  degree_fexp_wrt_ftyp n1 e2 ->
  degree_fexp_wrt_ftyp n1 (open_fexp_wrt_fexp_rec n2 e2 e1)).
Proof.
apply_mutual_ind fexp_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma degree_fexp_wrt_ftyp_open_fexp_wrt_fexp_rec :
forall e1 e2 n1 n2,
  degree_fexp_wrt_ftyp n1 e1 ->
  degree_fexp_wrt_ftyp n1 e2 ->
  degree_fexp_wrt_ftyp n1 (open_fexp_wrt_fexp_rec n2 e2 e1).
Proof.
pose proof degree_fexp_wrt_ftyp_open_fexp_wrt_fexp_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve degree_fexp_wrt_ftyp_open_fexp_wrt_fexp_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_fexp_wrt_fexp_open_fexp_wrt_ftyp_rec_mutual :
(forall e1 A1 n1 n2,
  degree_fexp_wrt_fexp n1 e1 ->
  degree_fexp_wrt_fexp n1 (open_fexp_wrt_ftyp_rec n2 A1 e1)).
Proof.
apply_mutual_ind fexp_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma degree_fexp_wrt_fexp_open_fexp_wrt_ftyp_rec :
forall e1 A1 n1 n2,
  degree_fexp_wrt_fexp n1 e1 ->
  degree_fexp_wrt_fexp n1 (open_fexp_wrt_ftyp_rec n2 A1 e1).
Proof.
pose proof degree_fexp_wrt_fexp_open_fexp_wrt_ftyp_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve degree_fexp_wrt_fexp_open_fexp_wrt_ftyp_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_fexp_wrt_fexp_open_fexp_wrt_fexp_rec_mutual :
(forall e1 e2 n1,
  degree_fexp_wrt_fexp (S n1) e1 ->
  degree_fexp_wrt_fexp n1 e2 ->
  degree_fexp_wrt_fexp n1 (open_fexp_wrt_fexp_rec n1 e2 e1)).
Proof.
apply_mutual_ind fexp_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma degree_fexp_wrt_fexp_open_fexp_wrt_fexp_rec :
forall e1 e2 n1,
  degree_fexp_wrt_fexp (S n1) e1 ->
  degree_fexp_wrt_fexp n1 e2 ->
  degree_fexp_wrt_fexp n1 (open_fexp_wrt_fexp_rec n1 e2 e1).
Proof.
pose proof degree_fexp_wrt_fexp_open_fexp_wrt_fexp_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve degree_fexp_wrt_fexp_open_fexp_wrt_fexp_rec : lngen.

(* end hide *)

Lemma degree_ftyp_wrt_ftyp_open_ftyp_wrt_ftyp :
forall A1 A2,
  degree_ftyp_wrt_ftyp 1 A1 ->
  degree_ftyp_wrt_ftyp 0 A2 ->
  degree_ftyp_wrt_ftyp 0 (open_ftyp_wrt_ftyp A1 A2).
Proof.
unfold open_ftyp_wrt_ftyp; default_simp.
Qed.

#[export] Hint Resolve degree_ftyp_wrt_ftyp_open_ftyp_wrt_ftyp : lngen.

Lemma degree_fexp_wrt_ftyp_open_fexp_wrt_ftyp :
forall e1 A1,
  degree_fexp_wrt_ftyp 1 e1 ->
  degree_ftyp_wrt_ftyp 0 A1 ->
  degree_fexp_wrt_ftyp 0 (open_fexp_wrt_ftyp e1 A1).
Proof.
unfold open_fexp_wrt_ftyp; default_simp.
Qed.

#[export] Hint Resolve degree_fexp_wrt_ftyp_open_fexp_wrt_ftyp : lngen.

Lemma degree_fexp_wrt_ftyp_open_fexp_wrt_fexp :
forall e1 e2 n1,
  degree_fexp_wrt_ftyp n1 e1 ->
  degree_fexp_wrt_ftyp n1 e2 ->
  degree_fexp_wrt_ftyp n1 (open_fexp_wrt_fexp e1 e2).
Proof.
unfold open_fexp_wrt_fexp; default_simp.
Qed.

#[export] Hint Resolve degree_fexp_wrt_ftyp_open_fexp_wrt_fexp : lngen.

Lemma degree_fexp_wrt_fexp_open_fexp_wrt_ftyp :
forall e1 A1 n1,
  degree_fexp_wrt_fexp n1 e1 ->
  degree_fexp_wrt_fexp n1 (open_fexp_wrt_ftyp e1 A1).
Proof.
unfold open_fexp_wrt_ftyp; default_simp.
Qed.

#[export] Hint Resolve degree_fexp_wrt_fexp_open_fexp_wrt_ftyp : lngen.

Lemma degree_fexp_wrt_fexp_open_fexp_wrt_fexp :
forall e1 e2,
  degree_fexp_wrt_fexp 1 e1 ->
  degree_fexp_wrt_fexp 0 e2 ->
  degree_fexp_wrt_fexp 0 (open_fexp_wrt_fexp e1 e2).
Proof.
unfold open_fexp_wrt_fexp; default_simp.
Qed.

#[export] Hint Resolve degree_fexp_wrt_fexp_open_fexp_wrt_fexp : lngen.

(* begin hide *)

Lemma degree_ftyp_wrt_ftyp_open_ftyp_wrt_ftyp_rec_inv_mutual :
(forall A1 A2 n1,
  degree_ftyp_wrt_ftyp n1 (open_ftyp_wrt_ftyp_rec n1 A2 A1) ->
  degree_ftyp_wrt_ftyp (S n1) A1).
Proof.
apply_mutual_ind ftyp_mutind;
default_simp; eauto with lngen.
Qed.

(* end hide *)

(* begin hide *)

Lemma degree_ftyp_wrt_ftyp_open_ftyp_wrt_ftyp_rec_inv :
forall A1 A2 n1,
  degree_ftyp_wrt_ftyp n1 (open_ftyp_wrt_ftyp_rec n1 A2 A1) ->
  degree_ftyp_wrt_ftyp (S n1) A1.
Proof.
pose proof degree_ftyp_wrt_ftyp_open_ftyp_wrt_ftyp_rec_inv_mutual as H; intuition eauto.
Qed.

#[export] Hint Immediate degree_ftyp_wrt_ftyp_open_ftyp_wrt_ftyp_rec_inv : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_fexp_wrt_ftyp_open_fexp_wrt_ftyp_rec_inv_mutual :
(forall e1 A1 n1,
  degree_fexp_wrt_ftyp n1 (open_fexp_wrt_ftyp_rec n1 A1 e1) ->
  degree_fexp_wrt_ftyp (S n1) e1).
Proof.
apply_mutual_ind fexp_mutind;
default_simp; eauto with lngen.
Qed.

(* end hide *)

(* begin hide *)

Lemma degree_fexp_wrt_ftyp_open_fexp_wrt_ftyp_rec_inv :
forall e1 A1 n1,
  degree_fexp_wrt_ftyp n1 (open_fexp_wrt_ftyp_rec n1 A1 e1) ->
  degree_fexp_wrt_ftyp (S n1) e1.
Proof.
pose proof degree_fexp_wrt_ftyp_open_fexp_wrt_ftyp_rec_inv_mutual as H; intuition eauto.
Qed.

#[export] Hint Immediate degree_fexp_wrt_ftyp_open_fexp_wrt_ftyp_rec_inv : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_fexp_wrt_ftyp_open_fexp_wrt_fexp_rec_inv_mutual :
(forall e1 e2 n1 n2,
  degree_fexp_wrt_ftyp n1 (open_fexp_wrt_fexp_rec n2 e2 e1) ->
  degree_fexp_wrt_ftyp n1 e1).
Proof.
apply_mutual_ind fexp_mutind;
default_simp; eauto with lngen.
Qed.

(* end hide *)

(* begin hide *)

Lemma degree_fexp_wrt_ftyp_open_fexp_wrt_fexp_rec_inv :
forall e1 e2 n1 n2,
  degree_fexp_wrt_ftyp n1 (open_fexp_wrt_fexp_rec n2 e2 e1) ->
  degree_fexp_wrt_ftyp n1 e1.
Proof.
pose proof degree_fexp_wrt_ftyp_open_fexp_wrt_fexp_rec_inv_mutual as H; intuition eauto.
Qed.

#[export] Hint Immediate degree_fexp_wrt_ftyp_open_fexp_wrt_fexp_rec_inv : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_fexp_wrt_fexp_open_fexp_wrt_ftyp_rec_inv_mutual :
(forall e1 A1 n1 n2,
  degree_fexp_wrt_fexp n1 (open_fexp_wrt_ftyp_rec n2 A1 e1) ->
  degree_fexp_wrt_fexp n1 e1).
Proof.
apply_mutual_ind fexp_mutind;
default_simp; eauto with lngen.
Qed.

(* end hide *)

(* begin hide *)

Lemma degree_fexp_wrt_fexp_open_fexp_wrt_ftyp_rec_inv :
forall e1 A1 n1 n2,
  degree_fexp_wrt_fexp n1 (open_fexp_wrt_ftyp_rec n2 A1 e1) ->
  degree_fexp_wrt_fexp n1 e1.
Proof.
pose proof degree_fexp_wrt_fexp_open_fexp_wrt_ftyp_rec_inv_mutual as H; intuition eauto.
Qed.

#[export] Hint Immediate degree_fexp_wrt_fexp_open_fexp_wrt_ftyp_rec_inv : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_fexp_wrt_fexp_open_fexp_wrt_fexp_rec_inv_mutual :
(forall e1 e2 n1,
  degree_fexp_wrt_fexp n1 (open_fexp_wrt_fexp_rec n1 e2 e1) ->
  degree_fexp_wrt_fexp (S n1) e1).
Proof.
apply_mutual_ind fexp_mutind;
default_simp; eauto with lngen.
Qed.

(* end hide *)

(* begin hide *)

Lemma degree_fexp_wrt_fexp_open_fexp_wrt_fexp_rec_inv :
forall e1 e2 n1,
  degree_fexp_wrt_fexp n1 (open_fexp_wrt_fexp_rec n1 e2 e1) ->
  degree_fexp_wrt_fexp (S n1) e1.
Proof.
pose proof degree_fexp_wrt_fexp_open_fexp_wrt_fexp_rec_inv_mutual as H; intuition eauto.
Qed.

#[export] Hint Immediate degree_fexp_wrt_fexp_open_fexp_wrt_fexp_rec_inv : lngen.

(* end hide *)

Lemma degree_ftyp_wrt_ftyp_open_ftyp_wrt_ftyp_inv :
forall A1 A2,
  degree_ftyp_wrt_ftyp 0 (open_ftyp_wrt_ftyp A1 A2) ->
  degree_ftyp_wrt_ftyp 1 A1.
Proof.
unfold open_ftyp_wrt_ftyp; eauto with lngen.
Qed.

#[export] Hint Immediate degree_ftyp_wrt_ftyp_open_ftyp_wrt_ftyp_inv : lngen.

Lemma degree_fexp_wrt_ftyp_open_fexp_wrt_ftyp_inv :
forall e1 A1,
  degree_fexp_wrt_ftyp 0 (open_fexp_wrt_ftyp e1 A1) ->
  degree_fexp_wrt_ftyp 1 e1.
Proof.
unfold open_fexp_wrt_ftyp; eauto with lngen.
Qed.

#[export] Hint Immediate degree_fexp_wrt_ftyp_open_fexp_wrt_ftyp_inv : lngen.

Lemma degree_fexp_wrt_ftyp_open_fexp_wrt_fexp_inv :
forall e1 e2 n1,
  degree_fexp_wrt_ftyp n1 (open_fexp_wrt_fexp e1 e2) ->
  degree_fexp_wrt_ftyp n1 e1.
Proof.
unfold open_fexp_wrt_fexp; eauto with lngen.
Qed.

#[export] Hint Immediate degree_fexp_wrt_ftyp_open_fexp_wrt_fexp_inv : lngen.

Lemma degree_fexp_wrt_fexp_open_fexp_wrt_ftyp_inv :
forall e1 A1 n1,
  degree_fexp_wrt_fexp n1 (open_fexp_wrt_ftyp e1 A1) ->
  degree_fexp_wrt_fexp n1 e1.
Proof.
unfold open_fexp_wrt_ftyp; eauto with lngen.
Qed.

#[export] Hint Immediate degree_fexp_wrt_fexp_open_fexp_wrt_ftyp_inv : lngen.

Lemma degree_fexp_wrt_fexp_open_fexp_wrt_fexp_inv :
forall e1 e2,
  degree_fexp_wrt_fexp 0 (open_fexp_wrt_fexp e1 e2) ->
  degree_fexp_wrt_fexp 1 e1.
Proof.
unfold open_fexp_wrt_fexp; eauto with lngen.
Qed.

#[export] Hint Immediate degree_fexp_wrt_fexp_open_fexp_wrt_fexp_inv : lngen.


(* *********************************************************************** *)
(** * Theorems about [open] and [close] *)

Ltac default_auto ::= auto with lngen brute_force; tauto.
Ltac default_autorewrite ::= fail.

(* begin hide *)

Lemma close_ftyp_wrt_ftyp_rec_inj_mutual :
(forall A1 A2 X1 n1,
  close_ftyp_wrt_ftyp_rec n1 X1 A1 = close_ftyp_wrt_ftyp_rec n1 X1 A2 ->
  A1 = A2).
Proof.
apply_mutual_ind ftyp_mutind;
intros; match goal with
          | |- _ = ?term => destruct term
        end;
default_simp; eauto with lngen.
Qed.

(* end hide *)

(* begin hide *)

Lemma close_ftyp_wrt_ftyp_rec_inj :
forall A1 A2 X1 n1,
  close_ftyp_wrt_ftyp_rec n1 X1 A1 = close_ftyp_wrt_ftyp_rec n1 X1 A2 ->
  A1 = A2.
Proof.
pose proof close_ftyp_wrt_ftyp_rec_inj_mutual as H; intuition eauto.
Qed.

#[export] Hint Immediate close_ftyp_wrt_ftyp_rec_inj : lngen.

(* end hide *)

(* begin hide *)

Lemma close_fexp_wrt_ftyp_rec_inj_mutual :
(forall e1 e2 X1 n1,
  close_fexp_wrt_ftyp_rec n1 X1 e1 = close_fexp_wrt_ftyp_rec n1 X1 e2 ->
  e1 = e2).
Proof.
apply_mutual_ind fexp_mutind;
intros; match goal with
          | |- _ = ?term => destruct term
        end;
default_simp; eauto with lngen.
Qed.

(* end hide *)

(* begin hide *)

Lemma close_fexp_wrt_ftyp_rec_inj :
forall e1 e2 X1 n1,
  close_fexp_wrt_ftyp_rec n1 X1 e1 = close_fexp_wrt_ftyp_rec n1 X1 e2 ->
  e1 = e2.
Proof.
pose proof close_fexp_wrt_ftyp_rec_inj_mutual as H; intuition eauto.
Qed.

#[export] Hint Immediate close_fexp_wrt_ftyp_rec_inj : lngen.

(* end hide *)

(* begin hide *)

Lemma close_fexp_wrt_fexp_rec_inj_mutual :
(forall e1 e2 x1 n1,
  close_fexp_wrt_fexp_rec n1 x1 e1 = close_fexp_wrt_fexp_rec n1 x1 e2 ->
  e1 = e2).
Proof.
apply_mutual_ind fexp_mutind;
intros; match goal with
          | |- _ = ?term => destruct term
        end;
default_simp; eauto with lngen.
Qed.

(* end hide *)

(* begin hide *)

Lemma close_fexp_wrt_fexp_rec_inj :
forall e1 e2 x1 n1,
  close_fexp_wrt_fexp_rec n1 x1 e1 = close_fexp_wrt_fexp_rec n1 x1 e2 ->
  e1 = e2.
Proof.
pose proof close_fexp_wrt_fexp_rec_inj_mutual as H; intuition eauto.
Qed.

#[export] Hint Immediate close_fexp_wrt_fexp_rec_inj : lngen.

(* end hide *)

Lemma close_ftyp_wrt_ftyp_inj :
forall A1 A2 X1,
  close_ftyp_wrt_ftyp X1 A1 = close_ftyp_wrt_ftyp X1 A2 ->
  A1 = A2.
Proof.
unfold close_ftyp_wrt_ftyp; eauto with lngen.
Qed.

#[export] Hint Immediate close_ftyp_wrt_ftyp_inj : lngen.

Lemma close_fexp_wrt_ftyp_inj :
forall e1 e2 X1,
  close_fexp_wrt_ftyp X1 e1 = close_fexp_wrt_ftyp X1 e2 ->
  e1 = e2.
Proof.
unfold close_fexp_wrt_ftyp; eauto with lngen.
Qed.

#[export] Hint Immediate close_fexp_wrt_ftyp_inj : lngen.

Lemma close_fexp_wrt_fexp_inj :
forall e1 e2 x1,
  close_fexp_wrt_fexp x1 e1 = close_fexp_wrt_fexp x1 e2 ->
  e1 = e2.
Proof.
unfold close_fexp_wrt_fexp; eauto with lngen.
Qed.

#[export] Hint Immediate close_fexp_wrt_fexp_inj : lngen.

(* begin hide *)

Lemma close_ftyp_wrt_ftyp_rec_open_ftyp_wrt_ftyp_rec_mutual :
(forall A1 X1 n1,
  X1 `notin` ftvar_in_ftyp A1 ->
  close_ftyp_wrt_ftyp_rec n1 X1 (open_ftyp_wrt_ftyp_rec n1 (ftyp_var_f X1) A1) = A1).
Proof.
apply_mutual_ind ftyp_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma close_ftyp_wrt_ftyp_rec_open_ftyp_wrt_ftyp_rec :
forall A1 X1 n1,
  X1 `notin` ftvar_in_ftyp A1 ->
  close_ftyp_wrt_ftyp_rec n1 X1 (open_ftyp_wrt_ftyp_rec n1 (ftyp_var_f X1) A1) = A1.
Proof.
pose proof close_ftyp_wrt_ftyp_rec_open_ftyp_wrt_ftyp_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve close_ftyp_wrt_ftyp_rec_open_ftyp_wrt_ftyp_rec : lngen.
#[export] Hint Rewrite close_ftyp_wrt_ftyp_rec_open_ftyp_wrt_ftyp_rec using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma close_fexp_wrt_ftyp_rec_open_fexp_wrt_ftyp_rec_mutual :
(forall e1 X1 n1,
  X1 `notin` ftvar_in_fexp e1 ->
  close_fexp_wrt_ftyp_rec n1 X1 (open_fexp_wrt_ftyp_rec n1 (ftyp_var_f X1) e1) = e1).
Proof.
apply_mutual_ind fexp_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma close_fexp_wrt_ftyp_rec_open_fexp_wrt_ftyp_rec :
forall e1 X1 n1,
  X1 `notin` ftvar_in_fexp e1 ->
  close_fexp_wrt_ftyp_rec n1 X1 (open_fexp_wrt_ftyp_rec n1 (ftyp_var_f X1) e1) = e1.
Proof.
pose proof close_fexp_wrt_ftyp_rec_open_fexp_wrt_ftyp_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve close_fexp_wrt_ftyp_rec_open_fexp_wrt_ftyp_rec : lngen.
#[export] Hint Rewrite close_fexp_wrt_ftyp_rec_open_fexp_wrt_ftyp_rec using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma close_fexp_wrt_fexp_rec_open_fexp_wrt_fexp_rec_mutual :
(forall e1 x1 n1,
  x1 `notin` fvar_in_fexp e1 ->
  close_fexp_wrt_fexp_rec n1 x1 (open_fexp_wrt_fexp_rec n1 (fexp_var_f x1) e1) = e1).
Proof.
apply_mutual_ind fexp_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma close_fexp_wrt_fexp_rec_open_fexp_wrt_fexp_rec :
forall e1 x1 n1,
  x1 `notin` fvar_in_fexp e1 ->
  close_fexp_wrt_fexp_rec n1 x1 (open_fexp_wrt_fexp_rec n1 (fexp_var_f x1) e1) = e1.
Proof.
pose proof close_fexp_wrt_fexp_rec_open_fexp_wrt_fexp_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve close_fexp_wrt_fexp_rec_open_fexp_wrt_fexp_rec : lngen.
#[export] Hint Rewrite close_fexp_wrt_fexp_rec_open_fexp_wrt_fexp_rec using solve [auto] : lngen.

(* end hide *)

Lemma close_ftyp_wrt_ftyp_open_ftyp_wrt_ftyp :
forall A1 X1,
  X1 `notin` ftvar_in_ftyp A1 ->
  close_ftyp_wrt_ftyp X1 (open_ftyp_wrt_ftyp A1 (ftyp_var_f X1)) = A1.
Proof.
unfold close_ftyp_wrt_ftyp; unfold open_ftyp_wrt_ftyp; default_simp.
Qed.

#[export] Hint Resolve close_ftyp_wrt_ftyp_open_ftyp_wrt_ftyp : lngen.
#[export] Hint Rewrite close_ftyp_wrt_ftyp_open_ftyp_wrt_ftyp using solve [auto] : lngen.

Lemma close_fexp_wrt_ftyp_open_fexp_wrt_ftyp :
forall e1 X1,
  X1 `notin` ftvar_in_fexp e1 ->
  close_fexp_wrt_ftyp X1 (open_fexp_wrt_ftyp e1 (ftyp_var_f X1)) = e1.
Proof.
unfold close_fexp_wrt_ftyp; unfold open_fexp_wrt_ftyp; default_simp.
Qed.

#[export] Hint Resolve close_fexp_wrt_ftyp_open_fexp_wrt_ftyp : lngen.
#[export] Hint Rewrite close_fexp_wrt_ftyp_open_fexp_wrt_ftyp using solve [auto] : lngen.

Lemma close_fexp_wrt_fexp_open_fexp_wrt_fexp :
forall e1 x1,
  x1 `notin` fvar_in_fexp e1 ->
  close_fexp_wrt_fexp x1 (open_fexp_wrt_fexp e1 (fexp_var_f x1)) = e1.
Proof.
unfold close_fexp_wrt_fexp; unfold open_fexp_wrt_fexp; default_simp.
Qed.

#[export] Hint Resolve close_fexp_wrt_fexp_open_fexp_wrt_fexp : lngen.
#[export] Hint Rewrite close_fexp_wrt_fexp_open_fexp_wrt_fexp using solve [auto] : lngen.

(* begin hide *)

Lemma open_ftyp_wrt_ftyp_rec_close_ftyp_wrt_ftyp_rec_mutual :
(forall A1 X1 n1,
  open_ftyp_wrt_ftyp_rec n1 (ftyp_var_f X1) (close_ftyp_wrt_ftyp_rec n1 X1 A1) = A1).
Proof.
apply_mutual_ind ftyp_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma open_ftyp_wrt_ftyp_rec_close_ftyp_wrt_ftyp_rec :
forall A1 X1 n1,
  open_ftyp_wrt_ftyp_rec n1 (ftyp_var_f X1) (close_ftyp_wrt_ftyp_rec n1 X1 A1) = A1.
Proof.
pose proof open_ftyp_wrt_ftyp_rec_close_ftyp_wrt_ftyp_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve open_ftyp_wrt_ftyp_rec_close_ftyp_wrt_ftyp_rec : lngen.
#[export] Hint Rewrite open_ftyp_wrt_ftyp_rec_close_ftyp_wrt_ftyp_rec using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma open_fexp_wrt_ftyp_rec_close_fexp_wrt_ftyp_rec_mutual :
(forall e1 X1 n1,
  open_fexp_wrt_ftyp_rec n1 (ftyp_var_f X1) (close_fexp_wrt_ftyp_rec n1 X1 e1) = e1).
Proof.
apply_mutual_ind fexp_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma open_fexp_wrt_ftyp_rec_close_fexp_wrt_ftyp_rec :
forall e1 X1 n1,
  open_fexp_wrt_ftyp_rec n1 (ftyp_var_f X1) (close_fexp_wrt_ftyp_rec n1 X1 e1) = e1.
Proof.
pose proof open_fexp_wrt_ftyp_rec_close_fexp_wrt_ftyp_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve open_fexp_wrt_ftyp_rec_close_fexp_wrt_ftyp_rec : lngen.
#[export] Hint Rewrite open_fexp_wrt_ftyp_rec_close_fexp_wrt_ftyp_rec using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma open_fexp_wrt_fexp_rec_close_fexp_wrt_fexp_rec_mutual :
(forall e1 x1 n1,
  open_fexp_wrt_fexp_rec n1 (fexp_var_f x1) (close_fexp_wrt_fexp_rec n1 x1 e1) = e1).
Proof.
apply_mutual_ind fexp_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma open_fexp_wrt_fexp_rec_close_fexp_wrt_fexp_rec :
forall e1 x1 n1,
  open_fexp_wrt_fexp_rec n1 (fexp_var_f x1) (close_fexp_wrt_fexp_rec n1 x1 e1) = e1.
Proof.
pose proof open_fexp_wrt_fexp_rec_close_fexp_wrt_fexp_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve open_fexp_wrt_fexp_rec_close_fexp_wrt_fexp_rec : lngen.
#[export] Hint Rewrite open_fexp_wrt_fexp_rec_close_fexp_wrt_fexp_rec using solve [auto] : lngen.

(* end hide *)

Lemma open_ftyp_wrt_ftyp_close_ftyp_wrt_ftyp :
forall A1 X1,
  open_ftyp_wrt_ftyp (close_ftyp_wrt_ftyp X1 A1) (ftyp_var_f X1) = A1.
Proof.
unfold close_ftyp_wrt_ftyp; unfold open_ftyp_wrt_ftyp; default_simp.
Qed.

#[export] Hint Resolve open_ftyp_wrt_ftyp_close_ftyp_wrt_ftyp : lngen.
#[export] Hint Rewrite open_ftyp_wrt_ftyp_close_ftyp_wrt_ftyp using solve [auto] : lngen.

Lemma open_fexp_wrt_ftyp_close_fexp_wrt_ftyp :
forall e1 X1,
  open_fexp_wrt_ftyp (close_fexp_wrt_ftyp X1 e1) (ftyp_var_f X1) = e1.
Proof.
unfold close_fexp_wrt_ftyp; unfold open_fexp_wrt_ftyp; default_simp.
Qed.

#[export] Hint Resolve open_fexp_wrt_ftyp_close_fexp_wrt_ftyp : lngen.
#[export] Hint Rewrite open_fexp_wrt_ftyp_close_fexp_wrt_ftyp using solve [auto] : lngen.

Lemma open_fexp_wrt_fexp_close_fexp_wrt_fexp :
forall e1 x1,
  open_fexp_wrt_fexp (close_fexp_wrt_fexp x1 e1) (fexp_var_f x1) = e1.
Proof.
unfold close_fexp_wrt_fexp; unfold open_fexp_wrt_fexp; default_simp.
Qed.

#[export] Hint Resolve open_fexp_wrt_fexp_close_fexp_wrt_fexp : lngen.
#[export] Hint Rewrite open_fexp_wrt_fexp_close_fexp_wrt_fexp using solve [auto] : lngen.

(* begin hide *)

Lemma open_ftyp_wrt_ftyp_rec_inj_mutual :
(forall A2 A1 X1 n1,
  X1 `notin` ftvar_in_ftyp A2 ->
  X1 `notin` ftvar_in_ftyp A1 ->
  open_ftyp_wrt_ftyp_rec n1 (ftyp_var_f X1) A2 = open_ftyp_wrt_ftyp_rec n1 (ftyp_var_f X1) A1 ->
  A2 = A1).
Proof.
apply_mutual_ind ftyp_mutind;
intros; match goal with
          | |- _ = ?term => destruct term
        end;
default_simp; eauto with lngen.
Qed.

(* end hide *)

(* begin hide *)

Lemma open_ftyp_wrt_ftyp_rec_inj :
forall A2 A1 X1 n1,
  X1 `notin` ftvar_in_ftyp A2 ->
  X1 `notin` ftvar_in_ftyp A1 ->
  open_ftyp_wrt_ftyp_rec n1 (ftyp_var_f X1) A2 = open_ftyp_wrt_ftyp_rec n1 (ftyp_var_f X1) A1 ->
  A2 = A1.
Proof.
pose proof open_ftyp_wrt_ftyp_rec_inj_mutual as H; intuition eauto.
Qed.

#[export] Hint Immediate open_ftyp_wrt_ftyp_rec_inj : lngen.

(* end hide *)

(* begin hide *)

Lemma open_fexp_wrt_ftyp_rec_inj_mutual :
(forall e2 e1 X1 n1,
  X1 `notin` ftvar_in_fexp e2 ->
  X1 `notin` ftvar_in_fexp e1 ->
  open_fexp_wrt_ftyp_rec n1 (ftyp_var_f X1) e2 = open_fexp_wrt_ftyp_rec n1 (ftyp_var_f X1) e1 ->
  e2 = e1).
Proof.
apply_mutual_ind fexp_mutind;
intros; match goal with
          | |- _ = ?term => destruct term
        end;
default_simp; eauto with lngen.
Qed.

(* end hide *)

(* begin hide *)

Lemma open_fexp_wrt_ftyp_rec_inj :
forall e2 e1 X1 n1,
  X1 `notin` ftvar_in_fexp e2 ->
  X1 `notin` ftvar_in_fexp e1 ->
  open_fexp_wrt_ftyp_rec n1 (ftyp_var_f X1) e2 = open_fexp_wrt_ftyp_rec n1 (ftyp_var_f X1) e1 ->
  e2 = e1.
Proof.
pose proof open_fexp_wrt_ftyp_rec_inj_mutual as H; intuition eauto.
Qed.

#[export] Hint Immediate open_fexp_wrt_ftyp_rec_inj : lngen.

(* end hide *)

(* begin hide *)

Lemma open_fexp_wrt_fexp_rec_inj_mutual :
(forall e2 e1 x1 n1,
  x1 `notin` fvar_in_fexp e2 ->
  x1 `notin` fvar_in_fexp e1 ->
  open_fexp_wrt_fexp_rec n1 (fexp_var_f x1) e2 = open_fexp_wrt_fexp_rec n1 (fexp_var_f x1) e1 ->
  e2 = e1).
Proof.
apply_mutual_ind fexp_mutind;
intros; match goal with
          | |- _ = ?term => destruct term
        end;
default_simp; eauto with lngen.
Qed.

(* end hide *)

(* begin hide *)

Lemma open_fexp_wrt_fexp_rec_inj :
forall e2 e1 x1 n1,
  x1 `notin` fvar_in_fexp e2 ->
  x1 `notin` fvar_in_fexp e1 ->
  open_fexp_wrt_fexp_rec n1 (fexp_var_f x1) e2 = open_fexp_wrt_fexp_rec n1 (fexp_var_f x1) e1 ->
  e2 = e1.
Proof.
pose proof open_fexp_wrt_fexp_rec_inj_mutual as H; intuition eauto.
Qed.

#[export] Hint Immediate open_fexp_wrt_fexp_rec_inj : lngen.

(* end hide *)

Lemma open_ftyp_wrt_ftyp_inj :
forall A2 A1 X1,
  X1 `notin` ftvar_in_ftyp A2 ->
  X1 `notin` ftvar_in_ftyp A1 ->
  open_ftyp_wrt_ftyp A2 (ftyp_var_f X1) = open_ftyp_wrt_ftyp A1 (ftyp_var_f X1) ->
  A2 = A1.
Proof.
unfold open_ftyp_wrt_ftyp; eauto with lngen.
Qed.

#[export] Hint Immediate open_ftyp_wrt_ftyp_inj : lngen.

Lemma open_fexp_wrt_ftyp_inj :
forall e2 e1 X1,
  X1 `notin` ftvar_in_fexp e2 ->
  X1 `notin` ftvar_in_fexp e1 ->
  open_fexp_wrt_ftyp e2 (ftyp_var_f X1) = open_fexp_wrt_ftyp e1 (ftyp_var_f X1) ->
  e2 = e1.
Proof.
unfold open_fexp_wrt_ftyp; eauto with lngen.
Qed.

#[export] Hint Immediate open_fexp_wrt_ftyp_inj : lngen.

Lemma open_fexp_wrt_fexp_inj :
forall e2 e1 x1,
  x1 `notin` fvar_in_fexp e2 ->
  x1 `notin` fvar_in_fexp e1 ->
  open_fexp_wrt_fexp e2 (fexp_var_f x1) = open_fexp_wrt_fexp e1 (fexp_var_f x1) ->
  e2 = e1.
Proof.
unfold open_fexp_wrt_fexp; eauto with lngen.
Qed.

#[export] Hint Immediate open_fexp_wrt_fexp_inj : lngen.


(* *********************************************************************** *)
(** * Theorems about [lc] *)

Ltac default_auto ::= auto with lngen brute_force; tauto.
Ltac default_autorewrite ::= autorewrite with lngen.

(* begin hide *)

Lemma degree_ftyp_wrt_ftyp_of_lc_ftyp_mutual :
(forall A1,
  lc_ftyp A1 ->
  degree_ftyp_wrt_ftyp 0 A1).
Proof.
apply_mutual_ind lc_ftyp_mutind;
intros;
let X1 := fresh "X1" in pick_fresh X1;
repeat (match goal with
          | H1 : _, H2 : _ |- _ => specialize H1 with H2
        end);
default_simp; eauto with lngen.
Qed.

(* end hide *)

Lemma degree_ftyp_wrt_ftyp_of_lc_ftyp :
forall A1,
  lc_ftyp A1 ->
  degree_ftyp_wrt_ftyp 0 A1.
Proof.
pose proof degree_ftyp_wrt_ftyp_of_lc_ftyp_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve degree_ftyp_wrt_ftyp_of_lc_ftyp : lngen.

(* begin hide *)

Lemma degree_fexp_wrt_ftyp_of_lc_fexp_mutual :
(forall e1,
  lc_fexp e1 ->
  degree_fexp_wrt_ftyp 0 e1).
Proof.
apply_mutual_ind lc_fexp_mutind;
intros;
let X1 := fresh "X1" in pick_fresh X1;
let x1 := fresh "x1" in pick_fresh x1;
repeat (match goal with
          | H1 : _, H2 : _ |- _ => specialize H1 with H2
        end);
default_simp; eauto with lngen.
Qed.

(* end hide *)

Lemma degree_fexp_wrt_ftyp_of_lc_fexp :
forall e1,
  lc_fexp e1 ->
  degree_fexp_wrt_ftyp 0 e1.
Proof.
pose proof degree_fexp_wrt_ftyp_of_lc_fexp_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve degree_fexp_wrt_ftyp_of_lc_fexp : lngen.

(* begin hide *)

Lemma degree_fexp_wrt_fexp_of_lc_fexp_mutual :
(forall e1,
  lc_fexp e1 ->
  degree_fexp_wrt_fexp 0 e1).
Proof.
apply_mutual_ind lc_fexp_mutind;
intros;
let X1 := fresh "X1" in pick_fresh X1;
let x1 := fresh "x1" in pick_fresh x1;
repeat (match goal with
          | H1 : _, H2 : _ |- _ => specialize H1 with H2
        end);
default_simp; eauto with lngen.
Qed.

(* end hide *)

Lemma degree_fexp_wrt_fexp_of_lc_fexp :
forall e1,
  lc_fexp e1 ->
  degree_fexp_wrt_fexp 0 e1.
Proof.
pose proof degree_fexp_wrt_fexp_of_lc_fexp_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve degree_fexp_wrt_fexp_of_lc_fexp : lngen.

(* begin hide *)

Lemma lc_ftyp_of_degree_size_mutual :
forall i1,
(forall A1,
  size_ftyp A1 = i1 ->
  degree_ftyp_wrt_ftyp 0 A1 ->
  lc_ftyp A1).
Proof.
intros i1; pattern i1; apply lt_wf_rec;
clear i1; intros i1 H1;
apply_mutual_ind ftyp_mutind;
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

Lemma lc_ftyp_of_degree :
forall A1,
  degree_ftyp_wrt_ftyp 0 A1 ->
  lc_ftyp A1.
Proof.
intros A1; intros;
pose proof (lc_ftyp_of_degree_size_mutual (size_ftyp A1));
intuition eauto.
Qed.

#[export] Hint Resolve lc_ftyp_of_degree : lngen.

(* begin hide *)

Lemma lc_fexp_of_degree_size_mutual :
forall i1,
(forall e1,
  size_fexp e1 = i1 ->
  degree_fexp_wrt_ftyp 0 e1 ->
  degree_fexp_wrt_fexp 0 e1 ->
  lc_fexp e1).
Proof.
intros i1; pattern i1; apply lt_wf_rec;
clear i1; intros i1 H1;
apply_mutual_ind fexp_mutind;
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

Lemma lc_fexp_of_degree :
forall e1,
  degree_fexp_wrt_ftyp 0 e1 ->
  degree_fexp_wrt_fexp 0 e1 ->
  lc_fexp e1.
Proof.
intros e1; intros;
pose proof (lc_fexp_of_degree_size_mutual (size_fexp e1));
intuition eauto.
Qed.

#[export] Hint Resolve lc_fexp_of_degree : lngen.

Ltac ftyp_lc_exists_tac :=
  repeat (match goal with
            | H : _ |- _ =>
              let J1 := fresh in pose proof H as J1; apply degree_ftyp_wrt_ftyp_of_lc_ftyp in J1; clear H
          end).

Ltac fexp_lc_exists_tac :=
  repeat (match goal with
            | H : _ |- _ =>
              let J1 := fresh in pose proof H as J1; apply degree_fexp_wrt_ftyp_of_lc_fexp in J1;
              let J2 := fresh in pose proof H as J2; apply degree_fexp_wrt_fexp_of_lc_fexp in J2; clear H
          end).

Lemma lc_ftyp_all_exists :
forall X1 A1,
  lc_ftyp (open_ftyp_wrt_ftyp A1 (ftyp_var_f X1)) ->
  lc_ftyp (ftyp_all A1).
Proof.
intros; ftyp_lc_exists_tac; eauto 6 with lngen.
Qed.

Lemma lc_fexp_abs_exists :
forall x1 A1 e1,
  lc_ftyp A1 ->
  lc_fexp (open_fexp_wrt_fexp e1 (fexp_var_f x1)) ->
  lc_fexp (fexp_abs A1 e1).
Proof.
intros; fexp_lc_exists_tac; eauto 6 with lngen.
Qed.

Lemma lc_fexp_tabs_exists :
forall X1 e1,
  lc_fexp (open_fexp_wrt_ftyp e1 (ftyp_var_f X1)) ->
  lc_fexp (fexp_tabs e1).
Proof.
intros; fexp_lc_exists_tac; eauto 6 with lngen.
Qed.

#[export] Hint Extern 1 (lc_ftyp (ftyp_all _)) =>
  let X1 := fresh in
  pick_fresh X1;
  apply (lc_ftyp_all_exists X1) : core.

#[export] Hint Extern 1 (lc_fexp (fexp_abs _ _)) =>
  let x1 := fresh in
  pick_fresh x1;
  apply (lc_fexp_abs_exists x1) : core.

#[export] Hint Extern 1 (lc_fexp (fexp_tabs _)) =>
  let X1 := fresh in
  pick_fresh X1;
  apply (lc_fexp_tabs_exists X1) : core.

Lemma lc_body_ftyp_wrt_ftyp :
forall A1 A2,
  body_ftyp_wrt_ftyp A1 ->
  lc_ftyp A2 ->
  lc_ftyp (open_ftyp_wrt_ftyp A1 A2).
Proof.
unfold body_ftyp_wrt_ftyp;
default_simp;
let X1 := fresh "x" in
pick_fresh X1;
specialize_all X1;
ftyp_lc_exists_tac;
eauto 7 with lngen.
Qed.

#[export] Hint Resolve lc_body_ftyp_wrt_ftyp : lngen.

Lemma lc_body_fexp_wrt_ftyp :
forall e1 A1,
  body_fexp_wrt_ftyp e1 ->
  lc_ftyp A1 ->
  lc_fexp (open_fexp_wrt_ftyp e1 A1).
Proof.
unfold body_fexp_wrt_ftyp;
default_simp;
let X1 := fresh "x" in
pick_fresh X1;
specialize_all X1;
fexp_lc_exists_tac;
eauto 7 with lngen.
Qed.

#[export] Hint Resolve lc_body_fexp_wrt_ftyp : lngen.

Lemma lc_body_fexp_wrt_fexp :
forall e1 e2,
  body_fexp_wrt_fexp e1 ->
  lc_fexp e2 ->
  lc_fexp (open_fexp_wrt_fexp e1 e2).
Proof.
unfold body_fexp_wrt_fexp;
default_simp;
let x1 := fresh "x" in
pick_fresh x1;
specialize_all x1;
fexp_lc_exists_tac;
eauto 7 with lngen.
Qed.

#[export] Hint Resolve lc_body_fexp_wrt_fexp : lngen.

Lemma lc_body_ftyp_all_1 :
forall A1,
  lc_ftyp (ftyp_all A1) ->
  body_ftyp_wrt_ftyp A1.
Proof.
default_simp.
Qed.

#[export] Hint Resolve lc_body_ftyp_all_1 : lngen.

Lemma lc_body_fexp_abs_2 :
forall A1 e1,
  lc_fexp (fexp_abs A1 e1) ->
  body_fexp_wrt_fexp e1.
Proof.
default_simp.
Qed.

#[export] Hint Resolve lc_body_fexp_abs_2 : lngen.

Lemma lc_body_fexp_tabs_1 :
forall e1,
  lc_fexp (fexp_tabs e1) ->
  body_fexp_wrt_ftyp e1.
Proof.
default_simp.
Qed.

#[export] Hint Resolve lc_body_fexp_tabs_1 : lngen.

(* begin hide *)

Lemma lc_ftyp_unique_mutual :
(forall A1 (proof2 proof3 : lc_ftyp A1), proof2 = proof3).
Proof.
apply_mutual_ind lc_ftyp_mutind;
intros;
let proof1 := fresh "proof1" in
rename_last_into proof1; dependent destruction proof1;
f_equal; default_simp; auto using @functional_extensionality_dep with lngen.
Qed.

(* end hide *)

Lemma lc_ftyp_unique :
forall A1 (proof2 proof3 : lc_ftyp A1), proof2 = proof3.
Proof.
pose proof lc_ftyp_unique_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve lc_ftyp_unique : lngen.

(* begin hide *)

Lemma lc_fexp_unique_mutual :
(forall e1 (proof2 proof3 : lc_fexp e1), proof2 = proof3).
Proof.
apply_mutual_ind lc_fexp_mutind;
intros;
let proof1 := fresh "proof1" in
rename_last_into proof1; dependent destruction proof1;
f_equal; default_simp; auto using @functional_extensionality_dep with lngen.
Qed.

(* end hide *)

Lemma lc_fexp_unique :
forall e1 (proof2 proof3 : lc_fexp e1), proof2 = proof3.
Proof.
pose proof lc_fexp_unique_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve lc_fexp_unique : lngen.

(* begin hide *)

Lemma lc_ftyp_of_lc_set_ftyp_mutual :
(forall A1, lc_set_ftyp A1 -> lc_ftyp A1).
Proof.
apply_mutual_ind lc_set_ftyp_mutind;
default_simp.
Qed.

(* end hide *)

Lemma lc_ftyp_of_lc_set_ftyp :
forall A1, lc_set_ftyp A1 -> lc_ftyp A1.
Proof.
pose proof lc_ftyp_of_lc_set_ftyp_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve lc_ftyp_of_lc_set_ftyp : lngen.

(* begin hide *)

Lemma lc_fexp_of_lc_set_fexp_mutual :
(forall e1, lc_set_fexp e1 -> lc_fexp e1).
Proof.
apply_mutual_ind lc_set_fexp_mutind;
default_simp.
Qed.

(* end hide *)

Lemma lc_fexp_of_lc_set_fexp :
forall e1, lc_set_fexp e1 -> lc_fexp e1.
Proof.
pose proof lc_fexp_of_lc_set_fexp_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve lc_fexp_of_lc_set_fexp : lngen.

(* begin hide *)

Lemma lc_set_ftyp_of_lc_ftyp_size_mutual :
forall i1,
(forall A1,
  size_ftyp A1 = i1 ->
  lc_ftyp A1 ->
  lc_set_ftyp A1).
Proof.
intros i1; pattern i1; apply lt_wf_rec;
clear i1; intros i1 H1;
apply_mutual_ind ftyp_mutrec;
default_simp;
try solve [assert False by default_simp; tauto];
(* non-trivial cases *)
constructor; default_simp;
try first [apply lc_set_ftyp_of_lc_ftyp];
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

Lemma lc_set_ftyp_of_lc_ftyp :
forall A1,
  lc_ftyp A1 ->
  lc_set_ftyp A1.
Proof.
intros A1; intros;
pose proof (lc_set_ftyp_of_lc_ftyp_size_mutual (size_ftyp A1));
intuition eauto.
Qed.

#[export] Hint Resolve lc_set_ftyp_of_lc_ftyp : lngen.

(* begin hide *)

Lemma lc_set_fexp_of_lc_fexp_size_mutual :
forall i1,
(forall e1,
  size_fexp e1 = i1 ->
  lc_fexp e1 ->
  lc_set_fexp e1).
Proof.
intros i1; pattern i1; apply lt_wf_rec;
clear i1; intros i1 H1;
apply_mutual_ind fexp_mutrec;
default_simp;
try solve [assert False by default_simp; tauto];
(* non-trivial cases *)
constructor; default_simp;
try first [apply lc_set_ftyp_of_lc_ftyp
 | apply lc_set_fexp_of_lc_fexp];
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

Lemma lc_set_fexp_of_lc_fexp :
forall e1,
  lc_fexp e1 ->
  lc_set_fexp e1.
Proof.
intros e1; intros;
pose proof (lc_set_fexp_of_lc_fexp_size_mutual (size_fexp e1));
intuition eauto.
Qed.

#[export] Hint Resolve lc_set_fexp_of_lc_fexp : lngen.


(* *********************************************************************** *)
(** * More theorems about [open] and [close] *)

Ltac default_auto ::= auto with lngen; tauto.
Ltac default_autorewrite ::= fail.

(* begin hide *)

Lemma close_ftyp_wrt_ftyp_rec_degree_ftyp_wrt_ftyp_mutual :
(forall A1 X1 n1,
  degree_ftyp_wrt_ftyp n1 A1 ->
  X1 `notin` ftvar_in_ftyp A1 ->
  close_ftyp_wrt_ftyp_rec n1 X1 A1 = A1).
Proof.
apply_mutual_ind ftyp_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma close_ftyp_wrt_ftyp_rec_degree_ftyp_wrt_ftyp :
forall A1 X1 n1,
  degree_ftyp_wrt_ftyp n1 A1 ->
  X1 `notin` ftvar_in_ftyp A1 ->
  close_ftyp_wrt_ftyp_rec n1 X1 A1 = A1.
Proof.
pose proof close_ftyp_wrt_ftyp_rec_degree_ftyp_wrt_ftyp_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve close_ftyp_wrt_ftyp_rec_degree_ftyp_wrt_ftyp : lngen.
#[export] Hint Rewrite close_ftyp_wrt_ftyp_rec_degree_ftyp_wrt_ftyp using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma close_fexp_wrt_ftyp_rec_degree_fexp_wrt_ftyp_mutual :
(forall e1 X1 n1,
  degree_fexp_wrt_ftyp n1 e1 ->
  X1 `notin` ftvar_in_fexp e1 ->
  close_fexp_wrt_ftyp_rec n1 X1 e1 = e1).
Proof.
apply_mutual_ind fexp_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma close_fexp_wrt_ftyp_rec_degree_fexp_wrt_ftyp :
forall e1 X1 n1,
  degree_fexp_wrt_ftyp n1 e1 ->
  X1 `notin` ftvar_in_fexp e1 ->
  close_fexp_wrt_ftyp_rec n1 X1 e1 = e1.
Proof.
pose proof close_fexp_wrt_ftyp_rec_degree_fexp_wrt_ftyp_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve close_fexp_wrt_ftyp_rec_degree_fexp_wrt_ftyp : lngen.
#[export] Hint Rewrite close_fexp_wrt_ftyp_rec_degree_fexp_wrt_ftyp using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma close_fexp_wrt_fexp_rec_degree_fexp_wrt_fexp_mutual :
(forall e1 x1 n1,
  degree_fexp_wrt_fexp n1 e1 ->
  x1 `notin` fvar_in_fexp e1 ->
  close_fexp_wrt_fexp_rec n1 x1 e1 = e1).
Proof.
apply_mutual_ind fexp_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma close_fexp_wrt_fexp_rec_degree_fexp_wrt_fexp :
forall e1 x1 n1,
  degree_fexp_wrt_fexp n1 e1 ->
  x1 `notin` fvar_in_fexp e1 ->
  close_fexp_wrt_fexp_rec n1 x1 e1 = e1.
Proof.
pose proof close_fexp_wrt_fexp_rec_degree_fexp_wrt_fexp_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve close_fexp_wrt_fexp_rec_degree_fexp_wrt_fexp : lngen.
#[export] Hint Rewrite close_fexp_wrt_fexp_rec_degree_fexp_wrt_fexp using solve [auto] : lngen.

(* end hide *)

Lemma close_ftyp_wrt_ftyp_lc_ftyp :
forall A1 X1,
  lc_ftyp A1 ->
  X1 `notin` ftvar_in_ftyp A1 ->
  close_ftyp_wrt_ftyp X1 A1 = A1.
Proof.
unfold close_ftyp_wrt_ftyp; default_simp.
Qed.

#[export] Hint Resolve close_ftyp_wrt_ftyp_lc_ftyp : lngen.
#[export] Hint Rewrite close_ftyp_wrt_ftyp_lc_ftyp using solve [auto] : lngen.

Lemma close_fexp_wrt_ftyp_lc_fexp :
forall e1 X1,
  lc_fexp e1 ->
  X1 `notin` ftvar_in_fexp e1 ->
  close_fexp_wrt_ftyp X1 e1 = e1.
Proof.
unfold close_fexp_wrt_ftyp; default_simp.
Qed.

#[export] Hint Resolve close_fexp_wrt_ftyp_lc_fexp : lngen.
#[export] Hint Rewrite close_fexp_wrt_ftyp_lc_fexp using solve [auto] : lngen.

Lemma close_fexp_wrt_fexp_lc_fexp :
forall e1 x1,
  lc_fexp e1 ->
  x1 `notin` fvar_in_fexp e1 ->
  close_fexp_wrt_fexp x1 e1 = e1.
Proof.
unfold close_fexp_wrt_fexp; default_simp.
Qed.

#[export] Hint Resolve close_fexp_wrt_fexp_lc_fexp : lngen.
#[export] Hint Rewrite close_fexp_wrt_fexp_lc_fexp using solve [auto] : lngen.

(* begin hide *)

Lemma open_ftyp_wrt_ftyp_rec_degree_ftyp_wrt_ftyp_mutual :
(forall A2 A1 n1,
  degree_ftyp_wrt_ftyp n1 A2 ->
  open_ftyp_wrt_ftyp_rec n1 A1 A2 = A2).
Proof.
apply_mutual_ind ftyp_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma open_ftyp_wrt_ftyp_rec_degree_ftyp_wrt_ftyp :
forall A2 A1 n1,
  degree_ftyp_wrt_ftyp n1 A2 ->
  open_ftyp_wrt_ftyp_rec n1 A1 A2 = A2.
Proof.
pose proof open_ftyp_wrt_ftyp_rec_degree_ftyp_wrt_ftyp_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve open_ftyp_wrt_ftyp_rec_degree_ftyp_wrt_ftyp : lngen.
#[export] Hint Rewrite open_ftyp_wrt_ftyp_rec_degree_ftyp_wrt_ftyp using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma open_fexp_wrt_ftyp_rec_degree_fexp_wrt_ftyp_mutual :
(forall e1 A1 n1,
  degree_fexp_wrt_ftyp n1 e1 ->
  open_fexp_wrt_ftyp_rec n1 A1 e1 = e1).
Proof.
apply_mutual_ind fexp_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma open_fexp_wrt_ftyp_rec_degree_fexp_wrt_ftyp :
forall e1 A1 n1,
  degree_fexp_wrt_ftyp n1 e1 ->
  open_fexp_wrt_ftyp_rec n1 A1 e1 = e1.
Proof.
pose proof open_fexp_wrt_ftyp_rec_degree_fexp_wrt_ftyp_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve open_fexp_wrt_ftyp_rec_degree_fexp_wrt_ftyp : lngen.
#[export] Hint Rewrite open_fexp_wrt_ftyp_rec_degree_fexp_wrt_ftyp using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma open_fexp_wrt_fexp_rec_degree_fexp_wrt_fexp_mutual :
(forall e2 e1 n1,
  degree_fexp_wrt_fexp n1 e2 ->
  open_fexp_wrt_fexp_rec n1 e1 e2 = e2).
Proof.
apply_mutual_ind fexp_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma open_fexp_wrt_fexp_rec_degree_fexp_wrt_fexp :
forall e2 e1 n1,
  degree_fexp_wrt_fexp n1 e2 ->
  open_fexp_wrt_fexp_rec n1 e1 e2 = e2.
Proof.
pose proof open_fexp_wrt_fexp_rec_degree_fexp_wrt_fexp_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve open_fexp_wrt_fexp_rec_degree_fexp_wrt_fexp : lngen.
#[export] Hint Rewrite open_fexp_wrt_fexp_rec_degree_fexp_wrt_fexp using solve [auto] : lngen.

(* end hide *)

Lemma open_ftyp_wrt_ftyp_lc_ftyp :
forall A2 A1,
  lc_ftyp A2 ->
  open_ftyp_wrt_ftyp A2 A1 = A2.
Proof.
unfold open_ftyp_wrt_ftyp; default_simp.
Qed.

#[export] Hint Resolve open_ftyp_wrt_ftyp_lc_ftyp : lngen.
#[export] Hint Rewrite open_ftyp_wrt_ftyp_lc_ftyp using solve [auto] : lngen.

Lemma open_fexp_wrt_ftyp_lc_fexp :
forall e1 A1,
  lc_fexp e1 ->
  open_fexp_wrt_ftyp e1 A1 = e1.
Proof.
unfold open_fexp_wrt_ftyp; default_simp.
Qed.

#[export] Hint Resolve open_fexp_wrt_ftyp_lc_fexp : lngen.
#[export] Hint Rewrite open_fexp_wrt_ftyp_lc_fexp using solve [auto] : lngen.

Lemma open_fexp_wrt_fexp_lc_fexp :
forall e2 e1,
  lc_fexp e2 ->
  open_fexp_wrt_fexp e2 e1 = e2.
Proof.
unfold open_fexp_wrt_fexp; default_simp.
Qed.

#[export] Hint Resolve open_fexp_wrt_fexp_lc_fexp : lngen.
#[export] Hint Rewrite open_fexp_wrt_fexp_lc_fexp using solve [auto] : lngen.


(* *********************************************************************** *)
(** * Theorems about [fv] *)

Ltac default_auto ::= auto with set lngen; tauto.
Ltac default_autorewrite ::= autorewrite with lngen.

(* begin hide *)

Lemma ftvar_in_ftyp_close_ftyp_wrt_ftyp_rec_mutual :
(forall A1 X1 n1,
  ftvar_in_ftyp (close_ftyp_wrt_ftyp_rec n1 X1 A1) [=] remove X1 (ftvar_in_ftyp A1)).
Proof.
apply_mutual_ind ftyp_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

(* begin hide *)

Lemma ftvar_in_ftyp_close_ftyp_wrt_ftyp_rec :
forall A1 X1 n1,
  ftvar_in_ftyp (close_ftyp_wrt_ftyp_rec n1 X1 A1) [=] remove X1 (ftvar_in_ftyp A1).
Proof.
pose proof ftvar_in_ftyp_close_ftyp_wrt_ftyp_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve ftvar_in_ftyp_close_ftyp_wrt_ftyp_rec : lngen.
#[export] Hint Rewrite ftvar_in_ftyp_close_ftyp_wrt_ftyp_rec using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma ftvar_in_fexp_close_fexp_wrt_ftyp_rec_mutual :
(forall e1 X1 n1,
  ftvar_in_fexp (close_fexp_wrt_ftyp_rec n1 X1 e1) [=] remove X1 (ftvar_in_fexp e1)).
Proof.
apply_mutual_ind fexp_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

(* begin hide *)

Lemma ftvar_in_fexp_close_fexp_wrt_ftyp_rec :
forall e1 X1 n1,
  ftvar_in_fexp (close_fexp_wrt_ftyp_rec n1 X1 e1) [=] remove X1 (ftvar_in_fexp e1).
Proof.
pose proof ftvar_in_fexp_close_fexp_wrt_ftyp_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve ftvar_in_fexp_close_fexp_wrt_ftyp_rec : lngen.
#[export] Hint Rewrite ftvar_in_fexp_close_fexp_wrt_ftyp_rec using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma ftvar_in_fexp_close_fexp_wrt_fexp_rec_mutual :
(forall e1 x1 n1,
  ftvar_in_fexp (close_fexp_wrt_fexp_rec n1 x1 e1) [=] ftvar_in_fexp e1).
Proof.
apply_mutual_ind fexp_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

(* begin hide *)

Lemma ftvar_in_fexp_close_fexp_wrt_fexp_rec :
forall e1 x1 n1,
  ftvar_in_fexp (close_fexp_wrt_fexp_rec n1 x1 e1) [=] ftvar_in_fexp e1.
Proof.
pose proof ftvar_in_fexp_close_fexp_wrt_fexp_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve ftvar_in_fexp_close_fexp_wrt_fexp_rec : lngen.
#[export] Hint Rewrite ftvar_in_fexp_close_fexp_wrt_fexp_rec using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma fvar_in_fexp_close_fexp_wrt_ftyp_rec_mutual :
(forall e1 X1 n1,
  fvar_in_fexp (close_fexp_wrt_ftyp_rec n1 X1 e1) [=] fvar_in_fexp e1).
Proof.
apply_mutual_ind fexp_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

(* begin hide *)

Lemma fvar_in_fexp_close_fexp_wrt_ftyp_rec :
forall e1 X1 n1,
  fvar_in_fexp (close_fexp_wrt_ftyp_rec n1 X1 e1) [=] fvar_in_fexp e1.
Proof.
pose proof fvar_in_fexp_close_fexp_wrt_ftyp_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve fvar_in_fexp_close_fexp_wrt_ftyp_rec : lngen.
#[export] Hint Rewrite fvar_in_fexp_close_fexp_wrt_ftyp_rec using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma fvar_in_fexp_close_fexp_wrt_fexp_rec_mutual :
(forall e1 x1 n1,
  fvar_in_fexp (close_fexp_wrt_fexp_rec n1 x1 e1) [=] remove x1 (fvar_in_fexp e1)).
Proof.
apply_mutual_ind fexp_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

(* begin hide *)

Lemma fvar_in_fexp_close_fexp_wrt_fexp_rec :
forall e1 x1 n1,
  fvar_in_fexp (close_fexp_wrt_fexp_rec n1 x1 e1) [=] remove x1 (fvar_in_fexp e1).
Proof.
pose proof fvar_in_fexp_close_fexp_wrt_fexp_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve fvar_in_fexp_close_fexp_wrt_fexp_rec : lngen.
#[export] Hint Rewrite fvar_in_fexp_close_fexp_wrt_fexp_rec using solve [auto] : lngen.

(* end hide *)

Lemma ftvar_in_ftyp_close_ftyp_wrt_ftyp :
forall A1 X1,
  ftvar_in_ftyp (close_ftyp_wrt_ftyp X1 A1) [=] remove X1 (ftvar_in_ftyp A1).
Proof.
unfold close_ftyp_wrt_ftyp; default_simp.
Qed.

#[export] Hint Resolve ftvar_in_ftyp_close_ftyp_wrt_ftyp : lngen.
#[export] Hint Rewrite ftvar_in_ftyp_close_ftyp_wrt_ftyp using solve [auto] : lngen.

Lemma ftvar_in_fexp_close_fexp_wrt_ftyp :
forall e1 X1,
  ftvar_in_fexp (close_fexp_wrt_ftyp X1 e1) [=] remove X1 (ftvar_in_fexp e1).
Proof.
unfold close_fexp_wrt_ftyp; default_simp.
Qed.

#[export] Hint Resolve ftvar_in_fexp_close_fexp_wrt_ftyp : lngen.
#[export] Hint Rewrite ftvar_in_fexp_close_fexp_wrt_ftyp using solve [auto] : lngen.

Lemma ftvar_in_fexp_close_fexp_wrt_fexp :
forall e1 x1,
  ftvar_in_fexp (close_fexp_wrt_fexp x1 e1) [=] ftvar_in_fexp e1.
Proof.
unfold close_fexp_wrt_fexp; default_simp.
Qed.

#[export] Hint Resolve ftvar_in_fexp_close_fexp_wrt_fexp : lngen.
#[export] Hint Rewrite ftvar_in_fexp_close_fexp_wrt_fexp using solve [auto] : lngen.

Lemma fvar_in_fexp_close_fexp_wrt_ftyp :
forall e1 X1,
  fvar_in_fexp (close_fexp_wrt_ftyp X1 e1) [=] fvar_in_fexp e1.
Proof.
unfold close_fexp_wrt_ftyp; default_simp.
Qed.

#[export] Hint Resolve fvar_in_fexp_close_fexp_wrt_ftyp : lngen.
#[export] Hint Rewrite fvar_in_fexp_close_fexp_wrt_ftyp using solve [auto] : lngen.

Lemma fvar_in_fexp_close_fexp_wrt_fexp :
forall e1 x1,
  fvar_in_fexp (close_fexp_wrt_fexp x1 e1) [=] remove x1 (fvar_in_fexp e1).
Proof.
unfold close_fexp_wrt_fexp; default_simp.
Qed.

#[export] Hint Resolve fvar_in_fexp_close_fexp_wrt_fexp : lngen.
#[export] Hint Rewrite fvar_in_fexp_close_fexp_wrt_fexp using solve [auto] : lngen.

(* begin hide *)

Lemma ftvar_in_ftyp_open_ftyp_wrt_ftyp_rec_lower_mutual :
(forall A1 A2 n1,
  ftvar_in_ftyp A1 [<=] ftvar_in_ftyp (open_ftyp_wrt_ftyp_rec n1 A2 A1)).
Proof.
apply_mutual_ind ftyp_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

(* begin hide *)

Lemma ftvar_in_ftyp_open_ftyp_wrt_ftyp_rec_lower :
forall A1 A2 n1,
  ftvar_in_ftyp A1 [<=] ftvar_in_ftyp (open_ftyp_wrt_ftyp_rec n1 A2 A1).
Proof.
pose proof ftvar_in_ftyp_open_ftyp_wrt_ftyp_rec_lower_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve ftvar_in_ftyp_open_ftyp_wrt_ftyp_rec_lower : lngen.

(* end hide *)

(* begin hide *)

Lemma ftvar_in_fexp_open_fexp_wrt_ftyp_rec_lower_mutual :
(forall e1 A1 n1,
  ftvar_in_fexp e1 [<=] ftvar_in_fexp (open_fexp_wrt_ftyp_rec n1 A1 e1)).
Proof.
apply_mutual_ind fexp_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

(* begin hide *)

Lemma ftvar_in_fexp_open_fexp_wrt_ftyp_rec_lower :
forall e1 A1 n1,
  ftvar_in_fexp e1 [<=] ftvar_in_fexp (open_fexp_wrt_ftyp_rec n1 A1 e1).
Proof.
pose proof ftvar_in_fexp_open_fexp_wrt_ftyp_rec_lower_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve ftvar_in_fexp_open_fexp_wrt_ftyp_rec_lower : lngen.

(* end hide *)

(* begin hide *)

Lemma ftvar_in_fexp_open_fexp_wrt_fexp_rec_lower_mutual :
(forall e1 e2 n1,
  ftvar_in_fexp e1 [<=] ftvar_in_fexp (open_fexp_wrt_fexp_rec n1 e2 e1)).
Proof.
apply_mutual_ind fexp_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

(* begin hide *)

Lemma ftvar_in_fexp_open_fexp_wrt_fexp_rec_lower :
forall e1 e2 n1,
  ftvar_in_fexp e1 [<=] ftvar_in_fexp (open_fexp_wrt_fexp_rec n1 e2 e1).
Proof.
pose proof ftvar_in_fexp_open_fexp_wrt_fexp_rec_lower_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve ftvar_in_fexp_open_fexp_wrt_fexp_rec_lower : lngen.

(* end hide *)

(* begin hide *)

Lemma fvar_in_fexp_open_fexp_wrt_ftyp_rec_lower_mutual :
(forall e1 A1 n1,
  fvar_in_fexp e1 [<=] fvar_in_fexp (open_fexp_wrt_ftyp_rec n1 A1 e1)).
Proof.
apply_mutual_ind fexp_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

(* begin hide *)

Lemma fvar_in_fexp_open_fexp_wrt_ftyp_rec_lower :
forall e1 A1 n1,
  fvar_in_fexp e1 [<=] fvar_in_fexp (open_fexp_wrt_ftyp_rec n1 A1 e1).
Proof.
pose proof fvar_in_fexp_open_fexp_wrt_ftyp_rec_lower_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve fvar_in_fexp_open_fexp_wrt_ftyp_rec_lower : lngen.

(* end hide *)

(* begin hide *)

Lemma fvar_in_fexp_open_fexp_wrt_fexp_rec_lower_mutual :
(forall e1 e2 n1,
  fvar_in_fexp e1 [<=] fvar_in_fexp (open_fexp_wrt_fexp_rec n1 e2 e1)).
Proof.
apply_mutual_ind fexp_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

(* begin hide *)

Lemma fvar_in_fexp_open_fexp_wrt_fexp_rec_lower :
forall e1 e2 n1,
  fvar_in_fexp e1 [<=] fvar_in_fexp (open_fexp_wrt_fexp_rec n1 e2 e1).
Proof.
pose proof fvar_in_fexp_open_fexp_wrt_fexp_rec_lower_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve fvar_in_fexp_open_fexp_wrt_fexp_rec_lower : lngen.

(* end hide *)

Lemma ftvar_in_ftyp_open_ftyp_wrt_ftyp_lower :
forall A1 A2,
  ftvar_in_ftyp A1 [<=] ftvar_in_ftyp (open_ftyp_wrt_ftyp A1 A2).
Proof.
unfold open_ftyp_wrt_ftyp; default_simp.
Qed.

#[export] Hint Resolve ftvar_in_ftyp_open_ftyp_wrt_ftyp_lower : lngen.

Lemma ftvar_in_fexp_open_fexp_wrt_ftyp_lower :
forall e1 A1,
  ftvar_in_fexp e1 [<=] ftvar_in_fexp (open_fexp_wrt_ftyp e1 A1).
Proof.
unfold open_fexp_wrt_ftyp; default_simp.
Qed.

#[export] Hint Resolve ftvar_in_fexp_open_fexp_wrt_ftyp_lower : lngen.

Lemma ftvar_in_fexp_open_fexp_wrt_fexp_lower :
forall e1 e2,
  ftvar_in_fexp e1 [<=] ftvar_in_fexp (open_fexp_wrt_fexp e1 e2).
Proof.
unfold open_fexp_wrt_fexp; default_simp.
Qed.

#[export] Hint Resolve ftvar_in_fexp_open_fexp_wrt_fexp_lower : lngen.

Lemma fvar_in_fexp_open_fexp_wrt_ftyp_lower :
forall e1 A1,
  fvar_in_fexp e1 [<=] fvar_in_fexp (open_fexp_wrt_ftyp e1 A1).
Proof.
unfold open_fexp_wrt_ftyp; default_simp.
Qed.

#[export] Hint Resolve fvar_in_fexp_open_fexp_wrt_ftyp_lower : lngen.

Lemma fvar_in_fexp_open_fexp_wrt_fexp_lower :
forall e1 e2,
  fvar_in_fexp e1 [<=] fvar_in_fexp (open_fexp_wrt_fexp e1 e2).
Proof.
unfold open_fexp_wrt_fexp; default_simp.
Qed.

#[export] Hint Resolve fvar_in_fexp_open_fexp_wrt_fexp_lower : lngen.

(* begin hide *)

Lemma ftvar_in_ftyp_open_ftyp_wrt_ftyp_rec_upper_mutual :
(forall A1 A2 n1,
  ftvar_in_ftyp (open_ftyp_wrt_ftyp_rec n1 A2 A1) [<=] ftvar_in_ftyp A2 `union` ftvar_in_ftyp A1).
Proof.
apply_mutual_ind ftyp_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

(* begin hide *)

Lemma ftvar_in_ftyp_open_ftyp_wrt_ftyp_rec_upper :
forall A1 A2 n1,
  ftvar_in_ftyp (open_ftyp_wrt_ftyp_rec n1 A2 A1) [<=] ftvar_in_ftyp A2 `union` ftvar_in_ftyp A1.
Proof.
pose proof ftvar_in_ftyp_open_ftyp_wrt_ftyp_rec_upper_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve ftvar_in_ftyp_open_ftyp_wrt_ftyp_rec_upper : lngen.

(* end hide *)

(* begin hide *)

Lemma ftvar_in_fexp_open_fexp_wrt_ftyp_rec_upper_mutual :
(forall e1 A1 n1,
  ftvar_in_fexp (open_fexp_wrt_ftyp_rec n1 A1 e1) [<=] ftvar_in_ftyp A1 `union` ftvar_in_fexp e1).
Proof.
apply_mutual_ind fexp_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

(* begin hide *)

Lemma ftvar_in_fexp_open_fexp_wrt_ftyp_rec_upper :
forall e1 A1 n1,
  ftvar_in_fexp (open_fexp_wrt_ftyp_rec n1 A1 e1) [<=] ftvar_in_ftyp A1 `union` ftvar_in_fexp e1.
Proof.
pose proof ftvar_in_fexp_open_fexp_wrt_ftyp_rec_upper_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve ftvar_in_fexp_open_fexp_wrt_ftyp_rec_upper : lngen.

(* end hide *)

(* begin hide *)

Lemma ftvar_in_fexp_open_fexp_wrt_fexp_rec_upper_mutual :
(forall e1 e2 n1,
  ftvar_in_fexp (open_fexp_wrt_fexp_rec n1 e2 e1) [<=] ftvar_in_fexp e2 `union` ftvar_in_fexp e1).
Proof.
apply_mutual_ind fexp_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

(* begin hide *)

Lemma ftvar_in_fexp_open_fexp_wrt_fexp_rec_upper :
forall e1 e2 n1,
  ftvar_in_fexp (open_fexp_wrt_fexp_rec n1 e2 e1) [<=] ftvar_in_fexp e2 `union` ftvar_in_fexp e1.
Proof.
pose proof ftvar_in_fexp_open_fexp_wrt_fexp_rec_upper_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve ftvar_in_fexp_open_fexp_wrt_fexp_rec_upper : lngen.

(* end hide *)

(* begin hide *)

Lemma fvar_in_fexp_open_fexp_wrt_ftyp_rec_upper_mutual :
(forall e1 A1 n1,
  fvar_in_fexp (open_fexp_wrt_ftyp_rec n1 A1 e1) [<=] fvar_in_fexp e1).
Proof.
apply_mutual_ind fexp_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

(* begin hide *)

Lemma fvar_in_fexp_open_fexp_wrt_ftyp_rec_upper :
forall e1 A1 n1,
  fvar_in_fexp (open_fexp_wrt_ftyp_rec n1 A1 e1) [<=] fvar_in_fexp e1.
Proof.
pose proof fvar_in_fexp_open_fexp_wrt_ftyp_rec_upper_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve fvar_in_fexp_open_fexp_wrt_ftyp_rec_upper : lngen.

(* end hide *)

(* begin hide *)

Lemma fvar_in_fexp_open_fexp_wrt_fexp_rec_upper_mutual :
(forall e1 e2 n1,
  fvar_in_fexp (open_fexp_wrt_fexp_rec n1 e2 e1) [<=] fvar_in_fexp e2 `union` fvar_in_fexp e1).
Proof.
apply_mutual_ind fexp_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

(* begin hide *)

Lemma fvar_in_fexp_open_fexp_wrt_fexp_rec_upper :
forall e1 e2 n1,
  fvar_in_fexp (open_fexp_wrt_fexp_rec n1 e2 e1) [<=] fvar_in_fexp e2 `union` fvar_in_fexp e1.
Proof.
pose proof fvar_in_fexp_open_fexp_wrt_fexp_rec_upper_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve fvar_in_fexp_open_fexp_wrt_fexp_rec_upper : lngen.

(* end hide *)

Lemma ftvar_in_ftyp_open_ftyp_wrt_ftyp_upper :
forall A1 A2,
  ftvar_in_ftyp (open_ftyp_wrt_ftyp A1 A2) [<=] ftvar_in_ftyp A2 `union` ftvar_in_ftyp A1.
Proof.
unfold open_ftyp_wrt_ftyp; default_simp.
Qed.

#[export] Hint Resolve ftvar_in_ftyp_open_ftyp_wrt_ftyp_upper : lngen.

Lemma ftvar_in_fexp_open_fexp_wrt_ftyp_upper :
forall e1 A1,
  ftvar_in_fexp (open_fexp_wrt_ftyp e1 A1) [<=] ftvar_in_ftyp A1 `union` ftvar_in_fexp e1.
Proof.
unfold open_fexp_wrt_ftyp; default_simp.
Qed.

#[export] Hint Resolve ftvar_in_fexp_open_fexp_wrt_ftyp_upper : lngen.

Lemma ftvar_in_fexp_open_fexp_wrt_fexp_upper :
forall e1 e2,
  ftvar_in_fexp (open_fexp_wrt_fexp e1 e2) [<=] ftvar_in_fexp e2 `union` ftvar_in_fexp e1.
Proof.
unfold open_fexp_wrt_fexp; default_simp.
Qed.

#[export] Hint Resolve ftvar_in_fexp_open_fexp_wrt_fexp_upper : lngen.

Lemma fvar_in_fexp_open_fexp_wrt_ftyp_upper :
forall e1 A1,
  fvar_in_fexp (open_fexp_wrt_ftyp e1 A1) [<=] fvar_in_fexp e1.
Proof.
unfold open_fexp_wrt_ftyp; default_simp.
Qed.

#[export] Hint Resolve fvar_in_fexp_open_fexp_wrt_ftyp_upper : lngen.

Lemma fvar_in_fexp_open_fexp_wrt_fexp_upper :
forall e1 e2,
  fvar_in_fexp (open_fexp_wrt_fexp e1 e2) [<=] fvar_in_fexp e2 `union` fvar_in_fexp e1.
Proof.
unfold open_fexp_wrt_fexp; default_simp.
Qed.

#[export] Hint Resolve fvar_in_fexp_open_fexp_wrt_fexp_upper : lngen.

(* begin hide *)

Lemma ftvar_in_ftyp_subst_ftyp_in_ftyp_fresh_mutual :
(forall A1 A2 X1,
  X1 `notin` ftvar_in_ftyp A1 ->
  ftvar_in_ftyp (subst_ftyp_in_ftyp A2 X1 A1) [=] ftvar_in_ftyp A1).
Proof.
apply_mutual_ind ftyp_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

Lemma ftvar_in_ftyp_subst_ftyp_in_ftyp_fresh :
forall A1 A2 X1,
  X1 `notin` ftvar_in_ftyp A1 ->
  ftvar_in_ftyp (subst_ftyp_in_ftyp A2 X1 A1) [=] ftvar_in_ftyp A1.
Proof.
pose proof ftvar_in_ftyp_subst_ftyp_in_ftyp_fresh_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve ftvar_in_ftyp_subst_ftyp_in_ftyp_fresh : lngen.
#[export] Hint Rewrite ftvar_in_ftyp_subst_ftyp_in_ftyp_fresh using solve [auto] : lngen.

(* begin hide *)

Lemma ftvar_in_fexp_subst_ftyp_in_fexp_fresh_mutual :
(forall e1 A1 X1,
  X1 `notin` ftvar_in_fexp e1 ->
  ftvar_in_fexp (subst_ftyp_in_fexp A1 X1 e1) [=] ftvar_in_fexp e1).
Proof.
apply_mutual_ind fexp_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

Lemma ftvar_in_fexp_subst_ftyp_in_fexp_fresh :
forall e1 A1 X1,
  X1 `notin` ftvar_in_fexp e1 ->
  ftvar_in_fexp (subst_ftyp_in_fexp A1 X1 e1) [=] ftvar_in_fexp e1.
Proof.
pose proof ftvar_in_fexp_subst_ftyp_in_fexp_fresh_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve ftvar_in_fexp_subst_ftyp_in_fexp_fresh : lngen.
#[export] Hint Rewrite ftvar_in_fexp_subst_ftyp_in_fexp_fresh using solve [auto] : lngen.

(* begin hide *)

Lemma ftvar_in_fexp_subst_fexp_in_fexp_fresh_mutual :
(forall e1 A1 X1,
  fvar_in_fexp (subst_ftyp_in_fexp A1 X1 e1) [=] fvar_in_fexp e1).
Proof.
apply_mutual_ind fexp_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

Lemma ftvar_in_fexp_subst_fexp_in_fexp_fresh :
forall e1 A1 X1,
  fvar_in_fexp (subst_ftyp_in_fexp A1 X1 e1) [=] fvar_in_fexp e1.
Proof.
pose proof ftvar_in_fexp_subst_fexp_in_fexp_fresh_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve ftvar_in_fexp_subst_fexp_in_fexp_fresh : lngen.
#[export] Hint Rewrite ftvar_in_fexp_subst_fexp_in_fexp_fresh using solve [auto] : lngen.

(* begin hide *)

Lemma fvar_in_fexp_subst_fexp_in_fexp_fresh_mutual :
(forall e1 e2 x1,
  x1 `notin` fvar_in_fexp e1 ->
  fvar_in_fexp (subst_fexp_in_fexp e2 x1 e1) [=] fvar_in_fexp e1).
Proof.
apply_mutual_ind fexp_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

Lemma fvar_in_fexp_subst_fexp_in_fexp_fresh :
forall e1 e2 x1,
  x1 `notin` fvar_in_fexp e1 ->
  fvar_in_fexp (subst_fexp_in_fexp e2 x1 e1) [=] fvar_in_fexp e1.
Proof.
pose proof fvar_in_fexp_subst_fexp_in_fexp_fresh_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve fvar_in_fexp_subst_fexp_in_fexp_fresh : lngen.
#[export] Hint Rewrite fvar_in_fexp_subst_fexp_in_fexp_fresh using solve [auto] : lngen.

(* begin hide *)

Lemma ftvar_in_ftyp_subst_ftyp_in_ftyp_lower_mutual :
(forall A1 A2 X1,
  remove X1 (ftvar_in_ftyp A1) [<=] ftvar_in_ftyp (subst_ftyp_in_ftyp A2 X1 A1)).
Proof.
apply_mutual_ind ftyp_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

Lemma ftvar_in_ftyp_subst_ftyp_in_ftyp_lower :
forall A1 A2 X1,
  remove X1 (ftvar_in_ftyp A1) [<=] ftvar_in_ftyp (subst_ftyp_in_ftyp A2 X1 A1).
Proof.
pose proof ftvar_in_ftyp_subst_ftyp_in_ftyp_lower_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve ftvar_in_ftyp_subst_ftyp_in_ftyp_lower : lngen.

(* begin hide *)

Lemma ftvar_in_fexp_subst_ftyp_in_fexp_lower_mutual :
(forall e1 A1 X1,
  remove X1 (ftvar_in_fexp e1) [<=] ftvar_in_fexp (subst_ftyp_in_fexp A1 X1 e1)).
Proof.
apply_mutual_ind fexp_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

Lemma ftvar_in_fexp_subst_ftyp_in_fexp_lower :
forall e1 A1 X1,
  remove X1 (ftvar_in_fexp e1) [<=] ftvar_in_fexp (subst_ftyp_in_fexp A1 X1 e1).
Proof.
pose proof ftvar_in_fexp_subst_ftyp_in_fexp_lower_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve ftvar_in_fexp_subst_ftyp_in_fexp_lower : lngen.

(* begin hide *)

Lemma ftvar_in_fexp_subst_fexp_in_fexp_lower_mutual :
(forall e1 e2 x1,
  ftvar_in_fexp e1 [<=] ftvar_in_fexp (subst_fexp_in_fexp e2 x1 e1)).
Proof.
apply_mutual_ind fexp_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

Lemma ftvar_in_fexp_subst_fexp_in_fexp_lower :
forall e1 e2 x1,
  ftvar_in_fexp e1 [<=] ftvar_in_fexp (subst_fexp_in_fexp e2 x1 e1).
Proof.
pose proof ftvar_in_fexp_subst_fexp_in_fexp_lower_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve ftvar_in_fexp_subst_fexp_in_fexp_lower : lngen.

(* begin hide *)

Lemma fvar_in_fexp_subst_ftyp_in_fexp_lower_mutual :
(forall e1 A1 X1,
  fvar_in_fexp e1 [<=] fvar_in_fexp (subst_ftyp_in_fexp A1 X1 e1)).
Proof.
apply_mutual_ind fexp_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

Lemma fvar_in_fexp_subst_ftyp_in_fexp_lower :
forall e1 A1 X1,
  fvar_in_fexp e1 [<=] fvar_in_fexp (subst_ftyp_in_fexp A1 X1 e1).
Proof.
pose proof fvar_in_fexp_subst_ftyp_in_fexp_lower_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve fvar_in_fexp_subst_ftyp_in_fexp_lower : lngen.

(* begin hide *)

Lemma fvar_in_fexp_subst_fexp_in_fexp_lower_mutual :
(forall e1 e2 x1,
  remove x1 (fvar_in_fexp e1) [<=] fvar_in_fexp (subst_fexp_in_fexp e2 x1 e1)).
Proof.
apply_mutual_ind fexp_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

Lemma fvar_in_fexp_subst_fexp_in_fexp_lower :
forall e1 e2 x1,
  remove x1 (fvar_in_fexp e1) [<=] fvar_in_fexp (subst_fexp_in_fexp e2 x1 e1).
Proof.
pose proof fvar_in_fexp_subst_fexp_in_fexp_lower_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve fvar_in_fexp_subst_fexp_in_fexp_lower : lngen.

(* begin hide *)

Lemma ftvar_in_ftyp_subst_ftyp_in_ftyp_notin_mutual :
(forall A1 A2 X1 X2,
  X2 `notin` ftvar_in_ftyp A1 ->
  X2 `notin` ftvar_in_ftyp A2 ->
  X2 `notin` ftvar_in_ftyp (subst_ftyp_in_ftyp A2 X1 A1)).
Proof.
apply_mutual_ind ftyp_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

Lemma ftvar_in_ftyp_subst_ftyp_in_ftyp_notin :
forall A1 A2 X1 X2,
  X2 `notin` ftvar_in_ftyp A1 ->
  X2 `notin` ftvar_in_ftyp A2 ->
  X2 `notin` ftvar_in_ftyp (subst_ftyp_in_ftyp A2 X1 A1).
Proof.
pose proof ftvar_in_ftyp_subst_ftyp_in_ftyp_notin_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve ftvar_in_ftyp_subst_ftyp_in_ftyp_notin : lngen.

(* begin hide *)

Lemma ftvar_in_fexp_subst_ftyp_in_fexp_notin_mutual :
(forall e1 A1 X1 X2,
  X2 `notin` ftvar_in_fexp e1 ->
  X2 `notin` ftvar_in_ftyp A1 ->
  X2 `notin` ftvar_in_fexp (subst_ftyp_in_fexp A1 X1 e1)).
Proof.
apply_mutual_ind fexp_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

Lemma ftvar_in_fexp_subst_ftyp_in_fexp_notin :
forall e1 A1 X1 X2,
  X2 `notin` ftvar_in_fexp e1 ->
  X2 `notin` ftvar_in_ftyp A1 ->
  X2 `notin` ftvar_in_fexp (subst_ftyp_in_fexp A1 X1 e1).
Proof.
pose proof ftvar_in_fexp_subst_ftyp_in_fexp_notin_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve ftvar_in_fexp_subst_ftyp_in_fexp_notin : lngen.

(* begin hide *)

Lemma ftvar_in_fexp_subst_fexp_in_fexp_notin_mutual :
(forall e1 e2 x1 X1,
  X1 `notin` ftvar_in_fexp e1 ->
  X1 `notin` ftvar_in_fexp e2 ->
  X1 `notin` ftvar_in_fexp (subst_fexp_in_fexp e2 x1 e1)).
Proof.
apply_mutual_ind fexp_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

Lemma ftvar_in_fexp_subst_fexp_in_fexp_notin :
forall e1 e2 x1 X1,
  X1 `notin` ftvar_in_fexp e1 ->
  X1 `notin` ftvar_in_fexp e2 ->
  X1 `notin` ftvar_in_fexp (subst_fexp_in_fexp e2 x1 e1).
Proof.
pose proof ftvar_in_fexp_subst_fexp_in_fexp_notin_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve ftvar_in_fexp_subst_fexp_in_fexp_notin : lngen.

(* begin hide *)

Lemma fvar_in_fexp_subst_ftyp_in_fexp_notin_mutual :
(forall e1 A1 X1 x1,
  x1 `notin` fvar_in_fexp e1 ->
  x1 `notin` fvar_in_fexp (subst_ftyp_in_fexp A1 X1 e1)).
Proof.
apply_mutual_ind fexp_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

Lemma fvar_in_fexp_subst_ftyp_in_fexp_notin :
forall e1 A1 X1 x1,
  x1 `notin` fvar_in_fexp e1 ->
  x1 `notin` fvar_in_fexp (subst_ftyp_in_fexp A1 X1 e1).
Proof.
pose proof fvar_in_fexp_subst_ftyp_in_fexp_notin_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve fvar_in_fexp_subst_ftyp_in_fexp_notin : lngen.

(* begin hide *)

Lemma fvar_in_fexp_subst_fexp_in_fexp_notin_mutual :
(forall e1 e2 x1 x2,
  x2 `notin` fvar_in_fexp e1 ->
  x2 `notin` fvar_in_fexp e2 ->
  x2 `notin` fvar_in_fexp (subst_fexp_in_fexp e2 x1 e1)).
Proof.
apply_mutual_ind fexp_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

Lemma fvar_in_fexp_subst_fexp_in_fexp_notin :
forall e1 e2 x1 x2,
  x2 `notin` fvar_in_fexp e1 ->
  x2 `notin` fvar_in_fexp e2 ->
  x2 `notin` fvar_in_fexp (subst_fexp_in_fexp e2 x1 e1).
Proof.
pose proof fvar_in_fexp_subst_fexp_in_fexp_notin_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve fvar_in_fexp_subst_fexp_in_fexp_notin : lngen.

(* begin hide *)

Lemma ftvar_in_ftyp_subst_ftyp_in_ftyp_upper_mutual :
(forall A1 A2 X1,
  ftvar_in_ftyp (subst_ftyp_in_ftyp A2 X1 A1) [<=] ftvar_in_ftyp A2 `union` remove X1 (ftvar_in_ftyp A1)).
Proof.
apply_mutual_ind ftyp_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

Lemma ftvar_in_ftyp_subst_ftyp_in_ftyp_upper :
forall A1 A2 X1,
  ftvar_in_ftyp (subst_ftyp_in_ftyp A2 X1 A1) [<=] ftvar_in_ftyp A2 `union` remove X1 (ftvar_in_ftyp A1).
Proof.
pose proof ftvar_in_ftyp_subst_ftyp_in_ftyp_upper_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve ftvar_in_ftyp_subst_ftyp_in_ftyp_upper : lngen.

(* begin hide *)

Lemma ftvar_in_fexp_subst_ftyp_in_fexp_upper_mutual :
(forall e1 A1 X1,
  ftvar_in_fexp (subst_ftyp_in_fexp A1 X1 e1) [<=] ftvar_in_ftyp A1 `union` remove X1 (ftvar_in_fexp e1)).
Proof.
apply_mutual_ind fexp_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

Lemma ftvar_in_fexp_subst_ftyp_in_fexp_upper :
forall e1 A1 X1,
  ftvar_in_fexp (subst_ftyp_in_fexp A1 X1 e1) [<=] ftvar_in_ftyp A1 `union` remove X1 (ftvar_in_fexp e1).
Proof.
pose proof ftvar_in_fexp_subst_ftyp_in_fexp_upper_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve ftvar_in_fexp_subst_ftyp_in_fexp_upper : lngen.

(* begin hide *)

Lemma ftvar_in_fexp_subst_fexp_in_fexp_upper_mutual :
(forall e1 e2 x1,
  ftvar_in_fexp (subst_fexp_in_fexp e2 x1 e1) [<=] ftvar_in_fexp e2 `union` ftvar_in_fexp e1).
Proof.
apply_mutual_ind fexp_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

Lemma ftvar_in_fexp_subst_fexp_in_fexp_upper :
forall e1 e2 x1,
  ftvar_in_fexp (subst_fexp_in_fexp e2 x1 e1) [<=] ftvar_in_fexp e2 `union` ftvar_in_fexp e1.
Proof.
pose proof ftvar_in_fexp_subst_fexp_in_fexp_upper_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve ftvar_in_fexp_subst_fexp_in_fexp_upper : lngen.

(* begin hide *)

Lemma fvar_in_fexp_subst_ftyp_in_fexp_upper_mutual :
(forall e1 A1 X1,
  fvar_in_fexp (subst_ftyp_in_fexp A1 X1 e1) [<=] fvar_in_fexp e1).
Proof.
apply_mutual_ind fexp_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

Lemma fvar_in_fexp_subst_ftyp_in_fexp_upper :
forall e1 A1 X1,
  fvar_in_fexp (subst_ftyp_in_fexp A1 X1 e1) [<=] fvar_in_fexp e1.
Proof.
pose proof fvar_in_fexp_subst_ftyp_in_fexp_upper_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve fvar_in_fexp_subst_ftyp_in_fexp_upper : lngen.

(* begin hide *)

Lemma fvar_in_fexp_subst_fexp_in_fexp_upper_mutual :
(forall e1 e2 x1,
  fvar_in_fexp (subst_fexp_in_fexp e2 x1 e1) [<=] fvar_in_fexp e2 `union` remove x1 (fvar_in_fexp e1)).
Proof.
apply_mutual_ind fexp_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

Lemma fvar_in_fexp_subst_fexp_in_fexp_upper :
forall e1 e2 x1,
  fvar_in_fexp (subst_fexp_in_fexp e2 x1 e1) [<=] fvar_in_fexp e2 `union` remove x1 (fvar_in_fexp e1).
Proof.
pose proof fvar_in_fexp_subst_fexp_in_fexp_upper_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve fvar_in_fexp_subst_fexp_in_fexp_upper : lngen.


(* *********************************************************************** *)
(** * Theorems about [subst] *)

Ltac default_auto ::= auto with lngen brute_force; tauto.
Ltac default_autorewrite ::= autorewrite with lngen.

(* begin hide *)

Lemma subst_ftyp_in_ftyp_close_ftyp_wrt_ftyp_rec_mutual :
(forall A2 A1 X1 X2 n1,
  degree_ftyp_wrt_ftyp n1 A1 ->
  X1 <> X2 ->
  X2 `notin` ftvar_in_ftyp A1 ->
  subst_ftyp_in_ftyp A1 X1 (close_ftyp_wrt_ftyp_rec n1 X2 A2) = close_ftyp_wrt_ftyp_rec n1 X2 (subst_ftyp_in_ftyp A1 X1 A2)).
Proof.
apply_mutual_ind ftyp_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_ftyp_in_ftyp_close_ftyp_wrt_ftyp_rec :
forall A2 A1 X1 X2 n1,
  degree_ftyp_wrt_ftyp n1 A1 ->
  X1 <> X2 ->
  X2 `notin` ftvar_in_ftyp A1 ->
  subst_ftyp_in_ftyp A1 X1 (close_ftyp_wrt_ftyp_rec n1 X2 A2) = close_ftyp_wrt_ftyp_rec n1 X2 (subst_ftyp_in_ftyp A1 X1 A2).
Proof.
pose proof subst_ftyp_in_ftyp_close_ftyp_wrt_ftyp_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_ftyp_in_ftyp_close_ftyp_wrt_ftyp_rec : lngen.

(* begin hide *)

Lemma subst_ftyp_in_fexp_close_fexp_wrt_ftyp_rec_mutual :
(forall e1 A1 X1 X2 n1,
  degree_ftyp_wrt_ftyp n1 A1 ->
  X1 <> X2 ->
  X2 `notin` ftvar_in_ftyp A1 ->
  subst_ftyp_in_fexp A1 X1 (close_fexp_wrt_ftyp_rec n1 X2 e1) = close_fexp_wrt_ftyp_rec n1 X2 (subst_ftyp_in_fexp A1 X1 e1)).
Proof.
apply_mutual_ind fexp_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_ftyp_in_fexp_close_fexp_wrt_ftyp_rec :
forall e1 A1 X1 X2 n1,
  degree_ftyp_wrt_ftyp n1 A1 ->
  X1 <> X2 ->
  X2 `notin` ftvar_in_ftyp A1 ->
  subst_ftyp_in_fexp A1 X1 (close_fexp_wrt_ftyp_rec n1 X2 e1) = close_fexp_wrt_ftyp_rec n1 X2 (subst_ftyp_in_fexp A1 X1 e1).
Proof.
pose proof subst_ftyp_in_fexp_close_fexp_wrt_ftyp_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_ftyp_in_fexp_close_fexp_wrt_ftyp_rec : lngen.

(* begin hide *)

Lemma subst_ftyp_in_fexp_close_fexp_wrt_fexp_rec_mutual :
(forall e1 A1 x1 X1 n1,
  subst_ftyp_in_fexp A1 x1 (close_fexp_wrt_fexp_rec n1 X1 e1) = close_fexp_wrt_fexp_rec n1 X1 (subst_ftyp_in_fexp A1 x1 e1)).
Proof.
apply_mutual_ind fexp_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_ftyp_in_fexp_close_fexp_wrt_fexp_rec :
forall e1 A1 x1 X1 n1,
  subst_ftyp_in_fexp A1 x1 (close_fexp_wrt_fexp_rec n1 X1 e1) = close_fexp_wrt_fexp_rec n1 X1 (subst_ftyp_in_fexp A1 x1 e1).
Proof.
pose proof subst_ftyp_in_fexp_close_fexp_wrt_fexp_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_ftyp_in_fexp_close_fexp_wrt_fexp_rec : lngen.

(* begin hide *)

Lemma subst_fexp_in_fexp_close_fexp_wrt_ftyp_rec_mutual :
(forall e2 e1 X1 x1 n1,
  degree_fexp_wrt_ftyp n1 e1 ->
  x1 `notin` ftvar_in_fexp e1 ->
  subst_fexp_in_fexp e1 X1 (close_fexp_wrt_ftyp_rec n1 x1 e2) = close_fexp_wrt_ftyp_rec n1 x1 (subst_fexp_in_fexp e1 X1 e2)).
Proof.
apply_mutual_ind fexp_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_fexp_in_fexp_close_fexp_wrt_ftyp_rec :
forall e2 e1 X1 x1 n1,
  degree_fexp_wrt_ftyp n1 e1 ->
  x1 `notin` ftvar_in_fexp e1 ->
  subst_fexp_in_fexp e1 X1 (close_fexp_wrt_ftyp_rec n1 x1 e2) = close_fexp_wrt_ftyp_rec n1 x1 (subst_fexp_in_fexp e1 X1 e2).
Proof.
pose proof subst_fexp_in_fexp_close_fexp_wrt_ftyp_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_fexp_in_fexp_close_fexp_wrt_ftyp_rec : lngen.

(* begin hide *)

Lemma subst_fexp_in_fexp_close_fexp_wrt_fexp_rec_mutual :
(forall e2 e1 x1 x2 n1,
  degree_fexp_wrt_fexp n1 e1 ->
  x1 <> x2 ->
  x2 `notin` fvar_in_fexp e1 ->
  subst_fexp_in_fexp e1 x1 (close_fexp_wrt_fexp_rec n1 x2 e2) = close_fexp_wrt_fexp_rec n1 x2 (subst_fexp_in_fexp e1 x1 e2)).
Proof.
apply_mutual_ind fexp_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_fexp_in_fexp_close_fexp_wrt_fexp_rec :
forall e2 e1 x1 x2 n1,
  degree_fexp_wrt_fexp n1 e1 ->
  x1 <> x2 ->
  x2 `notin` fvar_in_fexp e1 ->
  subst_fexp_in_fexp e1 x1 (close_fexp_wrt_fexp_rec n1 x2 e2) = close_fexp_wrt_fexp_rec n1 x2 (subst_fexp_in_fexp e1 x1 e2).
Proof.
pose proof subst_fexp_in_fexp_close_fexp_wrt_fexp_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_fexp_in_fexp_close_fexp_wrt_fexp_rec : lngen.

Lemma subst_ftyp_in_ftyp_close_ftyp_wrt_ftyp :
forall A2 A1 X1 X2,
  lc_ftyp A1 ->  X1 <> X2 ->
  X2 `notin` ftvar_in_ftyp A1 ->
  subst_ftyp_in_ftyp A1 X1 (close_ftyp_wrt_ftyp X2 A2) = close_ftyp_wrt_ftyp X2 (subst_ftyp_in_ftyp A1 X1 A2).
Proof.
unfold close_ftyp_wrt_ftyp; default_simp.
Qed.

#[export] Hint Resolve subst_ftyp_in_ftyp_close_ftyp_wrt_ftyp : lngen.

Lemma subst_ftyp_in_fexp_close_fexp_wrt_ftyp :
forall e1 A1 X1 X2,
  lc_ftyp A1 ->  X1 <> X2 ->
  X2 `notin` ftvar_in_ftyp A1 ->
  subst_ftyp_in_fexp A1 X1 (close_fexp_wrt_ftyp X2 e1) = close_fexp_wrt_ftyp X2 (subst_ftyp_in_fexp A1 X1 e1).
Proof.
unfold close_fexp_wrt_ftyp; default_simp.
Qed.

#[export] Hint Resolve subst_ftyp_in_fexp_close_fexp_wrt_ftyp : lngen.

Lemma subst_ftyp_in_fexp_close_fexp_wrt_fexp :
forall e1 A1 x1 X1,
  lc_ftyp A1 ->  subst_ftyp_in_fexp A1 x1 (close_fexp_wrt_fexp X1 e1) = close_fexp_wrt_fexp X1 (subst_ftyp_in_fexp A1 x1 e1).
Proof.
unfold close_fexp_wrt_fexp; default_simp.
Qed.

#[export] Hint Resolve subst_ftyp_in_fexp_close_fexp_wrt_fexp : lngen.

Lemma subst_fexp_in_fexp_close_fexp_wrt_ftyp :
forall e2 e1 X1 x1,
  lc_fexp e1 ->  x1 `notin` ftvar_in_fexp e1 ->
  subst_fexp_in_fexp e1 X1 (close_fexp_wrt_ftyp x1 e2) = close_fexp_wrt_ftyp x1 (subst_fexp_in_fexp e1 X1 e2).
Proof.
unfold close_fexp_wrt_ftyp; default_simp.
Qed.

#[export] Hint Resolve subst_fexp_in_fexp_close_fexp_wrt_ftyp : lngen.

Lemma subst_fexp_in_fexp_close_fexp_wrt_fexp :
forall e2 e1 x1 x2,
  lc_fexp e1 ->  x1 <> x2 ->
  x2 `notin` fvar_in_fexp e1 ->
  subst_fexp_in_fexp e1 x1 (close_fexp_wrt_fexp x2 e2) = close_fexp_wrt_fexp x2 (subst_fexp_in_fexp e1 x1 e2).
Proof.
unfold close_fexp_wrt_fexp; default_simp.
Qed.

#[export] Hint Resolve subst_fexp_in_fexp_close_fexp_wrt_fexp : lngen.

(* begin hide *)

Lemma subst_ftyp_in_ftyp_degree_ftyp_wrt_ftyp_mutual :
(forall A1 A2 X1 n1,
  degree_ftyp_wrt_ftyp n1 A1 ->
  degree_ftyp_wrt_ftyp n1 A2 ->
  degree_ftyp_wrt_ftyp n1 (subst_ftyp_in_ftyp A2 X1 A1)).
Proof.
apply_mutual_ind ftyp_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_ftyp_in_ftyp_degree_ftyp_wrt_ftyp :
forall A1 A2 X1 n1,
  degree_ftyp_wrt_ftyp n1 A1 ->
  degree_ftyp_wrt_ftyp n1 A2 ->
  degree_ftyp_wrt_ftyp n1 (subst_ftyp_in_ftyp A2 X1 A1).
Proof.
pose proof subst_ftyp_in_ftyp_degree_ftyp_wrt_ftyp_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_ftyp_in_ftyp_degree_ftyp_wrt_ftyp : lngen.

(* begin hide *)

Lemma subst_ftyp_in_fexp_degree_fexp_wrt_ftyp_mutual :
(forall e1 A1 X1 n1,
  degree_fexp_wrt_ftyp n1 e1 ->
  degree_ftyp_wrt_ftyp n1 A1 ->
  degree_fexp_wrt_ftyp n1 (subst_ftyp_in_fexp A1 X1 e1)).
Proof.
apply_mutual_ind fexp_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_ftyp_in_fexp_degree_fexp_wrt_ftyp :
forall e1 A1 X1 n1,
  degree_fexp_wrt_ftyp n1 e1 ->
  degree_ftyp_wrt_ftyp n1 A1 ->
  degree_fexp_wrt_ftyp n1 (subst_ftyp_in_fexp A1 X1 e1).
Proof.
pose proof subst_ftyp_in_fexp_degree_fexp_wrt_ftyp_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_ftyp_in_fexp_degree_fexp_wrt_ftyp : lngen.

(* begin hide *)

Lemma subst_ftyp_in_fexp_degree_fexp_wrt_fexp_mutual :
(forall e1 A1 X1 n1,
  degree_fexp_wrt_fexp n1 e1 ->
  degree_fexp_wrt_fexp n1 (subst_ftyp_in_fexp A1 X1 e1)).
Proof.
apply_mutual_ind fexp_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_ftyp_in_fexp_degree_fexp_wrt_fexp :
forall e1 A1 X1 n1,
  degree_fexp_wrt_fexp n1 e1 ->
  degree_fexp_wrt_fexp n1 (subst_ftyp_in_fexp A1 X1 e1).
Proof.
pose proof subst_ftyp_in_fexp_degree_fexp_wrt_fexp_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_ftyp_in_fexp_degree_fexp_wrt_fexp : lngen.

(* begin hide *)

Lemma subst_fexp_in_fexp_degree_fexp_wrt_ftyp_mutual :
(forall e1 e2 x1 n1,
  degree_fexp_wrt_ftyp n1 e1 ->
  degree_fexp_wrt_ftyp n1 e2 ->
  degree_fexp_wrt_ftyp n1 (subst_fexp_in_fexp e2 x1 e1)).
Proof.
apply_mutual_ind fexp_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_fexp_in_fexp_degree_fexp_wrt_ftyp :
forall e1 e2 x1 n1,
  degree_fexp_wrt_ftyp n1 e1 ->
  degree_fexp_wrt_ftyp n1 e2 ->
  degree_fexp_wrt_ftyp n1 (subst_fexp_in_fexp e2 x1 e1).
Proof.
pose proof subst_fexp_in_fexp_degree_fexp_wrt_ftyp_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_fexp_in_fexp_degree_fexp_wrt_ftyp : lngen.

(* begin hide *)

Lemma subst_fexp_in_fexp_degree_fexp_wrt_fexp_mutual :
(forall e1 e2 x1 n1,
  degree_fexp_wrt_fexp n1 e1 ->
  degree_fexp_wrt_fexp n1 e2 ->
  degree_fexp_wrt_fexp n1 (subst_fexp_in_fexp e2 x1 e1)).
Proof.
apply_mutual_ind fexp_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_fexp_in_fexp_degree_fexp_wrt_fexp :
forall e1 e2 x1 n1,
  degree_fexp_wrt_fexp n1 e1 ->
  degree_fexp_wrt_fexp n1 e2 ->
  degree_fexp_wrt_fexp n1 (subst_fexp_in_fexp e2 x1 e1).
Proof.
pose proof subst_fexp_in_fexp_degree_fexp_wrt_fexp_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_fexp_in_fexp_degree_fexp_wrt_fexp : lngen.

(* begin hide *)

Lemma subst_ftyp_in_ftyp_fresh_eq_mutual :
(forall A2 A1 X1,
  X1 `notin` ftvar_in_ftyp A2 ->
  subst_ftyp_in_ftyp A1 X1 A2 = A2).
Proof.
apply_mutual_ind ftyp_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_ftyp_in_ftyp_fresh_eq :
forall A2 A1 X1,
  X1 `notin` ftvar_in_ftyp A2 ->
  subst_ftyp_in_ftyp A1 X1 A2 = A2.
Proof.
pose proof subst_ftyp_in_ftyp_fresh_eq_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_ftyp_in_ftyp_fresh_eq : lngen.
#[export] Hint Rewrite subst_ftyp_in_ftyp_fresh_eq using solve [auto] : lngen.

(* begin hide *)

Lemma subst_ftyp_in_fexp_fresh_eq_mutual :
(forall e1 A1 X1,
  X1 `notin` ftvar_in_fexp e1 ->
  subst_ftyp_in_fexp A1 X1 e1 = e1).
Proof.
apply_mutual_ind fexp_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_ftyp_in_fexp_fresh_eq :
forall e1 A1 X1,
  X1 `notin` ftvar_in_fexp e1 ->
  subst_ftyp_in_fexp A1 X1 e1 = e1.
Proof.
pose proof subst_ftyp_in_fexp_fresh_eq_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_ftyp_in_fexp_fresh_eq : lngen.
#[export] Hint Rewrite subst_ftyp_in_fexp_fresh_eq using solve [auto] : lngen.

(* begin hide *)

Lemma subst_fexp_in_fexp_fresh_eq_mutual :
(forall e2 e1 x1,
  x1 `notin` fvar_in_fexp e2 ->
  subst_fexp_in_fexp e1 x1 e2 = e2).
Proof.
apply_mutual_ind fexp_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_fexp_in_fexp_fresh_eq :
forall e2 e1 x1,
  x1 `notin` fvar_in_fexp e2 ->
  subst_fexp_in_fexp e1 x1 e2 = e2.
Proof.
pose proof subst_fexp_in_fexp_fresh_eq_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_fexp_in_fexp_fresh_eq : lngen.
#[export] Hint Rewrite subst_fexp_in_fexp_fresh_eq using solve [auto] : lngen.

(* begin hide *)

Lemma subst_ftyp_in_ftyp_fresh_same_mutual :
(forall A2 A1 X1,
  X1 `notin` ftvar_in_ftyp A1 ->
  X1 `notin` ftvar_in_ftyp (subst_ftyp_in_ftyp A1 X1 A2)).
Proof.
apply_mutual_ind ftyp_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_ftyp_in_ftyp_fresh_same :
forall A2 A1 X1,
  X1 `notin` ftvar_in_ftyp A1 ->
  X1 `notin` ftvar_in_ftyp (subst_ftyp_in_ftyp A1 X1 A2).
Proof.
pose proof subst_ftyp_in_ftyp_fresh_same_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_ftyp_in_ftyp_fresh_same : lngen.

(* begin hide *)

Lemma subst_ftyp_in_fexp_fresh_same_mutual :
(forall e1 A1 X1,
  X1 `notin` ftvar_in_ftyp A1 ->
  X1 `notin` ftvar_in_fexp (subst_ftyp_in_fexp A1 X1 e1)).
Proof.
apply_mutual_ind fexp_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_ftyp_in_fexp_fresh_same :
forall e1 A1 X1,
  X1 `notin` ftvar_in_ftyp A1 ->
  X1 `notin` ftvar_in_fexp (subst_ftyp_in_fexp A1 X1 e1).
Proof.
pose proof subst_ftyp_in_fexp_fresh_same_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_ftyp_in_fexp_fresh_same : lngen.

(* begin hide *)

Lemma subst_fexp_in_fexp_fresh_same_mutual :
(forall e2 e1 x1,
  x1 `notin` fvar_in_fexp e1 ->
  x1 `notin` fvar_in_fexp (subst_fexp_in_fexp e1 x1 e2)).
Proof.
apply_mutual_ind fexp_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_fexp_in_fexp_fresh_same :
forall e2 e1 x1,
  x1 `notin` fvar_in_fexp e1 ->
  x1 `notin` fvar_in_fexp (subst_fexp_in_fexp e1 x1 e2).
Proof.
pose proof subst_fexp_in_fexp_fresh_same_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_fexp_in_fexp_fresh_same : lngen.

(* begin hide *)

Lemma subst_ftyp_in_ftyp_fresh_mutual :
(forall A2 A1 X1 X2,
  X1 `notin` ftvar_in_ftyp A2 ->
  X1 `notin` ftvar_in_ftyp A1 ->
  X1 `notin` ftvar_in_ftyp (subst_ftyp_in_ftyp A1 X2 A2)).
Proof.
apply_mutual_ind ftyp_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_ftyp_in_ftyp_fresh :
forall A2 A1 X1 X2,
  X1 `notin` ftvar_in_ftyp A2 ->
  X1 `notin` ftvar_in_ftyp A1 ->
  X1 `notin` ftvar_in_ftyp (subst_ftyp_in_ftyp A1 X2 A2).
Proof.
pose proof subst_ftyp_in_ftyp_fresh_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_ftyp_in_ftyp_fresh : lngen.

(* begin hide *)

Lemma subst_ftyp_in_fexp_fresh_mutual :
(forall e1 A1 X1 X2,
  X1 `notin` ftvar_in_fexp e1 ->
  X1 `notin` ftvar_in_ftyp A1 ->
  X1 `notin` ftvar_in_fexp (subst_ftyp_in_fexp A1 X2 e1)).
Proof.
apply_mutual_ind fexp_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_ftyp_in_fexp_fresh :
forall e1 A1 X1 X2,
  X1 `notin` ftvar_in_fexp e1 ->
  X1 `notin` ftvar_in_ftyp A1 ->
  X1 `notin` ftvar_in_fexp (subst_ftyp_in_fexp A1 X2 e1).
Proof.
pose proof subst_ftyp_in_fexp_fresh_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_ftyp_in_fexp_fresh : lngen.

(* begin hide *)

Lemma subst_fexp_in_fexp_fresh_mutual :
(forall e2 e1 x1 x2,
  x1 `notin` fvar_in_fexp e2 ->
  x1 `notin` fvar_in_fexp e1 ->
  x1 `notin` fvar_in_fexp (subst_fexp_in_fexp e1 x2 e2)).
Proof.
apply_mutual_ind fexp_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_fexp_in_fexp_fresh :
forall e2 e1 x1 x2,
  x1 `notin` fvar_in_fexp e2 ->
  x1 `notin` fvar_in_fexp e1 ->
  x1 `notin` fvar_in_fexp (subst_fexp_in_fexp e1 x2 e2).
Proof.
pose proof subst_fexp_in_fexp_fresh_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_fexp_in_fexp_fresh : lngen.

Lemma subst_ftyp_in_ftyp_lc_ftyp :
forall A1 A2 X1,
  lc_ftyp A1 ->
  lc_ftyp A2 ->
  lc_ftyp (subst_ftyp_in_ftyp A2 X1 A1).
Proof.
default_simp.
Qed.

#[export] Hint Resolve subst_ftyp_in_ftyp_lc_ftyp : lngen.

Lemma subst_ftyp_in_fexp_lc_fexp :
forall e1 A1 X1,
  lc_fexp e1 ->
  lc_ftyp A1 ->
  lc_fexp (subst_ftyp_in_fexp A1 X1 e1).
Proof.
default_simp.
Qed.

#[export] Hint Resolve subst_ftyp_in_fexp_lc_fexp : lngen.

Lemma subst_fexp_in_fexp_lc_fexp :
forall e1 e2 x1,
  lc_fexp e1 ->
  lc_fexp e2 ->
  lc_fexp (subst_fexp_in_fexp e2 x1 e1).
Proof.
default_simp.
Qed.

#[export] Hint Resolve subst_fexp_in_fexp_lc_fexp : lngen.

(* begin hide *)

Lemma subst_ftyp_in_ftyp_open_ftyp_wrt_ftyp_rec_mutual :
(forall A3 A1 A2 X1 n1,
  lc_ftyp A1 ->
  subst_ftyp_in_ftyp A1 X1 (open_ftyp_wrt_ftyp_rec n1 A2 A3) = open_ftyp_wrt_ftyp_rec n1 (subst_ftyp_in_ftyp A1 X1 A2) (subst_ftyp_in_ftyp A1 X1 A3)).
Proof.
apply_mutual_ind ftyp_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma subst_ftyp_in_ftyp_open_ftyp_wrt_ftyp_rec :
forall A3 A1 A2 X1 n1,
  lc_ftyp A1 ->
  subst_ftyp_in_ftyp A1 X1 (open_ftyp_wrt_ftyp_rec n1 A2 A3) = open_ftyp_wrt_ftyp_rec n1 (subst_ftyp_in_ftyp A1 X1 A2) (subst_ftyp_in_ftyp A1 X1 A3).
Proof.
pose proof subst_ftyp_in_ftyp_open_ftyp_wrt_ftyp_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_ftyp_in_ftyp_open_ftyp_wrt_ftyp_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma subst_ftyp_in_fexp_open_fexp_wrt_ftyp_rec_mutual :
(forall e1 A1 A2 X1 n1,
  lc_ftyp A1 ->
  subst_ftyp_in_fexp A1 X1 (open_fexp_wrt_ftyp_rec n1 A2 e1) = open_fexp_wrt_ftyp_rec n1 (subst_ftyp_in_ftyp A1 X1 A2) (subst_ftyp_in_fexp A1 X1 e1)).
Proof.
apply_mutual_ind fexp_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma subst_ftyp_in_fexp_open_fexp_wrt_ftyp_rec :
forall e1 A1 A2 X1 n1,
  lc_ftyp A1 ->
  subst_ftyp_in_fexp A1 X1 (open_fexp_wrt_ftyp_rec n1 A2 e1) = open_fexp_wrt_ftyp_rec n1 (subst_ftyp_in_ftyp A1 X1 A2) (subst_ftyp_in_fexp A1 X1 e1).
Proof.
pose proof subst_ftyp_in_fexp_open_fexp_wrt_ftyp_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_ftyp_in_fexp_open_fexp_wrt_ftyp_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma subst_ftyp_in_fexp_open_fexp_wrt_fexp_rec_mutual :
(forall e2 A1 e1 X1 n1,
  subst_ftyp_in_fexp A1 X1 (open_fexp_wrt_fexp_rec n1 e1 e2) = open_fexp_wrt_fexp_rec n1 (subst_ftyp_in_fexp A1 X1 e1) (subst_ftyp_in_fexp A1 X1 e2)).
Proof.
apply_mutual_ind fexp_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma subst_ftyp_in_fexp_open_fexp_wrt_fexp_rec :
forall e2 A1 e1 X1 n1,
  subst_ftyp_in_fexp A1 X1 (open_fexp_wrt_fexp_rec n1 e1 e2) = open_fexp_wrt_fexp_rec n1 (subst_ftyp_in_fexp A1 X1 e1) (subst_ftyp_in_fexp A1 X1 e2).
Proof.
pose proof subst_ftyp_in_fexp_open_fexp_wrt_fexp_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_ftyp_in_fexp_open_fexp_wrt_fexp_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma subst_fexp_in_fexp_open_fexp_wrt_ftyp_rec_mutual :
(forall e2 e1 A1 x1 n1,
  lc_fexp e1 ->
  subst_fexp_in_fexp e1 x1 (open_fexp_wrt_ftyp_rec n1 A1 e2) = open_fexp_wrt_ftyp_rec n1 A1 (subst_fexp_in_fexp e1 x1 e2)).
Proof.
apply_mutual_ind fexp_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma subst_fexp_in_fexp_open_fexp_wrt_ftyp_rec :
forall e2 e1 A1 x1 n1,
  lc_fexp e1 ->
  subst_fexp_in_fexp e1 x1 (open_fexp_wrt_ftyp_rec n1 A1 e2) = open_fexp_wrt_ftyp_rec n1 A1 (subst_fexp_in_fexp e1 x1 e2).
Proof.
pose proof subst_fexp_in_fexp_open_fexp_wrt_ftyp_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_fexp_in_fexp_open_fexp_wrt_ftyp_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma subst_fexp_in_fexp_open_fexp_wrt_fexp_rec_mutual :
(forall e3 e1 e2 x1 n1,
  lc_fexp e1 ->
  subst_fexp_in_fexp e1 x1 (open_fexp_wrt_fexp_rec n1 e2 e3) = open_fexp_wrt_fexp_rec n1 (subst_fexp_in_fexp e1 x1 e2) (subst_fexp_in_fexp e1 x1 e3)).
Proof.
apply_mutual_ind fexp_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma subst_fexp_in_fexp_open_fexp_wrt_fexp_rec :
forall e3 e1 e2 x1 n1,
  lc_fexp e1 ->
  subst_fexp_in_fexp e1 x1 (open_fexp_wrt_fexp_rec n1 e2 e3) = open_fexp_wrt_fexp_rec n1 (subst_fexp_in_fexp e1 x1 e2) (subst_fexp_in_fexp e1 x1 e3).
Proof.
pose proof subst_fexp_in_fexp_open_fexp_wrt_fexp_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_fexp_in_fexp_open_fexp_wrt_fexp_rec : lngen.

(* end hide *)

Lemma subst_ftyp_in_ftyp_open_ftyp_wrt_ftyp :
forall A3 A1 A2 X1,
  lc_ftyp A1 ->
  subst_ftyp_in_ftyp A1 X1 (open_ftyp_wrt_ftyp A3 A2) = open_ftyp_wrt_ftyp (subst_ftyp_in_ftyp A1 X1 A3) (subst_ftyp_in_ftyp A1 X1 A2).
Proof.
unfold open_ftyp_wrt_ftyp; default_simp.
Qed.

#[export] Hint Resolve subst_ftyp_in_ftyp_open_ftyp_wrt_ftyp : lngen.

Lemma subst_ftyp_in_fexp_open_fexp_wrt_ftyp :
forall e1 A1 A2 X1,
  lc_ftyp A1 ->
  subst_ftyp_in_fexp A1 X1 (open_fexp_wrt_ftyp e1 A2) = open_fexp_wrt_ftyp (subst_ftyp_in_fexp A1 X1 e1) (subst_ftyp_in_ftyp A1 X1 A2).
Proof.
unfold open_fexp_wrt_ftyp; default_simp.
Qed.

#[export] Hint Resolve subst_ftyp_in_fexp_open_fexp_wrt_ftyp : lngen.

Lemma subst_ftyp_in_fexp_open_fexp_wrt_fexp :
forall e2 A1 e1 X1,
  subst_ftyp_in_fexp A1 X1 (open_fexp_wrt_fexp e2 e1) = open_fexp_wrt_fexp (subst_ftyp_in_fexp A1 X1 e2) (subst_ftyp_in_fexp A1 X1 e1).
Proof.
unfold open_fexp_wrt_fexp; default_simp.
Qed.

#[export] Hint Resolve subst_ftyp_in_fexp_open_fexp_wrt_fexp : lngen.

Lemma subst_fexp_in_fexp_open_fexp_wrt_ftyp :
forall e2 e1 A1 x1,
  lc_fexp e1 ->
  subst_fexp_in_fexp e1 x1 (open_fexp_wrt_ftyp e2 A1) = open_fexp_wrt_ftyp (subst_fexp_in_fexp e1 x1 e2) A1.
Proof.
unfold open_fexp_wrt_ftyp; default_simp.
Qed.

#[export] Hint Resolve subst_fexp_in_fexp_open_fexp_wrt_ftyp : lngen.

Lemma subst_fexp_in_fexp_open_fexp_wrt_fexp :
forall e3 e1 e2 x1,
  lc_fexp e1 ->
  subst_fexp_in_fexp e1 x1 (open_fexp_wrt_fexp e3 e2) = open_fexp_wrt_fexp (subst_fexp_in_fexp e1 x1 e3) (subst_fexp_in_fexp e1 x1 e2).
Proof.
unfold open_fexp_wrt_fexp; default_simp.
Qed.

#[export] Hint Resolve subst_fexp_in_fexp_open_fexp_wrt_fexp : lngen.

Lemma subst_ftyp_in_ftyp_open_ftyp_wrt_ftyp_var :
forall A2 A1 X1 X2,
  X1 <> X2 ->
  lc_ftyp A1 ->
  open_ftyp_wrt_ftyp (subst_ftyp_in_ftyp A1 X1 A2) (ftyp_var_f X2) = subst_ftyp_in_ftyp A1 X1 (open_ftyp_wrt_ftyp A2 (ftyp_var_f X2)).
Proof.
intros; rewrite subst_ftyp_in_ftyp_open_ftyp_wrt_ftyp; default_simp.
Qed.

#[export] Hint Resolve subst_ftyp_in_ftyp_open_ftyp_wrt_ftyp_var : lngen.

Lemma subst_ftyp_in_fexp_open_fexp_wrt_ftyp_var :
forall e1 A1 X1 X2,
  X1 <> X2 ->
  lc_ftyp A1 ->
  open_fexp_wrt_ftyp (subst_ftyp_in_fexp A1 X1 e1) (ftyp_var_f X2) = subst_ftyp_in_fexp A1 X1 (open_fexp_wrt_ftyp e1 (ftyp_var_f X2)).
Proof.
intros; rewrite subst_ftyp_in_fexp_open_fexp_wrt_ftyp; default_simp.
Qed.

#[export] Hint Resolve subst_ftyp_in_fexp_open_fexp_wrt_ftyp_var : lngen.

Lemma subst_ftyp_in_fexp_open_fexp_wrt_fexp_var :
forall e1 A1 X1 x1,
  open_fexp_wrt_fexp (subst_ftyp_in_fexp A1 X1 e1) (fexp_var_f x1) = subst_ftyp_in_fexp A1 X1 (open_fexp_wrt_fexp e1 (fexp_var_f x1)).
Proof.
intros; rewrite subst_ftyp_in_fexp_open_fexp_wrt_fexp; default_simp.
Qed.

#[export] Hint Resolve subst_ftyp_in_fexp_open_fexp_wrt_fexp_var : lngen.

Lemma subst_fexp_in_fexp_open_fexp_wrt_ftyp_var :
forall e2 e1 x1 X1,
  lc_fexp e1 ->
  open_fexp_wrt_ftyp (subst_fexp_in_fexp e1 x1 e2) (ftyp_var_f X1) = subst_fexp_in_fexp e1 x1 (open_fexp_wrt_ftyp e2 (ftyp_var_f X1)).
Proof.
intros; rewrite subst_fexp_in_fexp_open_fexp_wrt_ftyp; default_simp.
Qed.

#[export] Hint Resolve subst_fexp_in_fexp_open_fexp_wrt_ftyp_var : lngen.

Lemma subst_fexp_in_fexp_open_fexp_wrt_fexp_var :
forall e2 e1 x1 x2,
  x1 <> x2 ->
  lc_fexp e1 ->
  open_fexp_wrt_fexp (subst_fexp_in_fexp e1 x1 e2) (fexp_var_f x2) = subst_fexp_in_fexp e1 x1 (open_fexp_wrt_fexp e2 (fexp_var_f x2)).
Proof.
intros; rewrite subst_fexp_in_fexp_open_fexp_wrt_fexp; default_simp.
Qed.

#[export] Hint Resolve subst_fexp_in_fexp_open_fexp_wrt_fexp_var : lngen.

(* begin hide *)

Lemma subst_ftyp_in_ftyp_spec_rec_mutual :
(forall A1 A2 X1 n1,
  subst_ftyp_in_ftyp A2 X1 A1 = open_ftyp_wrt_ftyp_rec n1 A2 (close_ftyp_wrt_ftyp_rec n1 X1 A1)).
Proof.
apply_mutual_ind ftyp_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma subst_ftyp_in_ftyp_spec_rec :
forall A1 A2 X1 n1,
  subst_ftyp_in_ftyp A2 X1 A1 = open_ftyp_wrt_ftyp_rec n1 A2 (close_ftyp_wrt_ftyp_rec n1 X1 A1).
Proof.
pose proof subst_ftyp_in_ftyp_spec_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_ftyp_in_ftyp_spec_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma subst_ftyp_in_fexp_spec_rec_mutual :
(forall e1 A1 X1 n1,
  subst_ftyp_in_fexp A1 X1 e1 = open_fexp_wrt_ftyp_rec n1 A1 (close_fexp_wrt_ftyp_rec n1 X1 e1)).
Proof.
apply_mutual_ind fexp_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma subst_ftyp_in_fexp_spec_rec :
forall e1 A1 X1 n1,
  subst_ftyp_in_fexp A1 X1 e1 = open_fexp_wrt_ftyp_rec n1 A1 (close_fexp_wrt_ftyp_rec n1 X1 e1).
Proof.
pose proof subst_ftyp_in_fexp_spec_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_ftyp_in_fexp_spec_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma subst_fexp_in_fexp_spec_rec_mutual :
(forall e1 e2 x1 n1,
  subst_fexp_in_fexp e2 x1 e1 = open_fexp_wrt_fexp_rec n1 e2 (close_fexp_wrt_fexp_rec n1 x1 e1)).
Proof.
apply_mutual_ind fexp_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma subst_fexp_in_fexp_spec_rec :
forall e1 e2 x1 n1,
  subst_fexp_in_fexp e2 x1 e1 = open_fexp_wrt_fexp_rec n1 e2 (close_fexp_wrt_fexp_rec n1 x1 e1).
Proof.
pose proof subst_fexp_in_fexp_spec_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_fexp_in_fexp_spec_rec : lngen.

(* end hide *)

Lemma subst_ftyp_in_ftyp_spec :
forall A1 A2 X1,
  subst_ftyp_in_ftyp A2 X1 A1 = open_ftyp_wrt_ftyp (close_ftyp_wrt_ftyp X1 A1) A2.
Proof.
unfold close_ftyp_wrt_ftyp; unfold open_ftyp_wrt_ftyp; default_simp.
Qed.

#[export] Hint Resolve subst_ftyp_in_ftyp_spec : lngen.

Lemma subst_ftyp_in_fexp_spec :
forall e1 A1 X1,
  subst_ftyp_in_fexp A1 X1 e1 = open_fexp_wrt_ftyp (close_fexp_wrt_ftyp X1 e1) A1.
Proof.
unfold close_fexp_wrt_ftyp; unfold open_fexp_wrt_ftyp; default_simp.
Qed.

#[export] Hint Resolve subst_ftyp_in_fexp_spec : lngen.

Lemma subst_fexp_in_fexp_spec :
forall e1 e2 x1,
  subst_fexp_in_fexp e2 x1 e1 = open_fexp_wrt_fexp (close_fexp_wrt_fexp x1 e1) e2.
Proof.
unfold close_fexp_wrt_fexp; unfold open_fexp_wrt_fexp; default_simp.
Qed.

#[export] Hint Resolve subst_fexp_in_fexp_spec : lngen.

(* begin hide *)

Lemma subst_ftyp_in_ftyp_subst_ftyp_in_ftyp_mutual :
(forall A1 A2 A3 X2 X1,
  X2 `notin` ftvar_in_ftyp A2 ->
  X2 <> X1 ->
  subst_ftyp_in_ftyp A2 X1 (subst_ftyp_in_ftyp A3 X2 A1) = subst_ftyp_in_ftyp (subst_ftyp_in_ftyp A2 X1 A3) X2 (subst_ftyp_in_ftyp A2 X1 A1)).
Proof.
apply_mutual_ind ftyp_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_ftyp_in_ftyp_subst_ftyp_in_ftyp :
forall A1 A2 A3 X2 X1,
  X2 `notin` ftvar_in_ftyp A2 ->
  X2 <> X1 ->
  subst_ftyp_in_ftyp A2 X1 (subst_ftyp_in_ftyp A3 X2 A1) = subst_ftyp_in_ftyp (subst_ftyp_in_ftyp A2 X1 A3) X2 (subst_ftyp_in_ftyp A2 X1 A1).
Proof.
pose proof subst_ftyp_in_ftyp_subst_ftyp_in_ftyp_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_ftyp_in_ftyp_subst_ftyp_in_ftyp : lngen.

(* begin hide *)

Lemma subst_ftyp_in_fexp_subst_ftyp_in_fexp_mutual :
(forall e1 A1 A2 X2 X1,
  X2 `notin` ftvar_in_ftyp A1 ->
  X2 <> X1 ->
  subst_ftyp_in_fexp A1 X1 (subst_ftyp_in_fexp A2 X2 e1) = subst_ftyp_in_fexp (subst_ftyp_in_ftyp A1 X1 A2) X2 (subst_ftyp_in_fexp A1 X1 e1)).
Proof.
apply_mutual_ind fexp_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_ftyp_in_fexp_subst_ftyp_in_fexp :
forall e1 A1 A2 X2 X1,
  X2 `notin` ftvar_in_ftyp A1 ->
  X2 <> X1 ->
  subst_ftyp_in_fexp A1 X1 (subst_ftyp_in_fexp A2 X2 e1) = subst_ftyp_in_fexp (subst_ftyp_in_ftyp A1 X1 A2) X2 (subst_ftyp_in_fexp A1 X1 e1).
Proof.
pose proof subst_ftyp_in_fexp_subst_ftyp_in_fexp_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_ftyp_in_fexp_subst_ftyp_in_fexp : lngen.

(* begin hide *)

Lemma subst_ftyp_in_fexp_subst_fexp_in_fexp_mutual :
(forall e1 A1 e2 x1 X1,
  subst_ftyp_in_fexp A1 X1 (subst_fexp_in_fexp e2 x1 e1) = subst_fexp_in_fexp (subst_ftyp_in_fexp A1 X1 e2) x1 (subst_ftyp_in_fexp A1 X1 e1)).
Proof.
apply_mutual_ind fexp_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_ftyp_in_fexp_subst_fexp_in_fexp :
forall e1 A1 e2 x1 X1,
  subst_ftyp_in_fexp A1 X1 (subst_fexp_in_fexp e2 x1 e1) = subst_fexp_in_fexp (subst_ftyp_in_fexp A1 X1 e2) x1 (subst_ftyp_in_fexp A1 X1 e1).
Proof.
pose proof subst_ftyp_in_fexp_subst_fexp_in_fexp_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_ftyp_in_fexp_subst_fexp_in_fexp : lngen.

(* begin hide *)

Lemma subst_fexp_in_fexp_subst_ftyp_in_fexp_mutual :
(forall e1 e2 A1 X1 x1,
  X1 `notin` ftvar_in_fexp e2 ->
  subst_fexp_in_fexp e2 x1 (subst_ftyp_in_fexp A1 X1 e1) = subst_ftyp_in_fexp A1 X1 (subst_fexp_in_fexp e2 x1 e1)).
Proof.
apply_mutual_ind fexp_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_fexp_in_fexp_subst_ftyp_in_fexp :
forall e1 e2 A1 X1 x1,
  X1 `notin` ftvar_in_fexp e2 ->
  subst_fexp_in_fexp e2 x1 (subst_ftyp_in_fexp A1 X1 e1) = subst_ftyp_in_fexp A1 X1 (subst_fexp_in_fexp e2 x1 e1).
Proof.
pose proof subst_fexp_in_fexp_subst_ftyp_in_fexp_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_fexp_in_fexp_subst_ftyp_in_fexp : lngen.

(* begin hide *)

Lemma subst_fexp_in_fexp_subst_fexp_in_fexp_mutual :
(forall e1 e2 e3 x2 x1,
  x2 `notin` fvar_in_fexp e2 ->
  x2 <> x1 ->
  subst_fexp_in_fexp e2 x1 (subst_fexp_in_fexp e3 x2 e1) = subst_fexp_in_fexp (subst_fexp_in_fexp e2 x1 e3) x2 (subst_fexp_in_fexp e2 x1 e1)).
Proof.
apply_mutual_ind fexp_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_fexp_in_fexp_subst_fexp_in_fexp :
forall e1 e2 e3 x2 x1,
  x2 `notin` fvar_in_fexp e2 ->
  x2 <> x1 ->
  subst_fexp_in_fexp e2 x1 (subst_fexp_in_fexp e3 x2 e1) = subst_fexp_in_fexp (subst_fexp_in_fexp e2 x1 e3) x2 (subst_fexp_in_fexp e2 x1 e1).
Proof.
pose proof subst_fexp_in_fexp_subst_fexp_in_fexp_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_fexp_in_fexp_subst_fexp_in_fexp : lngen.

(* begin hide *)

Lemma subst_ftyp_in_ftyp_close_ftyp_wrt_ftyp_rec_open_ftyp_wrt_ftyp_rec_mutual :
(forall A2 A1 X1 X2 n1,
  X2 `notin` ftvar_in_ftyp A2 ->
  X2 `notin` ftvar_in_ftyp A1 ->
  X2 <> X1 ->
  degree_ftyp_wrt_ftyp n1 A1 ->
  subst_ftyp_in_ftyp A1 X1 A2 = close_ftyp_wrt_ftyp_rec n1 X2 (subst_ftyp_in_ftyp A1 X1 (open_ftyp_wrt_ftyp_rec n1 (ftyp_var_f X2) A2))).
Proof.
apply_mutual_ind ftyp_mutrec;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma subst_ftyp_in_ftyp_close_ftyp_wrt_ftyp_rec_open_ftyp_wrt_ftyp_rec :
forall A2 A1 X1 X2 n1,
  X2 `notin` ftvar_in_ftyp A2 ->
  X2 `notin` ftvar_in_ftyp A1 ->
  X2 <> X1 ->
  degree_ftyp_wrt_ftyp n1 A1 ->
  subst_ftyp_in_ftyp A1 X1 A2 = close_ftyp_wrt_ftyp_rec n1 X2 (subst_ftyp_in_ftyp A1 X1 (open_ftyp_wrt_ftyp_rec n1 (ftyp_var_f X2) A2)).
Proof.
pose proof subst_ftyp_in_ftyp_close_ftyp_wrt_ftyp_rec_open_ftyp_wrt_ftyp_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_ftyp_in_ftyp_close_ftyp_wrt_ftyp_rec_open_ftyp_wrt_ftyp_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma subst_ftyp_in_fexp_close_fexp_wrt_ftyp_rec_open_fexp_wrt_ftyp_rec_mutual :
(forall e1 A1 X1 X2 n1,
  X2 `notin` ftvar_in_fexp e1 ->
  X2 `notin` ftvar_in_ftyp A1 ->
  X2 <> X1 ->
  degree_ftyp_wrt_ftyp n1 A1 ->
  subst_ftyp_in_fexp A1 X1 e1 = close_fexp_wrt_ftyp_rec n1 X2 (subst_ftyp_in_fexp A1 X1 (open_fexp_wrt_ftyp_rec n1 (ftyp_var_f X2) e1))).
Proof.
apply_mutual_ind fexp_mutrec;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma subst_ftyp_in_fexp_close_fexp_wrt_ftyp_rec_open_fexp_wrt_ftyp_rec :
forall e1 A1 X1 X2 n1,
  X2 `notin` ftvar_in_fexp e1 ->
  X2 `notin` ftvar_in_ftyp A1 ->
  X2 <> X1 ->
  degree_ftyp_wrt_ftyp n1 A1 ->
  subst_ftyp_in_fexp A1 X1 e1 = close_fexp_wrt_ftyp_rec n1 X2 (subst_ftyp_in_fexp A1 X1 (open_fexp_wrt_ftyp_rec n1 (ftyp_var_f X2) e1)).
Proof.
pose proof subst_ftyp_in_fexp_close_fexp_wrt_ftyp_rec_open_fexp_wrt_ftyp_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_ftyp_in_fexp_close_fexp_wrt_ftyp_rec_open_fexp_wrt_ftyp_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma subst_ftyp_in_fexp_close_fexp_wrt_fexp_rec_open_fexp_wrt_fexp_rec_mutual :
(forall e1 A1 X1 x1 n1,
  x1 `notin` fvar_in_fexp e1 ->
  subst_ftyp_in_fexp A1 X1 e1 = close_fexp_wrt_fexp_rec n1 x1 (subst_ftyp_in_fexp A1 X1 (open_fexp_wrt_fexp_rec n1 (fexp_var_f x1) e1))).
Proof.
apply_mutual_ind fexp_mutrec;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma subst_ftyp_in_fexp_close_fexp_wrt_fexp_rec_open_fexp_wrt_fexp_rec :
forall e1 A1 X1 x1 n1,
  x1 `notin` fvar_in_fexp e1 ->
  subst_ftyp_in_fexp A1 X1 e1 = close_fexp_wrt_fexp_rec n1 x1 (subst_ftyp_in_fexp A1 X1 (open_fexp_wrt_fexp_rec n1 (fexp_var_f x1) e1)).
Proof.
pose proof subst_ftyp_in_fexp_close_fexp_wrt_fexp_rec_open_fexp_wrt_fexp_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_ftyp_in_fexp_close_fexp_wrt_fexp_rec_open_fexp_wrt_fexp_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma subst_fexp_in_fexp_close_fexp_wrt_ftyp_rec_open_fexp_wrt_ftyp_rec_mutual :
(forall e2 e1 x1 X1 n1,
  X1 `notin` ftvar_in_fexp e2 ->
  X1 `notin` ftvar_in_fexp e1 ->
  degree_fexp_wrt_ftyp n1 e1 ->
  subst_fexp_in_fexp e1 x1 e2 = close_fexp_wrt_ftyp_rec n1 X1 (subst_fexp_in_fexp e1 x1 (open_fexp_wrt_ftyp_rec n1 (ftyp_var_f X1) e2))).
Proof.
apply_mutual_ind fexp_mutrec;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma subst_fexp_in_fexp_close_fexp_wrt_ftyp_rec_open_fexp_wrt_ftyp_rec :
forall e2 e1 x1 X1 n1,
  X1 `notin` ftvar_in_fexp e2 ->
  X1 `notin` ftvar_in_fexp e1 ->
  degree_fexp_wrt_ftyp n1 e1 ->
  subst_fexp_in_fexp e1 x1 e2 = close_fexp_wrt_ftyp_rec n1 X1 (subst_fexp_in_fexp e1 x1 (open_fexp_wrt_ftyp_rec n1 (ftyp_var_f X1) e2)).
Proof.
pose proof subst_fexp_in_fexp_close_fexp_wrt_ftyp_rec_open_fexp_wrt_ftyp_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_fexp_in_fexp_close_fexp_wrt_ftyp_rec_open_fexp_wrt_ftyp_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma subst_fexp_in_fexp_close_fexp_wrt_fexp_rec_open_fexp_wrt_fexp_rec_mutual :
(forall e2 e1 x1 x2 n1,
  x2 `notin` fvar_in_fexp e2 ->
  x2 `notin` fvar_in_fexp e1 ->
  x2 <> x1 ->
  degree_fexp_wrt_fexp n1 e1 ->
  subst_fexp_in_fexp e1 x1 e2 = close_fexp_wrt_fexp_rec n1 x2 (subst_fexp_in_fexp e1 x1 (open_fexp_wrt_fexp_rec n1 (fexp_var_f x2) e2))).
Proof.
apply_mutual_ind fexp_mutrec;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma subst_fexp_in_fexp_close_fexp_wrt_fexp_rec_open_fexp_wrt_fexp_rec :
forall e2 e1 x1 x2 n1,
  x2 `notin` fvar_in_fexp e2 ->
  x2 `notin` fvar_in_fexp e1 ->
  x2 <> x1 ->
  degree_fexp_wrt_fexp n1 e1 ->
  subst_fexp_in_fexp e1 x1 e2 = close_fexp_wrt_fexp_rec n1 x2 (subst_fexp_in_fexp e1 x1 (open_fexp_wrt_fexp_rec n1 (fexp_var_f x2) e2)).
Proof.
pose proof subst_fexp_in_fexp_close_fexp_wrt_fexp_rec_open_fexp_wrt_fexp_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_fexp_in_fexp_close_fexp_wrt_fexp_rec_open_fexp_wrt_fexp_rec : lngen.

(* end hide *)

Lemma subst_ftyp_in_ftyp_close_ftyp_wrt_ftyp_open_ftyp_wrt_ftyp :
forall A2 A1 X1 X2,
  X2 `notin` ftvar_in_ftyp A2 ->
  X2 `notin` ftvar_in_ftyp A1 ->
  X2 <> X1 ->
  lc_ftyp A1 ->
  subst_ftyp_in_ftyp A1 X1 A2 = close_ftyp_wrt_ftyp X2 (subst_ftyp_in_ftyp A1 X1 (open_ftyp_wrt_ftyp A2 (ftyp_var_f X2))).
Proof.
unfold close_ftyp_wrt_ftyp; unfold open_ftyp_wrt_ftyp; default_simp.
Qed.

#[export] Hint Resolve subst_ftyp_in_ftyp_close_ftyp_wrt_ftyp_open_ftyp_wrt_ftyp : lngen.

Lemma subst_ftyp_in_fexp_close_fexp_wrt_ftyp_open_fexp_wrt_ftyp :
forall e1 A1 X1 X2,
  X2 `notin` ftvar_in_fexp e1 ->
  X2 `notin` ftvar_in_ftyp A1 ->
  X2 <> X1 ->
  lc_ftyp A1 ->
  subst_ftyp_in_fexp A1 X1 e1 = close_fexp_wrt_ftyp X2 (subst_ftyp_in_fexp A1 X1 (open_fexp_wrt_ftyp e1 (ftyp_var_f X2))).
Proof.
unfold close_fexp_wrt_ftyp; unfold open_fexp_wrt_ftyp; default_simp.
Qed.

#[export] Hint Resolve subst_ftyp_in_fexp_close_fexp_wrt_ftyp_open_fexp_wrt_ftyp : lngen.

Lemma subst_ftyp_in_fexp_close_fexp_wrt_fexp_open_fexp_wrt_fexp :
forall e1 A1 X1 x1,
  x1 `notin` fvar_in_fexp e1 ->
  lc_ftyp A1 ->
  subst_ftyp_in_fexp A1 X1 e1 = close_fexp_wrt_fexp x1 (subst_ftyp_in_fexp A1 X1 (open_fexp_wrt_fexp e1 (fexp_var_f x1))).
Proof.
unfold close_fexp_wrt_fexp; unfold open_fexp_wrt_fexp; default_simp.
Qed.

#[export] Hint Resolve subst_ftyp_in_fexp_close_fexp_wrt_fexp_open_fexp_wrt_fexp : lngen.

Lemma subst_fexp_in_fexp_close_fexp_wrt_ftyp_open_fexp_wrt_ftyp :
forall e2 e1 x1 X1,
  X1 `notin` ftvar_in_fexp e2 ->
  X1 `notin` ftvar_in_fexp e1 ->
  lc_fexp e1 ->
  subst_fexp_in_fexp e1 x1 e2 = close_fexp_wrt_ftyp X1 (subst_fexp_in_fexp e1 x1 (open_fexp_wrt_ftyp e2 (ftyp_var_f X1))).
Proof.
unfold close_fexp_wrt_ftyp; unfold open_fexp_wrt_ftyp; default_simp.
Qed.

#[export] Hint Resolve subst_fexp_in_fexp_close_fexp_wrt_ftyp_open_fexp_wrt_ftyp : lngen.

Lemma subst_fexp_in_fexp_close_fexp_wrt_fexp_open_fexp_wrt_fexp :
forall e2 e1 x1 x2,
  x2 `notin` fvar_in_fexp e2 ->
  x2 `notin` fvar_in_fexp e1 ->
  x2 <> x1 ->
  lc_fexp e1 ->
  subst_fexp_in_fexp e1 x1 e2 = close_fexp_wrt_fexp x2 (subst_fexp_in_fexp e1 x1 (open_fexp_wrt_fexp e2 (fexp_var_f x2))).
Proof.
unfold close_fexp_wrt_fexp; unfold open_fexp_wrt_fexp; default_simp.
Qed.

#[export] Hint Resolve subst_fexp_in_fexp_close_fexp_wrt_fexp_open_fexp_wrt_fexp : lngen.

Lemma subst_ftyp_in_ftyp_ftyp_all :
forall X2 A2 A1 X1,
  lc_ftyp A1 ->
  X2 `notin` ftvar_in_ftyp A1 `union` ftvar_in_ftyp A2 `union` singleton X1 ->
  subst_ftyp_in_ftyp A1 X1 (ftyp_all A2) = ftyp_all (close_ftyp_wrt_ftyp X2 (subst_ftyp_in_ftyp A1 X1 (open_ftyp_wrt_ftyp A2 (ftyp_var_f X2)))).
Proof.
default_simp.
Qed.

#[export] Hint Resolve subst_ftyp_in_ftyp_ftyp_all : lngen.

Lemma subst_ftyp_in_fexp_fexp_abs :
forall x1 A2 e1 A1 X1,
  lc_ftyp A1 ->
  x1 `notin` fvar_in_fexp e1 ->
  subst_ftyp_in_fexp A1 X1 (fexp_abs A2 e1) = fexp_abs (subst_ftyp_in_ftyp A1 X1 A2) (close_fexp_wrt_fexp x1 (subst_ftyp_in_fexp A1 X1 (open_fexp_wrt_fexp e1 (fexp_var_f x1)))).
Proof.
default_simp.
Qed.

#[export] Hint Resolve subst_ftyp_in_fexp_fexp_abs : lngen.

Lemma subst_ftyp_in_fexp_fexp_tabs :
forall X2 e1 A1 X1,
  lc_ftyp A1 ->
  X2 `notin` ftvar_in_ftyp A1 `union` ftvar_in_fexp e1 `union` singleton X1 ->
  subst_ftyp_in_fexp A1 X1 (fexp_tabs e1) = fexp_tabs (close_fexp_wrt_ftyp X2 (subst_ftyp_in_fexp A1 X1 (open_fexp_wrt_ftyp e1 (ftyp_var_f X2)))).
Proof.
default_simp.
Qed.

#[export] Hint Resolve subst_ftyp_in_fexp_fexp_tabs : lngen.

Lemma subst_fexp_in_fexp_fexp_abs :
forall x2 A1 e2 e1 x1,
  lc_fexp e1 ->
  x2 `notin` fvar_in_fexp e1 `union` fvar_in_fexp e2 `union` singleton x1 ->
  subst_fexp_in_fexp e1 x1 (fexp_abs A1 e2) = fexp_abs (A1) (close_fexp_wrt_fexp x2 (subst_fexp_in_fexp e1 x1 (open_fexp_wrt_fexp e2 (fexp_var_f x2)))).
Proof.
default_simp.
Qed.

#[export] Hint Resolve subst_fexp_in_fexp_fexp_abs : lngen.

Lemma subst_fexp_in_fexp_fexp_tabs :
forall X1 e2 e1 x1,
  lc_fexp e1 ->
  X1 `notin` ftvar_in_fexp e1 `union` ftvar_in_fexp e2 ->
  subst_fexp_in_fexp e1 x1 (fexp_tabs e2) = fexp_tabs (close_fexp_wrt_ftyp X1 (subst_fexp_in_fexp e1 x1 (open_fexp_wrt_ftyp e2 (ftyp_var_f X1)))).
Proof.
default_simp.
Qed.

#[export] Hint Resolve subst_fexp_in_fexp_fexp_tabs : lngen.

(* begin hide *)

Lemma subst_ftyp_in_ftyp_intro_rec_mutual :
(forall A1 X1 A2 n1,
  X1 `notin` ftvar_in_ftyp A1 ->
  open_ftyp_wrt_ftyp_rec n1 A2 A1 = subst_ftyp_in_ftyp A2 X1 (open_ftyp_wrt_ftyp_rec n1 (ftyp_var_f X1) A1)).
Proof.
apply_mutual_ind ftyp_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_ftyp_in_ftyp_intro_rec :
forall A1 X1 A2 n1,
  X1 `notin` ftvar_in_ftyp A1 ->
  open_ftyp_wrt_ftyp_rec n1 A2 A1 = subst_ftyp_in_ftyp A2 X1 (open_ftyp_wrt_ftyp_rec n1 (ftyp_var_f X1) A1).
Proof.
pose proof subst_ftyp_in_ftyp_intro_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_ftyp_in_ftyp_intro_rec : lngen.
#[export] Hint Rewrite subst_ftyp_in_ftyp_intro_rec using solve [auto] : lngen.

(* begin hide *)

Lemma subst_ftyp_in_fexp_intro_rec_mutual :
(forall e1 X1 A1 n1,
  X1 `notin` ftvar_in_fexp e1 ->
  open_fexp_wrt_ftyp_rec n1 A1 e1 = subst_ftyp_in_fexp A1 X1 (open_fexp_wrt_ftyp_rec n1 (ftyp_var_f X1) e1)).
Proof.
apply_mutual_ind fexp_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_ftyp_in_fexp_intro_rec :
forall e1 X1 A1 n1,
  X1 `notin` ftvar_in_fexp e1 ->
  open_fexp_wrt_ftyp_rec n1 A1 e1 = subst_ftyp_in_fexp A1 X1 (open_fexp_wrt_ftyp_rec n1 (ftyp_var_f X1) e1).
Proof.
pose proof subst_ftyp_in_fexp_intro_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_ftyp_in_fexp_intro_rec : lngen.
#[export] Hint Rewrite subst_ftyp_in_fexp_intro_rec using solve [auto] : lngen.

(* begin hide *)

Lemma subst_fexp_in_fexp_intro_rec_mutual :
(forall e1 x1 e2 n1,
  x1 `notin` fvar_in_fexp e1 ->
  open_fexp_wrt_fexp_rec n1 e2 e1 = subst_fexp_in_fexp e2 x1 (open_fexp_wrt_fexp_rec n1 (fexp_var_f x1) e1)).
Proof.
apply_mutual_ind fexp_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_fexp_in_fexp_intro_rec :
forall e1 x1 e2 n1,
  x1 `notin` fvar_in_fexp e1 ->
  open_fexp_wrt_fexp_rec n1 e2 e1 = subst_fexp_in_fexp e2 x1 (open_fexp_wrt_fexp_rec n1 (fexp_var_f x1) e1).
Proof.
pose proof subst_fexp_in_fexp_intro_rec_mutual as H; intuition eauto.
Qed.

#[export] Hint Resolve subst_fexp_in_fexp_intro_rec : lngen.
#[export] Hint Rewrite subst_fexp_in_fexp_intro_rec using solve [auto] : lngen.

Lemma subst_ftyp_in_ftyp_intro :
forall X1 A1 A2,
  X1 `notin` ftvar_in_ftyp A1 ->
  open_ftyp_wrt_ftyp A1 A2 = subst_ftyp_in_ftyp A2 X1 (open_ftyp_wrt_ftyp A1 (ftyp_var_f X1)).
Proof.
unfold open_ftyp_wrt_ftyp; default_simp.
Qed.

#[export] Hint Resolve subst_ftyp_in_ftyp_intro : lngen.

Lemma subst_ftyp_in_fexp_intro :
forall X1 e1 A1,
  X1 `notin` ftvar_in_fexp e1 ->
  open_fexp_wrt_ftyp e1 A1 = subst_ftyp_in_fexp A1 X1 (open_fexp_wrt_ftyp e1 (ftyp_var_f X1)).
Proof.
unfold open_fexp_wrt_ftyp; default_simp.
Qed.

#[export] Hint Resolve subst_ftyp_in_fexp_intro : lngen.

Lemma subst_fexp_in_fexp_intro :
forall x1 e1 e2,
  x1 `notin` fvar_in_fexp e1 ->
  open_fexp_wrt_fexp e1 e2 = subst_fexp_in_fexp e2 x1 (open_fexp_wrt_fexp e1 (fexp_var_f x1)).
Proof.
unfold open_fexp_wrt_fexp; default_simp.
Qed.

#[export] Hint Resolve subst_fexp_in_fexp_intro : lngen.


(* *********************************************************************** *)
(** * "Restore" tactics *)

Ltac default_auto ::= auto; tauto.
Ltac default_autorewrite ::= fail.
