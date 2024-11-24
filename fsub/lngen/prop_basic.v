Require Import Coq.Program.Equality.
Require Import Metalib.Metatheory.
From Hammer Require Import Tactics.

Require Import fsub.lngen.def_ott.
Require Import fsub.lngen.prop_ln.
Require Import common.ltac_ln.
Require Import common.prop_ln.
Require Import fsub.lngen.def_extra.

Lemma wf_typ_lc_typ Γ A :
  Γ ⊢ A -> 
  lc_typ A.
Proof.
  intros. induction H; try hauto ctrs:lc_typ.
  - pick fresh X. inst_cofinites_with X.
    eapply lc_typ_all_exists with X; eauto.
Qed.

Lemma subtyping_lc_typ Γ A B :
  Γ ⊢ A <: B -> 
  lc_typ A /\ lc_typ B.
Proof.
  intros. induction H; try hauto ctrs:lc_typ use:wf_typ_lc_typ.
  - split; pick fresh X; inst_cofinites_with X; 
    eapply lc_typ_all_exists with X; hauto.
Qed.