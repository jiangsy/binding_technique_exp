Require Import Coq.Program.Equality.
Require Import Lia.
Require Import Metalib.Metatheory.
From Hammer Require Import Tactics.

From Coq Require Import ssreflect ssrfun ssrbool.

Require Import fsub.lngen.def_ott.
Require Import fsub.lngen.prop_ln.
Require Import common.ltac_ln.
Require Import common.prop_ln.
Require Import fsub.lngen.def_extra.
Require Import fsub.lngen.prop_basic.
Require Import fsub.lngen.prop_subtyping.

Theorem preservation Γ t t' A : 
  uniq Γ ->
  Γ ⊢ t : A ->
  t ⤳ t' ->
  Γ ⊢ t' : A.
Proof.
  move => Huniq Hty Hstep. move : Γ A Hty Huniq. 
    induction Hstep; intros; try hauto inv:typing ctrs:typing depth:2.
  - ssimpl. admit.
  - ssimpl.
    pick fresh X. inst_cofinites_with X. admit.
Admitted.

Theorem progress t A :
  nil ⊢ t : A ->
  is_value t \/ exists t', t ⤳ t'.
Proof.
Admitted.