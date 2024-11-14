Require Import common.prop_as_core.
Require Import common.prop_as_unscoped.
Require Import fsub.autosubst2_dctx.def_as2.
Require Import fsub.autosubst2_dctx.def_extra.

From Coq Require Import ssreflect ssrfun ssrbool.
From Hammer Require Import Tactics.
Require Import Coq.Program.Equality.
Require Import List.

Import SubstNotations.
Import UnscopedNotations.

Theorem subtyping_reflexivity Δ A : 
  Δ ⊢ A ->
  Δ ⊢ A <: A.
Proof.
  move : Δ; elim: A; intros; try hauto ctrs:subtyping.
  apply sub_top; eauto.
Qed.