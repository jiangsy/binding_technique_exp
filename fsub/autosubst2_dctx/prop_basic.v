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

Definition ctx_tvar_rename_weak Δ Δ' ξ :=
  forall X B, lookup_tvar X Δ B -> exists B', lookup_tvar (ξ X) Δ' B'.

Definition ctx_tvar_rename Δ Δ' ξ :=
  forall X B, lookup_tvar X Δ B -> lookup_tvar (ξ X) Δ' (B ⟨ ξ ⟩).

Lemma wf_typ_renaming_tvar Δ Δ' A ξ:
  Δ ⊢ A ->
  ctx_tvar_rename_weak Δ Δ' ξ ->
  Δ' ⊢ A ⟨ ξ ⟩.
Proof.
  move: Δ Δ' ξ. induction A; try hauto.
  - intros. unfold ctx_tvar_rename_weak in *.
    asimpl. simpl in *. 
    hauto inv:lookup_tvar ctrs:lookup_tvar.
Qed.

Corollary wf_typ_weakening_tvar0 Δ A B:
  Δ ⊢ A ->
  (B :: Δ) ⊢ A ⟨↑⟩.
Proof.
  hauto unfold:ctx_tvar_rename_weak inv:lookup_tvar ctrs:lookup_tvar
    use:wf_typ_renaming_tvar.
Qed.

Lemma sub_weakening_tvar  Δ Δ' A B ξ :
  Δ ⊢ A <: B ->
  ctx_tvar_rename Δ Δ' ξ ->
  Δ' ⊢ A ⟨ ξ ⟩ <: B ⟨ ξ ⟩.
Proof.
  move => H.
  move: Δ' ξ. elim: Δ A B / H; intros; 
    try hauto unfold:ctx_tvar_rename,ctx_tvar_rename_weak ctrs:subtyping use:wf_typ_renaming_tvar.
  - asimpl. eapply sub_all; try hauto unfold:ctx_tvar_rename,ctx_tvar_rename_weak ctrs:subtyping use:wf_typ_renaming_tvar.
    eapply H0.
    unfold ctx_tvar_rename in *. intros. asimpl. simpl in *.
    inversion H2; subst; asimpl.
    + replace (ren_typ (ξ >> S) B1) with (B1 ⟨ξ⟩ ⟨S⟩) by (asimpl; auto).
      constructor.
    + replace (ren_typ (ξ >> S) A) with (A ⟨ξ⟩ ⟨S⟩) by (asimpl; auto).
      constructor; eauto.
Qed.