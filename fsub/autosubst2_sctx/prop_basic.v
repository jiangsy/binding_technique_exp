Require Import common.prop_as_core. 
Require Import common.prop_as_unscoped.
Require Import fsub.autosubst2_sctx.def_as2.
Require Import fsub.autosubst2_sctx.def_extra.

From Coq Require Import ssreflect ssrfun ssrbool.
From Hammer Require Import Tactics.
Require Import Coq.Program.Equality.
Require Import List.

Import SubstNotations.
Import UnscopedNotations.

Definition ctx_tvar_rename_weak Γ Γ' ξ :=
  forall X B, lookup_tvar X Γ B -> exists B', lookup_tvar (ξ X) Γ' B'.

Definition ctx_tvar_rename Γ Γ' ξ :=
  forall X B, lookup_tvar X Γ B -> lookup_tvar (ξ X) Γ' (B ⟨ ξ ⟩).

Definition ctx_tvar_subst_wf Γ Γ' σ :=
  forall X A, lookup_tvar X Γ A -> Γ' ⊢ σ X.

Lemma ctx_tvar_rename_weak_rebounding Γ1 Γ2 A A':
  ctx_tvar_rename_weak (Γ2 ++ (entry_tvar A) :: Γ1)  (Γ2 ++ (entry_tvar A') :: Γ1) id.
Proof.
  intros. induction Γ2; simpl;
    hauto unfold:ctx_tvar_rename_weak inv:lookup_tvar ctrs:lookup_tvar.
Qed.