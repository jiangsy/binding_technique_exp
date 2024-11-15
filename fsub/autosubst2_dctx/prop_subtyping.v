Require Import common.prop_as_core.
Require Import common.prop_as_unscoped.
Require Import fsub.autosubst2_dctx.def_as2.
Require Import fsub.autosubst2_dctx.def_extra.
Require Import fsub.autosubst2_dctx.prop_basic.

From Coq Require Import ssreflect ssrfun ssrbool.
From Hammer Require Import Tactics.
Require Import Coq.Program.Equality.
Require Import List.
Require Import Arith.

Import SubstNotations.
Import UnscopedNotations.

Fixpoint typ_size (A : typ) :=
  match A with
  | typ_arr A B => 1 + typ_size A + typ_size B
  | typ_all A B => 1 + typ_size A + typ_size B
  | _ => 0
  end.

Lemma typ_size_renaming_eq A ξ:
  typ_size (A ⟨ ξ ⟩) = typ_size A.
Proof.
  move : ξ; induction A; intros; simpl; hauto.
Qed.

Lemma lookup_tvar_det : forall Δ X A B,
  lookup_tvar X Δ A -> lookup_tvar X Δ B -> A = B.
Proof.
  intros. move : B H0. 
    induction H; hauto inv:lookup_tvar ctrs:lookup_tvar.
Qed.

Corollary ctx_tvar_renaming_tvars Δ1 Δ2 A: 
  ctx_tvar_rename Δ1 (Δ2 ++ A :: Δ1) (fun X : nat => 1 + (length Δ2 + X)).
Proof.
  intros. unfold ctx_tvar_rename. intros.
    induction Δ2; simpl; try hauto inv:lookup_tvar ctrs:lookup_tvar.
  - replace (⟨fun X0 : nat => S (S (length Δ2 + X0))⟩ B) with
    (B ⟨fun X : nat => 1 + (length Δ2 + X)⟩ ⟨ ↑⟩ ) by (asimpl; auto).
    hauto ctrs:lookup_tvar.
Qed.

Lemma lookup_tvar_rebounding : forall Δ1 Δ2 B,
  lookup_tvar (length Δ2) (Δ2 ++ B :: Δ1) (B ⟨fun X => 1 + (length Δ2 + X) ⟩) /\
  (forall X A B', X <> length Δ2 -> 
    lookup_tvar X (Δ2 ++ B :: Δ1) A ->
    lookup_tvar X (Δ2 ++ B' :: Δ1) A).
Proof.
  split. 
  - induction Δ2; simpl; asimpl; try hauto ctrs:lookup_tvar.
    + replace (ren_typ (fun X : nat => S (S (length Δ2 + X))) B) with
      (B ⟨fun X : nat => 1 + (length Δ2 + X)⟩ ⟨↑⟩ ) by (asimpl; auto).
      hauto ctrs:lookup_tvar.
  - intros. dependent induction H0.
    + destruct Δ2; simpl in *; try hauto ctrs:lookup_tvar.
    + destruct Δ2; simpl in *; try hauto ctrs:lookup_tvar.
Qed.

Lemma conj' (A B : Prop) : A -> (A -> B) -> A /\ B.
Proof. tauto. Qed.

Theorem subtyping_reflexivity Δ A :
  Δ ⊢ A ->
  Δ ⊢ A <: A.
Proof.
  move : Δ. induction A; intros; try hauto ctrs:subtyping.
  - apply sub_top; auto.
Qed.

Theorem subtyping_transitivity_narrowing n:
  (forall Δ A B C,  
    typ_size B = n -> 
    Δ ⊢ A <: B ->
    Δ ⊢ B <: C ->
    Δ ⊢ A <: C) /\
  (forall Δ1 Δ2 A B B' C,
    typ_size B = n -> 
    Δ2 ++ (B :: Δ1) ⊢ A <: C ->
    Δ1 ⊢ B' <: B ->
    Δ2 ++ (B' :: Δ1) ⊢ A <: C).
Proof.
  induction (lt_wf n) as [n _ IH].
  intros. apply conj'.
  - intros. move : C H1. induction H0; intros; try hauto ctrs:subtyping.
    + inversion H1; subst.
      * hauto ctrs:subtyping. 
    + simpl in *. 
      inversion H1; subst.
      * eapply sub_top. hauto use:sub_wf_typ1, sub_wf_typ2.
      * eapply sub_arrow.
        -- edestruct (IH (typ_size B1)). hfcrush. hauto. 
        -- edestruct (IH (typ_size B2)). hfcrush. hauto. 
    + inversion H1; subst.
      * eapply sub_top. simpl in *. split.
        -- hauto use:sub_wf_typ1, sub_wf_typ2.
        -- eapply wf_typ_renaming_tvar' with (ξ:=id) (A:=A2) (A':=A2) (Δ:=B1::Δ);
          hauto unfold:ctx_tvar_rename_weak inv:lookup_tvar ctrs:lookup_tvar use:sub_wf_typ1, sub_wf_typ2 simp+:asimpl.
      * eapply sub_all; eauto.
        -- edestruct (IH (typ_size B1)). hfcrush. auto. hauto. 
        -- edestruct (IH (typ_size B1)). eauto. hfcrush. eauto. 
           edestruct (IH (typ_size B2)). hfcrush. eauto.
           replace (B0 :: Δ) with (nil ++ B0 :: Δ) by auto.
           eapply H2; eauto.
  - intros Htrans. intros. move : B' H1. dependent induction H0; intros; auto.
    + eapply sub_top.
      eapply wf_typ_renaming_tvar' with (ξ:=id); 
        hauto use:ctx_tvar_rename_weak_rebounding simp+:asimpl.
    + eapply sub_tvar_refl; eauto.
      eapply wf_typ_renaming_tvar' with (ξ:=id) (A:=typ_var X); 
        hauto use:ctx_tvar_rename_weak_rebounding simp+:asimpl.
    + edestruct (Nat.eq_dec X (length Δ2)).
      * subst. 
        eapply sub_tvar_bound with (A:=B' ⟨fun X => 1 + (length Δ2 + X) ⟩).
        hauto use:lookup_tvar_rebounding. eapply Htrans with (B:=B ⟨fun X => 1 + (length Δ2 + X) ⟩).
        -- hauto use:typ_size_renaming_eq.
        -- eapply sub_renaming_tvar; eauto.
           eapply ctx_tvar_renaming_tvars.
        -- erewrite (lookup_tvar_det _ _ (⟨fun X : nat => 1 + (length Δ2 + X)⟩ B)); eauto.
           hauto use:lookup_tvar_rebounding.
      * subst. eapply sub_tvar_bound; eauto.
        eapply lookup_tvar_rebounding; eauto.
    + hauto ctrs:subtyping.
    + eapply sub_all; try hauto ctrs:subtyping.
      * eapply wf_typ_renaming_tvar' with (ξ:=id); 
        hauto use:ctx_tvar_rename_weak_rebounding simp+:asimpl.
      * replace (B1 :: Δ2 ++ B' :: Δ1) with ((B1 :: Δ2) ++ B' :: Δ1) by auto.
        eapply IHsubtyping2; eauto.
Qed.

Corollary subtyping_transitivity Δ A B C:
  Δ ⊢ A <: B -> 
  Δ ⊢ B <: C -> 
  Δ ⊢ A <: C.
Proof.
  eapply subtyping_transitivity_narrowing; eauto.
Qed.

Corollary subtyping_narrowing Δ1 Δ2 A B B' C:
  Δ2 ++ B :: Δ1 ⊢ A <: C ->
  Δ1 ⊢ B' <: B ->
  Δ2 ++ B' :: Δ1 ⊢ A <: C.
Proof.
  eapply subtyping_transitivity_narrowing; eauto.
Qed.

Definition ctx_tvar_subst Δ Δ' σ :=
  forall X A, lookup_tvar X Δ A -> Δ' ⊢ σ X <: A [σ].

Lemma subtyping_subst Δ Δ' A B σ :
  Δ ⊢ A <: B ->
  ctx_tvar_subst Δ Δ' σ ->
  Δ' ⊢ A [ σ ] <: B [ σ ].
Proof.
  move => H. move : Δ' σ. elim: Δ A B / H; intros.
  - asimpl.
    hauto unfold:ctx_tvar_subst_wf,ctx_tvar_subst use:wf_typ_subst_tvar,sub_wf_typ1,sub_wf_typ2 ctrs:subtyping.
  - hauto use:subtyping_reflexivity,sub_wf_typ1 unfold:ctx_tvar_subst ctrs:subtyping.
  - hauto use:subtyping_transitivity unfold:ctx_tvar_subst ctrs:subtyping.
  - apply sub_arrow; hauto.
  - asimpl. apply sub_all; eauto.
    + hauto unfold:ctx_tvar_subst_wf,ctx_tvar_subst use:wf_typ_subst_tvar,sub_wf_typ1,sub_wf_typ2 ctrs:subtyping.
    + apply H0. unfold ctx_tvar_subst in *. intros.
      inversion H2; subst; asimpl.
      eapply sub_tvar_bound with (A:=B1 [σ] ⟨ ↑ ⟩). econstructor.
      replace (subst_typ (σ >> (ren_typ ↑)) B1) with (B1 [σ] ⟨ ↑ ⟩) by (asimpl; auto).
      eapply sub_weakening_tvar0. 
      hauto unfold:ctx_tvar_subst_wf inv:lookup_tvar ctrs:lookup_tvar use:sub_wf_typ1,sub_wf_typ2,subtyping_reflexivity,wf_typ_subst_tvar.
      replace (subst_typ (σ >> (ren_typ ↑)) A0) with (A0 [σ] ⟨ ↑ ⟩) by (asimpl; auto).
      eapply sub_weakening_tvar0. 
      hauto unfold:ctx_tvar_subst_wf inv:lookup_tvar ctrs:lookup_tvar use:sub_wf_typ1,sub_wf_typ2,subtyping_reflexivity,wf_typ_subst_tvar.
Qed.