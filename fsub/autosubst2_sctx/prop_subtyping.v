Require Import common.prop_as_core.
Require Import common.prop_as_unscoped.
Require Import fsub.autosubst2_sctx.def_as2.
Require Import fsub.autosubst2_sctx.def_extra.
Require Import fsub.autosubst2_sctx.prop_basic.

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

Lemma lookup_tvar_det : forall Γ X A B,
  lookup_tvar X Γ A -> lookup_tvar X Γ B -> A = B.
Proof.
  intros. move : B H0. 
    induction H; hauto inv:lookup_tvar ctrs:lookup_tvar.
Qed.

Fixpoint num_tvars (Γ : ctx) :=
  match Γ with
  | nil => 0
  | entry_tvar _ :: Γ => 1 + num_tvars Γ
  | _ :: Γ => num_tvars Γ
  end.

Corollary ctx_tvar_renaming_tvars Γ1 Γ2 A: 
  ctx_tvar_rename Γ1 (Γ2 ++ (entry_tvar A) :: Γ1) (fun X : nat => 1 + (num_tvars Γ2 + X)).
Proof.
  intros. unfold ctx_tvar_rename. intros.
    induction Γ2; simpl; try hauto inv:lookup_tvar ctrs:lookup_tvar.
  - destruct a; eauto using lookup_tvar.
    replace (⟨fun X0 : nat => S (S (num_tvars Γ2 + X0))⟩ B) with
    (B ⟨fun X : nat => 1 + (num_tvars Γ2 + X)⟩ ⟨ ↑⟩ ) by (asimpl; eauto).
    eauto using lookup_tvar.
Qed.

Lemma lookup_tvar_rebinding : forall Γ1 Γ2 B,
  lookup_tvar (num_tvars Γ2) (Γ2 ++ (entry_tvar B) :: Γ1) (B ⟨fun X => 1 + (num_tvars Γ2 + X) ⟩) /\
  (forall X A B', X <> num_tvars Γ2 -> 
    lookup_tvar X (Γ2 ++ (entry_tvar B) :: Γ1) A ->
    lookup_tvar X (Γ2 ++ (entry_tvar B') :: Γ1) A).
Proof.
  split. 
  - induction Γ2; simpl; asimpl; try hauto ctrs:lookup_tvar.
    + destruct a; try hauto ctrs:lookup_tvar. 
      replace (ren_typ (Init.Nat.add (S (num_tvars Γ2)) >> S) B) with
      (B ⟨fun X : nat => 1 + (num_tvars Γ2 + X)⟩ ⟨↑⟩ ) by (asimpl; auto).
      hauto ctrs:lookup_tvar. 
  - intros. dependent induction H0.
    + destruct Γ2; simpl in *; try hauto ctrs:lookup_tvar.
    + destruct Γ2; simpl in *; try hauto ctrs:lookup_tvar.
    + destruct Γ2; simpl in *; try hauto ctrs:lookup_tvar.
Qed.

Lemma conj' (A B : Prop) : A -> (A -> B) -> A /\ B.
Proof. tauto. Qed.

Theorem subtyping_reflexivity Γ A :
  Γ ⊢ A ->
  Γ ⊢ A <: A.
Proof.
  move : Γ. induction A; intros; try hauto ctrs:subtyping.
  - apply sub_top; auto.
Qed. 

Theorem subtyping_transitivity_narrowing n:
  (forall Γ A B C,  
    typ_size B = n -> 
    Γ ⊢ A <: B ->
    Γ ⊢ B <: C ->
    Γ ⊢ A <: C) /\
  (forall Γ1 Γ2 A B B' C,
    typ_size B = n -> 
    Γ2 ++ (entry_tvar B :: Γ1) ⊢ A <: C ->
    Γ1 ⊢ B' <: B ->
    Γ2 ++ (entry_tvar B' :: Γ1) ⊢ A <: C).
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
        -- eapply wf_typ_renaming_tvar' with (ξ:=id) (A:=A2) (A':=A2) (Γ:=(entry_tvar B1)::Γ);
          hauto unfold:ctx_tvar_rename_weak inv:lookup_tvar ctrs:lookup_tvar use:sub_wf_typ1, sub_wf_typ2 simp+:asimpl.
      * eapply sub_all; eauto.
        -- edestruct (IH (typ_size B1)). hfcrush. auto. hauto. 
        -- edestruct (IH (typ_size B1)). eauto. hfcrush. eauto. 
           edestruct (IH (typ_size B2)). hfcrush. eauto.
           replace ((entry_tvar B0) :: Γ) with (nil ++ (entry_tvar B0) :: Γ) by auto.
           eapply H2; eauto.
  - intros Htrans. intros. move : B' H1. dependent induction H0; intros; auto.
    + eapply sub_top.
      eapply wf_typ_renaming_tvar' with (ξ:=id); 
        hauto use:ctx_tvar_rename_weak_rebinding simp+:asimpl.
    + eapply sub_tvar_refl; eauto.
      eapply wf_typ_renaming_tvar' with (ξ:=id) (A:=typ_var X); 
        hauto use:ctx_tvar_rename_weak_rebinding simp+:asimpl.
    + edestruct (Nat.eq_dec X (num_tvars Γ2)).
      * subst. 
        eapply sub_tvar_bound with (A:=B' ⟨fun X => 1 + (num_tvars Γ2 + X) ⟩).
        hauto use:lookup_tvar_rebinding. eapply Htrans with (B:=B ⟨fun X => 1 + (num_tvars Γ2 + X) ⟩).
        -- hauto use:typ_size_renaming_eq.
        -- eapply sub_renaming_tvar; eauto.
           eapply ctx_tvar_renaming_tvars.
        -- erewrite (lookup_tvar_det _ _ (⟨fun X : nat => 1 + (num_tvars Γ2 + X)⟩ B)); eauto.
           hauto use:lookup_tvar_rebinding.
      * subst. eapply sub_tvar_bound; eauto.
        eapply lookup_tvar_rebinding; eauto.
    + hauto ctrs:subtyping.
    + eapply sub_all; try hauto ctrs:subtyping.
      * eapply wf_typ_renaming_tvar' with (ξ:=id); 
        hauto use:ctx_tvar_rename_weak_rebinding simp+:asimpl.
      * replace ((entry_tvar B1) :: Γ2 ++ (entry_tvar B') :: Γ1) with ((entry_tvar B1 :: Γ2) ++ (entry_tvar B') :: Γ1) by auto.
        eapply IHsubtyping2; eauto.
Qed.

Corollary subtyping_transitivity Γ A B C:
  Γ ⊢ A <: B -> 
  Γ ⊢ B <: C -> 
  Γ ⊢ A <: C.
Proof.
  eapply subtyping_transitivity_narrowing; eauto.
Qed.

Corollary subtyping_narrowing Γ1 Γ2 A B B' C:
  Γ2 ++ (entry_tvar B) :: Γ1 ⊢ A <: C ->
  Γ1 ⊢ B' <: B ->
  Γ2 ++ (entry_tvar B') :: Γ1 ⊢ A <: C.
Proof.
  eapply subtyping_transitivity_narrowing; eauto.
Qed.

Definition ctx_tvar_subst Γ Γ' σ :=
  forall X A, lookup_tvar X Γ A -> Γ' ⊢ σ X <: A [σ].

Lemma subtyping_subst Γ Γ' A B σ :
  Γ ⊢ A <: B ->
  ctx_tvar_subst Γ Γ' σ ->
  Γ' ⊢ A [ σ ] <: B [ σ ].
Proof.
  move => H. move : Γ' σ. elim: Γ A B / H; intros.
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