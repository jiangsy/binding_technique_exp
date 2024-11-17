Require Import List.
Require Import Program.Equality.
From Hammer Require Import Tactics.
From Coq Require Import ssreflect ssrfun ssrbool.

Require Import common.prop_as_core.
Require Import common.prop_as_unscoped.
Require Import fsub.autosubst2_dctx.def_as2.
Require Import fsub.autosubst2_dctx.def_extra.
Require Import fsub.autosubst2_dctx.prop_basic.
Require Import fsub.autosubst2_dctx.prop_subtyping.

Import SubstNotations.
Import UnscopedNotations.

Lemma typing_narrowing Δ1 Δ2 Γ A B C t :
  Δ2 ++ A :: Δ1 ;; Γ ⊢ t : C ->
  Δ1 ⊢ B <: A ->
  Δ2 ++ B :: Δ1 ;; Γ ⊢ t : C.
Proof.
  intro H. dependent induction H; intros; 
    try hauto ctrs:typing.
  - apply typing_abs.
    + eapply wf_typ_narrowing; eauto.
    + eauto.
  - apply typing_tabs; eauto.
    + eapply wf_typ_narrowing; eauto.
    + replace (A0 :: Δ2 ++ B :: Δ1) with ((A0 :: Δ2) ++ B :: Δ1) by auto.
      eapply IHtyping; simpl; eauto. 
  - eapply typing_tapp; eauto using subtyping_narrowing.
  - eapply typing_sub; eauto using subtyping_narrowing.
Qed.

Definition ctx_var_subst Δ Γ Γ' σ τ :=
  forall x A, lookup_var x Γ A -> (Δ ;; Γ' ⊢ τ x : A [σ]).

Lemma typing_subst Δ Δ' Γ Γ' A t σ τ :
  Δ ;; Γ ⊢ t : A ->
  ctx_tvar_subst Δ Δ' σ ->
  ctx_var_subst Δ' Γ Γ' σ τ -> 
  Δ' ;; Γ' ⊢ t [σ;τ] : A [σ] .
Proof.
  move => Hty. move : Δ' Γ' σ τ.
  induction Hty; intros; asimpl; try hauto ctrs:typing.
  - eapply typing_abs; eauto. 
    + hauto unfold:ctx_tvar_subst_wf,ctx_tvar_subst use:wf_typ_subst_tvar,sub_wf_typ1.
    + eapply IHHty; eauto.
      * unfold ctx_var_subst in *. intros.
        inversion H2; subst; asimpl; eauto.
        -- hauto ctrs:lookup_var, typing.
        -- eapply typing_weakening_var0; eauto. 
  - eapply typing_tabs.
    + hauto unfold:ctx_tvar_subst_wf,ctx_tvar_subst use:wf_typ_subst_tvar,sub_wf_typ1.
    + eapply IHHty; eauto.
      * unfold ctx_tvar_subst in *. intros.
        inversion H2; subst; asimpl; eauto.
        eapply sub_tvar_bound; try hauto ctrs:lookup_tvar use:subtyping_reflexivity simp+:asimpl.
        asimpl. apply subtyping_reflexivity. eapply wf_typ_subst_tvar; eauto. 
        -- hauto unfold:ctx_tvar_subst_wf ctrs:lookup_tvar use:wf_typ_weakening_tvar0,sub_wf_typ1,sub_wf_typ2. 
        -- replace ( subst_typ (σ >> ren_typ ↑) A1) with (A1 [σ] ⟨ ↑ ⟩) by (asimpl; auto).
           replace ( (σ >> ren_typ ↑) n) with ((σ n) ⟨ ↑ ⟩) by (asimpl; auto).
           eapply sub_weakening_tvar0; eauto.
      * unfold ctx_var_subst in *. intros.
        apply lookup_var_map_inv in H2. ssimpl. asimpl.
        replace (subst_typ (σ >> ren_typ ↑) A1) with (A1 [σ] ⟨ ↑ ⟩) by (asimpl; auto).
        eapply typing_weakening_tvar0. eapply H1; eauto.
  - asimpl. subst.
    eapply typing_tapp with (A:=A [σ]) (B:=B [up_typ_typ σ]); asimpl; eauto. 
    eapply subtyping_subst; eauto.
  - eapply typing_sub with (A:=A [σ]); eauto.
    eapply subtyping_subst; eauto.
Qed.

Definition wf_ctx Δ :=
  forall X A, lookup_tvar X Δ A -> Δ ⊢ A.

Corollary typing_subst_term Δ Γ Γ' A t τ :
  Δ ;; Γ ⊢ t : A ->
  wf_ctx Δ ->
  ctx_var_subst Δ Γ Γ' typ_var τ ->
  Δ ;; Γ' ⊢ t [typ_var;τ] : A.
Proof.
  intros. replace A with (A [typ_var]) by (asimpl; auto).
  eapply typing_subst; eauto.
  hauto unfold:ctx_tvar_subst,wf_ctx use:subtyping_reflexivity ctrs:subtyping simp+:asimpl.
Qed.

Lemma typing_abs_inv Δ Γ A A' B C t :
  Δ ;; Γ ⊢ exp_abs A t : B ->
  Δ ⊢ B <: typ_arr A' C ->
  ((Δ ⊢ A' <: A) /\ (exists C', (Δ ;; (A :: Γ) ⊢ t : C') /\ (Δ ⊢ C' <: C))).
Proof.
  move => H. move : C A'. dependent induction H; intros; try hauto ctrs:typing.
  - inversion H1; eauto.
  - eapply IHtyping; eauto.
    eapply subtyping_transitivity; eauto.
Qed.

Lemma typing_tabs_inv Δ Γ A A' B C t :
  Δ ;; Γ ⊢ exp_tabs A t : B ->
  Δ ⊢ B <: typ_all A' C ->
  ((Δ ⊢ A' <: A) /\ (exists C', ((A'::Δ) ;; (map (ren_typ ↑) Γ) ⊢ t : C') /\ (A'::Δ ⊢ C' <: C))).
Proof.
  move => H. move : C A'. 
    dependent induction H; intros; try hauto ctrs:typing.
  - inversion H1; subst; split; eauto. eexists; split; eauto.
    eapply (typing_narrowing _ nil); eauto.
  - eauto using subtyping_transitivity.
Qed.

Lemma value_arr_inv t A B :
  nil ;; nil ⊢ t : typ_arr A B ->
  is_value t ->
  exists A' t', t = exp_abs A' t'.
Proof.
  intros. dependent induction H; simpl;
    try hauto inv:lookup_var.
  - inversion H0; subst; eauto. inversion H2.
Qed.

Lemma value_all_inv t A B :
  nil ;; nil ⊢ t : typ_all A B ->
  is_value t ->
  exists A' t', t = exp_tabs A' t'.
Proof.
  intros. dependent induction H; simpl;
    try hauto inv:lookup_var.
  - inversion H0; subst; eauto. inversion H2.
Qed.
  
Theorem progress t A :
  nil ;; nil ⊢ t : A ->
  is_value t \/ exists t', t ⤳ t'.
Proof.
  intros. dependent induction H; subst; try hauto ctrs:typing.
  - inversion H.
  - ssimpl; try hauto ctrs:typing, step.
    hauto use:value_arr_inv ctrs:step.
  - ssimpl; try hauto ctrs:typing, step.
    hauto use:value_all_inv ctrs:step.
Qed.

Theorem preservation Δ Γ t A t' :
  Δ ;; Γ ⊢ t : A ->
  wf_ctx Δ ->
  t ⤳ t' ->
  Δ ;; Γ ⊢ t' : A.
Proof.
  move => Hty Hwf Hstep. move : Δ Γ A Hty Hwf.
  induction Hstep; intros; eauto using typing;
    dependent induction Hty; try hauto ctrs:typing.
  - inversion Hty1; subst.
    + eapply typing_subst_term; eauto.
      hauto unfold:ctx_var_subst inv:lookup_var ctrs:lookup_var,typing simp+:asimpl.
    + eapply typing_abs_inv in H1; eauto.
      ssimpl.
      eapply typing_sub with (A:=C'); eauto.
      eapply typing_subst_term; eauto.
      hauto unfold:ctx_var_subst inv:lookup_var ctrs:lookup_var,typing simp+:asimpl.
  - inversion Hty; subst.
    + eapply typing_subst; eauto. 
      * hauto unfold:ctx_tvar_subst,wf_ctx inv:lookup_tvar ctrs:subtyping use:subtyping_reflexivity simp+:asimpl.
      * unfold ctx_var_subst. intros. 
        apply lookup_var_map_inv in H0. ssimpl. asimpl. hauto ctrs:typing.
    + eapply typing_tabs_inv in H1; eauto.
      ssimpl. eapply typing_sub with (A:=C' [B..]).
      * eapply typing_subst; eauto.
        hauto unfold:ctx_tvar_subst,wf_ctx inv:lookup_tvar ctrs:subtyping use:subtyping_reflexivity simp+:asimpl. 
        unfold ctx_var_subst. intros. asimpl.
        apply lookup_var_map_inv in H3. ssimpl. asimpl. hauto ctrs:typing.
      * eapply subtyping_subst; eauto.
        hauto unfold:ctx_tvar_subst,wf_ctx inv:lookup_tvar ctrs:subtyping use:subtyping_reflexivity simp+:asimpl. 
Qed.