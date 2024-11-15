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

Definition ctx_tvar_subst_wf Δ Δ' σ :=
  forall X A, lookup_tvar X Δ A -> Δ' ⊢ σ X.

Lemma ctx_tvar_rename_weak_rebounding Δ1 Δ2 A A':
  ctx_tvar_rename_weak (Δ2 ++ A :: Δ1)  (Δ2 ++ A' :: Δ1) id.
Proof.
  intros. induction Δ2; simpl;
    hauto unfold:ctx_tvar_rename_weak inv:lookup_tvar ctrs:lookup_tvar.
Qed.

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

Lemma wf_typ_renaming_tvar' Δ Δ' A A' ξ:
  Δ ⊢ A ->
  ctx_tvar_rename_weak Δ Δ' ξ ->
  A' = A ⟨ ξ ⟩ ->
  Δ' ⊢ A'.
Proof.
  intros. subst. eapply wf_typ_renaming_tvar; eauto.
Qed.

Corollary wf_typ_weakening_tvar0 Δ A B:
  Δ ⊢ A ->
  (B :: Δ) ⊢ A ⟨↑⟩.
Proof.
  hauto unfold:ctx_tvar_rename_weak inv:lookup_tvar ctrs:lookup_tvar
    use:wf_typ_renaming_tvar.
Qed.


Lemma wf_typ_subst_tvar Δ Δ' A σ:
  Δ ⊢ A ->
  ctx_tvar_subst_wf Δ Δ' σ ->
  Δ' ⊢ A [ σ ].
Proof.
  move: Δ Δ' σ. induction A; intros; 
    try hauto unfold:ctx_tvar_subst_wf.
  - asimpl. simpl in *; split.
    + hauto. 
    + eapply IHA2; hauto unfold:ctx_tvar_subst_wf use:wf_typ_weakening_tvar0 inv:lookup_tvar. 
Qed.

Lemma sub_renaming_tvar Δ Δ' A B ξ :
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

Corollary sub_weakening_tvar0 Δ A B C:
  Δ ⊢ A <: B ->
  (C :: Δ) ⊢ A ⟨↑⟩ <: B ⟨↑⟩.
Proof.
  hauto unfold:ctx_tvar_rename ctrs:subtyping use:sub_renaming_tvar.
Qed.

Lemma sub_wf_typ Δ A B :
  Δ ⊢ A <: B ->
  (Δ ⊢ A) /\ (Δ ⊢ B).
Proof.
  intros; induction H; try hauto.
  - simpl; repeat split; try hauto.
    replace (A2) with (A2 ⟨id⟩) by (asimpl; auto).
    hauto unfold:ctx_tvar_rename_weak 
      inv:lookup_tvar ctrs:lookup_tvar use:wf_typ_renaming_tvar.
Qed.

Corollary sub_wf_typ1 Δ A B :
  Δ ⊢ A <: B ->
  Δ ⊢ A.
Proof.
  hauto use:sub_wf_typ.
Qed.

Corollary sub_wf_typ2 Δ A B :
  Δ ⊢ A <: B ->
  Δ ⊢ B.
Proof.
  hauto use:sub_wf_typ.
Qed.

Definition ctx_var_rename Γ Γ' ξ ζ :=
  forall x A, lookup_var x Γ A -> lookup_var (ζ x) Γ' (A ⟨ ξ ⟩).

Lemma lookup_map : forall A f Γ x ,
  lookup_var x Γ A -> lookup_var x (map f Γ) (f A).
Proof.
  intros. induction H; hauto inv:lookup_var ctrs:lookup_var.
Qed.

Lemma lookup_var_map_inv : forall x A' f Γ,
  lookup_var x (map f Γ) A' -> exists A, A' = (f A) /\ lookup_var x Γ A.
Proof.
  intros. dependent induction H; 
    destruct Γ; hauto inv:lookup_var ctrs:lookup_var.
Qed.

Lemma typing_renaming Δ Δ' Γ Γ' t A ξ ζ:
  Δ ;; Γ ⊢ t : A ->
  ctx_tvar_rename Δ Δ' ξ ->
  ctx_var_rename Γ Γ' ξ ζ ->
  Δ' ;; Γ' ⊢ t ⟨ξ;ζ⟩ : A ⟨ξ⟩.
Proof.
  move => H.
  move : Δ' Γ' ξ ζ.
  elim : Δ Γ t A / H; intros; asimpl;
    try hauto unfold!:ctx_var_rename,ctx_tvar_rename use:typing.
  - eapply typing_abs.
    + hauto use:wf_typ_renaming_tvar unfold:ctx_tvar_rename_weak,ctx_tvar_rename.
    + eapply H1; eauto.
      hauto unfold:ctx_var_rename inv:lookup_var ctrs:lookup_var.
  - eapply typing_tabs; asimpl; eauto.
    + hauto use:wf_typ_renaming_tvar unfold:ctx_tvar_rename_weak,ctx_tvar_rename.
    + eapply H1; eauto.
      (* seems hard to fully automate the following proof *)
      * unfold ctx_tvar_rename in *. intros. asimpl. 
        inversion H4; subst.
        -- asimpl. replace (ren_typ (ξ >> S) A) with (A ⟨ξ⟩ ⟨S⟩) by (asimpl; auto).
           hauto inv:lookup_tvar ctrs:lookup_tvar.
        -- asimpl. replace (ren_typ (ξ >> S) A0) with (A0 ⟨ξ⟩ ⟨S⟩) by (asimpl; auto).
           hauto inv:lookup_tvar ctrs:lookup_tvar.
      * unfold ctx_var_rename in *. intros. asimpl.
        eapply lookup_var_map_inv in H4.
        destruct H4 as [A' [H4 H5]]. subst.
        replace (ren_typ (0 .: ξ >> S) (ren_typ ↑ A')) with (A' ⟨↑ >> (0 .: ξ >> S)⟩) by (asimpl; auto).
        asimpl.
        replace (ren_typ (ξ >> S) A') with (A' ⟨ξ⟩ ⟨S⟩) by (asimpl; auto). 
        eapply lookup_map; eauto.
  - subst. asimpl. 
    eapply typing_tapp with (A:=A ⟨ξ⟩) (B:=B ⟨up_ren ξ⟩); eauto.
    + hauto use:sub_renaming_tvar ctrs:subtyping.
    + asimpl. auto.
  - eapply typing_sub; eauto.
    eapply sub_renaming_tvar; eauto.
Qed.

Corollary typing_weakening_tvar0 Δ Γ t A B:
  Δ ;; Γ ⊢ t : A ->
  (B :: Δ) ;; (map (ren_typ ↑) Γ) ⊢ t ⟨↑;id⟩ : A ⟨↑⟩.
Proof.
  intros. eapply typing_renaming; eauto.
  - hauto unfold:ctx_tvar_rename use:lookup_tvar. 
  - hauto unfold:ctx_var_rename use:lookup_map.
Qed.

Corollary typing_weakening_var0 Δ Γ t A B:
  Δ ;; Γ ⊢ t : A ->
  Δ ;; (B :: Γ) ⊢ t ⟨id;↑⟩ : A.
Proof.
  intros. replace (A) with (ren_typ id A) by (asimpl; auto). 
    eapply typing_renaming; eauto.
  - unfold ctx_tvar_rename. intros. asimpl. auto.
  - unfold ctx_var_rename. intros. asimpl.
    hauto ctrs:lookup_var.
Qed.