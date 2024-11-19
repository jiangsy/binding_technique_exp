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

Lemma wf_typ_renaming_tvar Γ Γ' A ξ:
  Γ ⊢ A ->
  ctx_tvar_rename_weak Γ Γ' ξ ->
  Γ' ⊢ A ⟨ ξ ⟩.
Proof.
  move: Γ Γ' ξ. induction A; try hauto.
  - intros. unfold ctx_tvar_rename_weak in *.
    asimpl. simpl in *. 
    hauto inv:lookup_tvar ctrs:lookup_tvar.
Qed.

Lemma wf_typ_renaming_tvar' Γ Γ' A A' ξ:
  Γ ⊢ A ->
  ctx_tvar_rename_weak Γ Γ' ξ ->
  A' = A ⟨ ξ ⟩ ->
  Γ' ⊢ A'.
Proof.
  intros. subst. eapply wf_typ_renaming_tvar; eauto.
Qed.

Corollary wf_typ_weakening_tvar0 Γ A B:
  Γ ⊢ A ->
  ((entry_tvar B) :: Γ) ⊢ A ⟨↑⟩.
Proof.
  hauto unfold:ctx_tvar_rename_weak inv:lookup_tvar ctrs:lookup_tvar
    use:wf_typ_renaming_tvar.
Qed.

Lemma wf_typ_subst_tvar Γ Γ' A σ:
  Γ ⊢ A ->
  ctx_tvar_subst_wf Γ Γ' σ ->
  Γ' ⊢ A [ σ ].
Proof.
  move: Γ Γ' σ. induction A; intros; 
    try hauto unfold:ctx_tvar_subst_wf.
  - asimpl. simpl in *; split.
    + hauto. 
    + eapply IHA2; hauto unfold:ctx_tvar_subst_wf use:wf_typ_weakening_tvar0 inv:lookup_tvar. 
Qed.

Lemma wf_typ_narrowing : forall Γ1 Γ2 A B C,
  Γ2 ++ (entry_tvar A) :: Γ1 ⊢ C->
  Γ2 ++ (entry_tvar B) :: Γ1 ⊢ C.
Proof.
  intros. eapply wf_typ_renaming_tvar' with (ξ:=id) in H; eauto.
  - eapply ctx_tvar_rename_weak_rebounding; eauto.
  - asimpl; auto.
Qed.

Lemma sub_renaming_tvar Γ Γ' A B ξ :
  Γ ⊢ A <: B ->
  ctx_tvar_rename Γ Γ' ξ ->
  Γ' ⊢ A ⟨ ξ ⟩ <: B ⟨ ξ ⟩.
Proof.
  move => H.
  move: Γ' ξ. elim: Γ A B / H; intros; 
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

Corollary sub_weakening_tvar0 Γ A B C:
  Γ ⊢ A <: B ->
  (entry_tvar C :: Γ) ⊢ A ⟨↑⟩ <: B ⟨↑⟩.
Proof.
  hauto unfold:ctx_tvar_rename ctrs:subtyping use:sub_renaming_tvar ctrs:lookup_tvar.
Qed.

Lemma sub_wf_typ Γ A B :
  Γ ⊢ A <: B ->
  (Γ ⊢ A) /\ (Γ ⊢ B).
Proof.
  intros; induction H; try hauto.
  - simpl; repeat split; try hauto.
    replace (A2) with (A2 ⟨id⟩) by (asimpl; auto).
    hauto unfold:ctx_tvar_rename_weak 
      inv:lookup_tvar ctrs:lookup_tvar use:wf_typ_renaming_tvar.
Qed.

Corollary sub_wf_typ1 Γ A B :
  Γ ⊢ A <: B ->
  Γ ⊢ A.
Proof.
  hauto use:sub_wf_typ.
Qed.

Corollary sub_wf_typ2 Γ A B :
  Γ ⊢ A <: B ->
  Γ ⊢ B.
Proof.
  hauto use:sub_wf_typ.
Qed.

Definition ctx_var_rename Γ Γ' ξ ζ :=
  forall x A, lookup_var x Γ A -> lookup_var (ζ x) Γ' (A ⟨ ξ ⟩).

(* Fixpoint map_entry_tvar (f: typ -> typ) (Γ: list entry) :=
  match Γ with
  | nil => nil
  | (entry_tvar A) :: Γ' => (entry_tvar (f A)) :: (map_entry_tvar f Γ')
  | (entry_var A) :: Γ' => (entry_var A) :: (map_entry_tvar f Γ')
  end.

Fixpoint map_entry_var (f: typ -> typ) (Γ: list entry) :=
  match Γ with
  | nil => nil
  | (entry_tvar A) :: Γ' => (entry_tvar A) :: (map_entry_var f Γ')
  | (entry_var A) :: Γ' => (entry_var (f A)) :: (map_entry_var f Γ')
  end.

Lemma lookup_map : forall A f Γ x ,
  lookup_var x Γ A -> lookup_var x (map_entry_var f Γ) (f A).
Proof.
  intros.  generalize dependent f. induction H; simpl; auto using lookup_var.
  - intros. eapply skip_tvar. econstructor.
Qed.

Lemma lookup_var_map_inv : forall x A' f Γ,
  lookup_var x (map f Γ) A' -> exists A, A' = (f A) /\ lookup_var x Γ A.
Proof.
  intros. dependent induction H; 
    destruct Γ; hauto inv:lookup_var ctrs:lookup_var.
Qed. *)