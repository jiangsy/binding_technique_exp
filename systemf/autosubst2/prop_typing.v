Require Import Coq.Program.Equality.
Require Import List.

Require Import common.prop_as_core.
Require Import common.prop_as_unscoped.
Require Import systemf.autosubst2.def_as2.
Require Import systemf.autosubst2.def_extra.

Import SubstNotations.
Import UnscopedNotations.

Definition lookup_fun {T} n (Δ : list T) :=
  nth_error Δ n.

Hint Constructors lookup : core.

Lemma lookup_iff {T} n (Γ : list T) A : lookup n Γ A -> lookup_fun n Γ = Some A.
Proof.
  intros. induction H; eauto.
Qed.

Lemma lookup_det {U} n (Γ : list U) A B : lookup n Γ A -> lookup n Γ B -> A = B.
Proof.
  intros. induction H; inversion H0; eauto.
Qed.

Definition ctx_var_rename {T} ζ Γ Δ :=
  forall i (A : T), lookup i Γ A -> lookup (ζ i) Δ A.

Lemma lookup_map {T} : forall (A : T) (f : T -> T) (Γ : list T) x ,
  lookup x Γ A -> lookup x (map f Γ) (f A).
Proof.
  intros. induction H; simpl; eauto.
Qed.

Lemma lookup_map_inv {T} : forall x A' (f : T -> T) Γ,
  lookup x (map f Γ) A' -> exists A, A' = (f A) /\ lookup x Γ A.
Proof.
  intros. dependent induction H; destruct Γ; inversion x; subst; eauto.
  pose proof (IHlookup _ _ (eq_refl _)).
  destruct H0; subst; intuition; eauto.
Qed.

Lemma ctx_var_rename_refl {T} : forall Γ : list T,
  ctx_var_rename id Γ Γ.
Proof.
  intros. unfold ctx_var_rename. intros. eauto.
Qed.

Lemma ctx_var_rename_map {T} : forall Γ Δ ζ (f : T -> T),
  ctx_var_rename ζ Γ Δ -> ctx_var_rename ζ (list_map f Γ) (list_map f Δ).
Proof.
  intros. unfold ctx_var_rename in *. intros.
  apply lookup_map_inv in H0. destruct H0 as [A' [Hf Hl]].
  subst.
  apply H in Hl.
  apply lookup_map; eauto.
Qed.

Theorem typing_rename Γ t A : 
  Γ ⊢ t : A ->
  forall Δ ξ ζ,
    ctx_var_rename ζ Γ Δ ->
    (map (ren_typ ξ) Δ) ⊢ t ⟨ξ;ζ⟩ : A ⟨ξ⟩.
Proof.
  intros H. induction H; intros; asimpl.
  - eapply typing_var.
    eapply lookup_map; eauto.
  - eapply typing_abs.
    replace ((ren_typ ξ A) :: (list_map (ren_typ ξ) Δ)) with (map (ren_typ ξ) (A :: Δ)) by auto.
    eapply IHtyping; eauto.
    unfold ctx_var_rename; intros.
    inversion H1; subst; eauto.
    fsimpl. inversion H1; subst; eauto. econstructor.
    eapply H0; eauto.
  - eapply typing_app; eauto. 
  - eapply typing_tabs; asimpl; eauto.
    apply ctx_var_rename_map with (f := ren_typ ↑) in H0.
    eapply IHtyping with (ξ := 0 .: ξ >> S) in H0; eauto.
    erewrite list_comp; eauto.
    erewrite list_comp in H0; eauto.
    intros. asimpl; auto.
  - rewrite H0.
    eapply IHtyping with (ξ := ξ) in H1; eauto.
    eapply typing_tapp with (A:=A ⟨up_ren ξ⟩).
    + eauto.
    + asimpl. auto.
Qed.

Lemma ctx_map_id : forall Γ,
  map (ren_typ id) Γ = Γ.
Proof.
  intros. induction Γ; simpl; eauto.
  rewrite <- IHΓ at 2; asimpl; eauto.
Qed.

Corollary typing_weaken : forall Γ t A B,
  Γ ⊢ t : A ->
  (B :: Γ) ⊢ t ⟨id ; ↑⟩ : A.
Proof.
  intros. rewrite <- (ctx_map_id (B :: Γ)).
  replace A with (A ⟨id⟩) by (asimpl; auto).
  eapply typing_rename; eauto.
  - unfold ctx_var_rename. intros. eauto.
Qed.

Definition ctx_var_subst Γ Δ τ ρ := 
  forall x A, lookup x Γ A -> Δ ⊢ τ x : A [ρ].

Theorem typing_subst Γ t A : 
  Γ ⊢ t : A ->
  forall Δ τ ρ,
    (* maybe some wf conditions? *)
    ctx_var_subst Γ Δ τ ρ ->
    Δ ⊢ t [ρ;τ] : A [ρ].
Proof.
  intros H. induction H; asimpl; intros.
  - eauto.
  - eapply typing_abs.
    assert (ctx_var_subst (A :: Γ) (A [ρ] :: Δ) ((up_exp_exp τ)) (ρ)).
    + unfold ctx_var_subst in *. intros.
      inversion H1; subst; asimpl; eauto.
      * econstructor; eauto.
      * apply H0 in H6. fsimpl. eauto. 
        apply typing_weaken with (B:=A [ρ]) in H6. eauto.
    + eapply IHtyping in H1. asimpl. eauto.
  - eapply typing_app; eauto. 
  - eapply typing_tabs.
    eapply IHtyping. unfold ctx_var_subst in *. intros.
    apply lookup_map_inv in H1. destruct H1 as [A' [Hf Hl]]. subst.
    apply H0 in Hl.
    eapply typing_rename with (ξ:=↑) (ζ:=id) (Δ:=Δ) in Hl.
    + asimpl in Hl. asimpl. auto.
    + eapply ctx_var_rename_refl; eauto. 
  - eapply typing_tapp with (A := subst_typ (up_typ_typ ρ) A); eauto.
    + rewrite H0. asimpl. auto.
Qed.

(* see also *)
(* https://github.com/qcfu-bu/TYDE23/blob/50bd676e830e76beae7809a67ddcd19bc4e903b2/coq/theories/clc_substitution.v#L703 *)