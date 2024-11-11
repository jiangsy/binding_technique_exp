Require Import stlc.autosubst2.prop_as_core.
Require Import stlc.autosubst2.prop_as_unscoped.
Require Import stlc.autosubst2.def_as2.
Require Import stlc.autosubst2.def_typing.

Definition ctx_var_rename {T} ζ Γ Δ :=
  forall i (A : T), lookup i Γ A -> lookup (ζ i) Δ A.

Import SubstNotations.
Import UnscopedNotations.

Hint Constructors lookup typing : core.

Theorem typing_rename Γ t A : 
  Γ ⊢ t : A ->
  forall Δ ζ,
    ctx_var_rename ζ Γ Δ ->
    Δ ⊢ t ⟨ζ⟩ : A.
Proof.
  intros H. induction H; intros; asimpl; eauto.
  - apply typing_abs. 
    eapply IHtyping; eauto.
    unfold ctx_var_rename in *. intros.
    inversion H1; subst; asimpl; eauto.
    econstructor. eauto.
Qed.