Require Import stlc.lngen.def_ott.
Require Import stlc.lngen.prop_ln.
Require Import stlc.lngen.def_extra.

Require Import Coq.Program.Equality.

Hint Constructors typing : core.

Theorem typing_subst Γ1 Γ2 x s t A B:
  x `notin` dom (Γ2 ++ Γ1) ->
  Γ2 ++ (x, B) :: Γ1 ⊢ t : A ->
  Γ1 ⊢ s : B ->
  Γ2 ++ Γ1 ⊢ (subst_exp_in_exp s x t) : A.
Proof.
  intros. dependent induction H0; eauto.
  - simpl. destruct (x0 == x). admit.
  - admit.
  - simpl. eapply typing_app; eauto.
Admitted.

Corollary typing_subst0 Γ x s t A B: 
  ((x, B) :: Γ) ⊢ t : A ->
  Γ ⊢ s : B ->
  Γ ⊢ (subst_exp_in_exp s x t) : A.
Proof.
  intros. rewrite <- (app_nil_l Γ). eapply typing_subst; eauto.
Qed.

Theorem preservation Γ t t' A : 
  Γ ⊢ t : A ->
  t ⤳ t' ->
  Γ ⊢ t' : A.
Proof.
  intros Htyping Hstep. generalize dependent A.
  induction Hstep; intros; inversion Htyping; subst; eauto.
  - inversion H2. subst. admit.
Admitted.