Require Import Coq.Program.Equality.
Require Export Metalib.Metatheory.

Ltac unify_binds :=
  match goal with
  | H_1 : binds ?X ?b1 ?θ, H_2 : binds ?X ?b2 ?θ |- _ =>
    let H_3 := fresh "H" in
    apply binds_unique with (a:=b2) in H_1 as H_3; eauto; dependent destruction H_3; subst
  end.

Lemma binds_remove_mid_diff_bind {A} : forall ls1 ls2 X Y (b1 b2 : A),
  binds X b1 (ls2 ++ (Y, b2) :: ls1) ->
  b1 <> b2 ->
  binds X b1 (ls2 ++ ls1).
Proof.  
  intros. induction ls2; simpl in *; eauto.
  - inversion H. dependent destruction H1.
    + contradiction.
    + auto. 
  - destruct a. inversion H.
    + dependent destruction H1. auto.
    + auto.
Qed.

Lemma uniq_rebind : forall {T} ls1 ls2 X (b1 b2 : T),
  uniq (ls2 ++ (X, b1) :: ls1) ->
  uniq (ls2 ++ (X, b2) :: ls1).
Proof.
  intros. induction ls2; simpl in *; eauto.
  - inversion H; eauto.
  - destruct a. inversion H; eauto.
Qed.

Lemma binds_exact {T} ls1 ls2 X (b1 b2 : T) :
  uniq (ls2 ++ (X, b2) :: ls1) ->
  binds X b1 (ls2 ++ (X, b2) :: ls1) -> b1 = b2.
Proof.
  intros.
  assert (binds X b2 (ls2 ++ (X, b2) :: ls1)) by auto.
  unify_binds.
Qed.

Lemma binds_rebind_mid {T} : forall ls1 ls2 X Y (b1 b2 b2' : T),
  X <> Y ->
  binds X b1 (ls1 ++ (Y, b2'):: ls2) ->
  binds X b1 (ls1 ++ (Y, b2) :: ls2).
Proof.
  intros. rewrite_env (ls1 ++ (Y ~ b2) ++ ls2).
  rewrite_env (ls1 ++ (Y ~ b2') ++ ls2) in H0.
  apply binds_weaken; eauto.
Qed.