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