Require Import Coq.Program.Equality.
Require Import Metalib.Metatheory.
From Hammer Require Import Tactics.

Require Import fsub.lngen.def_ott.
Require Import fsub.lngen.prop_ln.
Require Import common.ltac_ln.
Require Import common.prop_ln.
Require Import fsub.lngen.def_extra.

Lemma wf_typ_lc_typ Γ A :
  Γ ⊢ A -> 
  lc_typ A.
Proof.
  intros. induction H; try hauto ctrs:lc_typ.
  - pick fresh X. inst_cofinites_with X.
    eapply lc_typ_all_exists with X; eauto.
Qed.

Lemma subtyping_lc_typ Γ A B :
  Γ ⊢ A <: B -> 
  lc_typ A /\ lc_typ B.
Proof.
  intros. induction H; try hauto ctrs:lc_typ use:wf_typ_lc_typ.
  - split; pick fresh X; inst_cofinites_with X; 
    eapply lc_typ_all_exists with X; hauto.
Qed.

Lemma wf_typ_weakening Γ1 Γ2 Γ3 A :
  (Γ3 ++ Γ1) ⊢ A ->
  (Γ3 ++ Γ2 ++ Γ1) ⊢ A.
Proof.
  intros. dependent induction H; try hauto ctrs:wf_typ.
  - eapply wf_typ_tvar; eauto. 
  - inst_cofinites_for wf_typ_all; eauto.
    intros.   
    intros. inst_cofinites_with X.
    rewrite_env (((X, entry_tvar A) :: Γ3) ++ Γ2 ++ Γ1); eauto.
Qed.

Lemma wf_typ_rebinding Γ1 Γ2 X A B B' :
  (Γ2 ++ ((X, entry_tvar B) :: Γ1)) ⊢ A ->
  (Γ2 ++ ((X, entry_tvar B') :: Γ1)) ⊢ A.
Proof.
  intros. dependent induction H; try hauto ctrs:wf_typ use:wf_typ_weakening.
  - destruct (X == X0); subst; eauto.
    + eapply wf_typ_tvar; eauto.
    + eapply wf_typ_tvar with (A:=A); eauto.
      eapply binds_remove_mid in H; eauto.
      rewrite_env (Γ2 ++ (X ~ entry_tvar B') ++ Γ1).
      eapply binds_weaken; eauto.
  - inst_cofinites_for wf_typ_all; eauto.
    intros.   
    intros. inst_cofinites_with X.
    rewrite_env (((X0, entry_tvar A) :: Γ2) ++ (X, entry_tvar B') :: Γ1).
    eapply H1; eauto. simpl; eauto.
Qed.

Lemma subtyping_weakening Γ1 Γ2 Γ3 A B :
  (Γ3 ++ Γ1) ⊢ A <: B ->
  (Γ3 ++ Γ2 ++ Γ1) ⊢ A <: B.
Proof.
  intros. dependent induction H; try hauto ctrs:subtyping use:wf_typ_weakening.
  - eapply sub_tvar_bound with (A:=A).
    + apply binds_weaken; eauto.
    + eauto.
  - inst_cofinites_for sub_all.
    + hauto use:wf_typ_weakening.
    + eauto.
    + intros. inst_cofinites_with X.
      rewrite_env (((X, entry_tvar B1) :: Γ3) ++ Γ2 ++ Γ1). 
      eapply H2; eauto. 
Qed.

Lemma subtyping_wf_typ Γ A B :
  Γ ⊢ A <: B -> 
  Γ ⊢ A /\ Γ ⊢ B.
Proof.
  intros. induction H; try hauto ctrs:wf_typ.
  - split; inst_cofinites_for wf_typ_all; 
    intros; inst_cofinites_with X; try hauto.
    rewrite_env (nil ++ (X, entry_tvar A1) :: Γ). 
    eapply wf_typ_rebinding; simpl; hauto.
Qed.

Corollary subtyping_wf_typ1 Γ A B :
  Γ ⊢ A <: B -> 
  Γ ⊢ A.
Proof.
  hauto use:subtyping_wf_typ.
Qed.

Corollary subtyping_wf_typ2 Γ A B :
  Γ ⊢ A <: B -> 
  Γ ⊢ B.
Proof.
  hauto use:subtyping_wf_typ.
Qed.