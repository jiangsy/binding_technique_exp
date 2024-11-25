Require Import Coq.Program.Equality.
Require Import Metalib.Metatheory.
From Hammer Require Import Tactics.

Require Import fsub.lngen.def_ott.
Require Import fsub.lngen.prop_ln.
Require Import common.ltac_ln.
Require Import common.prop_ln.
Require Import fsub.lngen.def_extra.

From Coq Require Import ssreflect ssrfun ssrbool.

Lemma wf_typ_lc_typ Γ A :
  Γ ⊢ A -> 
  lc_typ A.
Proof.
  intros. induction H; try hauto ctrs:lc_typ.
  - pick fresh X. inst_cofinites_with X.
    eapply lc_typ_all_exists with X; eauto.
Qed.

Lemma wf_typ_tvar_upper : forall Γ A,
  Γ ⊢ A ->
  tvar_in_typ A [<=] dom Γ.
Proof.
  intros. induction H; simpl in *; try fsetdec.
  - apply binds_In in H. fsetdec.
  - pick fresh X. inst_cofinites_with X.
    pose proof (tvar_in_typ_open_typ_wrt_typ_lower B (typ_var_f X)). fsetdec.
Qed.

Lemma wf_ctx_uniq Γ :
  ⊢ Γ ->
  uniq Γ.
Proof.
  intros. induction H; eauto.
Qed. 

Lemma wf_ctx_strengthening Γ1 Γ2 :
  ⊢ (Γ2 ++ Γ1) ->
  ⊢ Γ1.
Proof.
  intros. induction Γ2; hauto inv:wf_ctx.
Qed.

Hint Resolve wf_ctx_uniq : core.

Lemma binds_entry_upper X E Γ :
  binds X E Γ ->
  ⊢ Γ ->
  tvar_in_entry E [<=] dom Γ.
Proof.
  intros. induction Γ.
  - inversion H.
  - ssimpl; destruct_binds.
    + inversion H0; subst; auto. 
      rewrite <- wf_typ_tvar_upper; eauto. fsetdec.
      rewrite <- wf_typ_tvar_upper; eauto. fsetdec.
    + inversion H0; subst; auto; rewrite IHΓ; eauto; fsetdec.
Qed.

Lemma binds_subst_tvar Γ1 Γ2 X Y A B E:
  ⊢ (Γ2 ++ (Y, entry_tvar A) :: Γ1) ->
  binds X E (Γ2 ++ (Y, entry_tvar A) :: Γ1) ->
  X <> Y ->
  Γ1 ⊢ B ->
  binds X (subst_typ_in_entry B Y E) (map (subst_typ_in_entry B Y) Γ2 ++ Γ1).
Proof.
  intros. induction Γ2; simpl; eauto.
  - destruct_binds. ssimpl.
    rewrite subst_typ_in_entry_fresh_eq; eauto.
    rewrite binds_entry_upper; eauto.
  - destruct a; ssimpl.
    destruct_binds; eauto.
    inversion H; subst; eauto.
Qed.

Corollary binds_tvar_subst_tvar Γ1 Γ2 X Y A B C :
  ⊢ (Γ2 ++ (Y, entry_tvar A) :: Γ1) ->
  binds X (entry_tvar C) (Γ2 ++ (Y, entry_tvar A) :: Γ1) ->
  X <> Y ->
  Γ1 ⊢ B ->
  binds X (entry_tvar (subst_typ_in_typ B Y C)) (map (subst_typ_in_entry B Y) Γ2 ++ Γ1).
Proof.
  hauto use:binds_subst_tvar.
Qed.

Corollary binds_var_subst_tvar Γ1 Γ2 X Y A B C :
  ⊢ (Γ2 ++ (Y, entry_tvar A) :: Γ1) ->
  binds X (entry_var C) (Γ2 ++ (Y, entry_tvar A) :: Γ1) ->
  X <> Y ->
  Γ1 ⊢ B ->
  binds X (entry_var (subst_typ_in_typ B Y C)) (map (subst_typ_in_entry B Y) Γ2 ++ Γ1).
Proof.
  hauto use:binds_subst_tvar.
Qed.

Hint Resolve wf_typ_lc_typ : core.

Lemma wf_typ_weakening Γ1 Γ2 Γ3 A :
  (Γ3 ++ Γ1) ⊢ A ->
  (Γ3 ++ Γ2 ++ Γ1) ⊢ A.
Proof.
  intros. dependent induction H; try hauto ctrs:wf_typ.
  - eapply wf_typ_tvar; eauto. 
  - inst_cofinites_for wf_typ_all; eauto.
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

Hint Resolve subtyping_wf_typ1 subtyping_wf_typ2 : core.

Lemma wf_typ_subst_tvar Γ1 Γ2 X A B C : 
  (Γ2 ++ (X, entry_tvar B) :: Γ1) ⊢ A ->
  Γ1 ⊢ C ->
  (map (subst_typ_in_entry C X) Γ2 ++ Γ1) ⊢ subst_typ_in_typ C X A.
Proof.
  intros. dependent induction H; simpl; try hauto ctrs:wf_typ.
  - destruct_eq_atom; eauto. 
    + rewrite_env (nil ++ map (subst_typ_in_entry C X) Γ2 ++ Γ1).
      eapply wf_typ_weakening; hauto.
    + apply binds_remove_mid in H; eauto.
      apply binds_app_iff in H; inversion H. try hauto ctrs:typing.
      * apply wf_typ_tvar with (A:=subst_typ_in_typ C X A); eauto.
        replace (entry_tvar (subst_typ_in_typ C X A)) with (subst_typ_in_entry C X (entry_tvar A)) by auto.
        eapply binds_map in H1. apply binds_app_iff. left. eauto.
      * eapply wf_typ_tvar with (A:=A). apply binds_app_iff. hauto.
  - inst_cofinites_for wf_typ_all; eauto.
    intros. inst_cofinites_with X0.
    rewrite_env (map (subst_typ_in_entry C X) ((X0, entry_tvar A) :: Γ2) ++ Γ1).
    setoid_rewrite subst_typ_in_typ_open_typ_wrt_typ in H1; try hauto.
    move : H1 => /(_ _ _ X) H1.
    simpl in H1. destruct_eq_atom. 
    eapply H1; hauto.
Qed.

Lemma wf_ctx_subst_tvar Γ1 Γ2 X A B : 
  ⊢ (Γ2 ++ (X, entry_tvar A) :: Γ1) ->
  Γ1 ⊢ B ->
  ⊢ (map (subst_typ_in_entry B X) Γ2 ++ Γ1).
Proof.
  intros. induction Γ2; simpl.
  - hauto inv:wf_ctx use:wf_typ_subst_tvar.
  - destruct a; destruct e; simpl.
    + inversion H; subst.
      constructor; eauto.
      hauto use:wf_typ_subst_tvar.
    + inversion H; subst.
      constructor; eauto.
      hauto use:wf_typ_subst_tvar.
Qed.