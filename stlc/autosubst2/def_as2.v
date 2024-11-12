Require Import common.prop_as_core common.prop_as_unscoped.

Require Import Setoid Morphisms Relation_Definitions.


Module Core.

Inductive exp : Type :=
  | exp_var : nat -> exp
  | exp_abs : exp -> exp
  | exp_app : exp -> exp -> exp
  | exp_unit : exp.

Lemma congr_exp_abs {s0 : exp} {t0 : exp} (H0 : s0 = t0) :
  exp_abs s0 = exp_abs t0.
Proof.
exact (eq_trans eq_refl (ap (fun x => exp_abs x) H0)).
Qed.

Lemma congr_exp_app {s0 : exp} {s1 : exp} {t0 : exp} {t1 : exp}
  (H0 : s0 = t0) (H1 : s1 = t1) : exp_app s0 s1 = exp_app t0 t1.
Proof.
exact (eq_trans (eq_trans eq_refl (ap (fun x => exp_app x s1) H0))
         (ap (fun x => exp_app t0 x) H1)).
Qed.

Lemma congr_exp_unit : exp_unit = exp_unit.
Proof.
exact (eq_refl).
Qed.

Lemma upRen_exp_exp (xi : nat -> nat) : nat -> nat.
Proof.
exact (up_ren xi).
Defined.

Fixpoint ren_exp (xi_exp : nat -> nat) (s : exp) {struct s} : exp :=
  match s with
  | exp_var s0 => exp_var (xi_exp s0)
  | exp_abs s0 => exp_abs (ren_exp (upRen_exp_exp xi_exp) s0)
  | exp_app s0 s1 => exp_app (ren_exp xi_exp s0) (ren_exp xi_exp s1)
  | exp_unit => exp_unit
  end.

Lemma up_exp_exp (sigma : nat -> exp) : nat -> exp.
Proof.
exact (scons (exp_var var_zero) (funcomp (ren_exp shift) sigma)).
Defined.

Fixpoint subst_exp (sigma_exp : nat -> exp) (s : exp) {struct s} : exp :=
  match s with
  | exp_var s0 => sigma_exp s0
  | exp_abs s0 => exp_abs (subst_exp (up_exp_exp sigma_exp) s0)
  | exp_app s0 s1 =>
      exp_app (subst_exp sigma_exp s0) (subst_exp sigma_exp s1)
  | exp_unit => exp_unit
  end.

Lemma upId_exp_exp (sigma : nat -> exp) (Eq : forall x, sigma x = exp_var x)
  : forall x, up_exp_exp sigma x = exp_var x.
Proof.
exact (fun n =>
       match n with
       | S n' => ap (ren_exp shift) (Eq n')
       | O => eq_refl
       end).
Qed.

Fixpoint idSubst_exp (sigma_exp : nat -> exp)
(Eq_exp : forall x, sigma_exp x = exp_var x) (s : exp) {struct s} :
subst_exp sigma_exp s = s :=
  match s with
  | exp_var s0 => Eq_exp s0
  | exp_abs s0 =>
      congr_exp_abs
        (idSubst_exp (up_exp_exp sigma_exp) (upId_exp_exp _ Eq_exp) s0)
  | exp_app s0 s1 =>
      congr_exp_app (idSubst_exp sigma_exp Eq_exp s0)
        (idSubst_exp sigma_exp Eq_exp s1)
  | exp_unit => congr_exp_unit
  end.

Lemma upExtRen_exp_exp (xi : nat -> nat) (zeta : nat -> nat)
  (Eq : forall x, xi x = zeta x) :
  forall x, upRen_exp_exp xi x = upRen_exp_exp zeta x.
Proof.
exact (fun n => match n with
                | S n' => ap shift (Eq n')
                | O => eq_refl
                end).
Qed.

Fixpoint extRen_exp (xi_exp : nat -> nat) (zeta_exp : nat -> nat)
(Eq_exp : forall x, xi_exp x = zeta_exp x) (s : exp) {struct s} :
ren_exp xi_exp s = ren_exp zeta_exp s :=
  match s with
  | exp_var s0 => ap (exp_var) (Eq_exp s0)
  | exp_abs s0 =>
      congr_exp_abs
        (extRen_exp (upRen_exp_exp xi_exp) (upRen_exp_exp zeta_exp)
           (upExtRen_exp_exp _ _ Eq_exp) s0)
  | exp_app s0 s1 =>
      congr_exp_app (extRen_exp xi_exp zeta_exp Eq_exp s0)
        (extRen_exp xi_exp zeta_exp Eq_exp s1)
  | exp_unit => congr_exp_unit
  end.

Lemma upExt_exp_exp (sigma : nat -> exp) (tau : nat -> exp)
  (Eq : forall x, sigma x = tau x) :
  forall x, up_exp_exp sigma x = up_exp_exp tau x.
Proof.
exact (fun n =>
       match n with
       | S n' => ap (ren_exp shift) (Eq n')
       | O => eq_refl
       end).
Qed.

Fixpoint ext_exp (sigma_exp : nat -> exp) (tau_exp : nat -> exp)
(Eq_exp : forall x, sigma_exp x = tau_exp x) (s : exp) {struct s} :
subst_exp sigma_exp s = subst_exp tau_exp s :=
  match s with
  | exp_var s0 => Eq_exp s0
  | exp_abs s0 =>
      congr_exp_abs
        (ext_exp (up_exp_exp sigma_exp) (up_exp_exp tau_exp)
           (upExt_exp_exp _ _ Eq_exp) s0)
  | exp_app s0 s1 =>
      congr_exp_app (ext_exp sigma_exp tau_exp Eq_exp s0)
        (ext_exp sigma_exp tau_exp Eq_exp s1)
  | exp_unit => congr_exp_unit
  end.

Lemma up_ren_ren_exp_exp (xi : nat -> nat) (zeta : nat -> nat)
  (rho : nat -> nat) (Eq : forall x, funcomp zeta xi x = rho x) :
  forall x,
  funcomp (upRen_exp_exp zeta) (upRen_exp_exp xi) x = upRen_exp_exp rho x.
Proof.
exact (up_ren_ren xi zeta rho Eq).
Qed.

Fixpoint compRenRen_exp (xi_exp : nat -> nat) (zeta_exp : nat -> nat)
(rho_exp : nat -> nat)
(Eq_exp : forall x, funcomp zeta_exp xi_exp x = rho_exp x) (s : exp) {struct
 s} : ren_exp zeta_exp (ren_exp xi_exp s) = ren_exp rho_exp s :=
  match s with
  | exp_var s0 => ap (exp_var) (Eq_exp s0)
  | exp_abs s0 =>
      congr_exp_abs
        (compRenRen_exp (upRen_exp_exp xi_exp) (upRen_exp_exp zeta_exp)
           (upRen_exp_exp rho_exp) (up_ren_ren _ _ _ Eq_exp) s0)
  | exp_app s0 s1 =>
      congr_exp_app (compRenRen_exp xi_exp zeta_exp rho_exp Eq_exp s0)
        (compRenRen_exp xi_exp zeta_exp rho_exp Eq_exp s1)
  | exp_unit => congr_exp_unit
  end.

Lemma up_ren_subst_exp_exp (xi : nat -> nat) (tau : nat -> exp)
  (theta : nat -> exp) (Eq : forall x, funcomp tau xi x = theta x) :
  forall x,
  funcomp (up_exp_exp tau) (upRen_exp_exp xi) x = up_exp_exp theta x.
Proof.
exact (fun n =>
       match n with
       | S n' => ap (ren_exp shift) (Eq n')
       | O => eq_refl
       end).
Qed.

Fixpoint compRenSubst_exp (xi_exp : nat -> nat) (tau_exp : nat -> exp)
(theta_exp : nat -> exp)
(Eq_exp : forall x, funcomp tau_exp xi_exp x = theta_exp x) (s : exp) {struct
 s} : subst_exp tau_exp (ren_exp xi_exp s) = subst_exp theta_exp s :=
  match s with
  | exp_var s0 => Eq_exp s0
  | exp_abs s0 =>
      congr_exp_abs
        (compRenSubst_exp (upRen_exp_exp xi_exp) (up_exp_exp tau_exp)
           (up_exp_exp theta_exp) (up_ren_subst_exp_exp _ _ _ Eq_exp) s0)
  | exp_app s0 s1 =>
      congr_exp_app (compRenSubst_exp xi_exp tau_exp theta_exp Eq_exp s0)
        (compRenSubst_exp xi_exp tau_exp theta_exp Eq_exp s1)
  | exp_unit => congr_exp_unit
  end.

Lemma up_subst_ren_exp_exp (sigma : nat -> exp) (zeta_exp : nat -> nat)
  (theta : nat -> exp)
  (Eq : forall x, funcomp (ren_exp zeta_exp) sigma x = theta x) :
  forall x,
  funcomp (ren_exp (upRen_exp_exp zeta_exp)) (up_exp_exp sigma) x =
  up_exp_exp theta x.
Proof.
exact (fun n =>
       match n with
       | S n' =>
           eq_trans
             (compRenRen_exp shift (upRen_exp_exp zeta_exp)
                (funcomp shift zeta_exp) (fun x => eq_refl) (sigma n'))
             (eq_trans
                (eq_sym
                   (compRenRen_exp zeta_exp shift (funcomp shift zeta_exp)
                      (fun x => eq_refl) (sigma n')))
                (ap (ren_exp shift) (Eq n')))
       | O => eq_refl
       end).
Qed.

Fixpoint compSubstRen_exp (sigma_exp : nat -> exp) (zeta_exp : nat -> nat)
(theta_exp : nat -> exp)
(Eq_exp : forall x, funcomp (ren_exp zeta_exp) sigma_exp x = theta_exp x)
(s : exp) {struct s} :
ren_exp zeta_exp (subst_exp sigma_exp s) = subst_exp theta_exp s :=
  match s with
  | exp_var s0 => Eq_exp s0
  | exp_abs s0 =>
      congr_exp_abs
        (compSubstRen_exp (up_exp_exp sigma_exp) (upRen_exp_exp zeta_exp)
           (up_exp_exp theta_exp) (up_subst_ren_exp_exp _ _ _ Eq_exp) s0)
  | exp_app s0 s1 =>
      congr_exp_app (compSubstRen_exp sigma_exp zeta_exp theta_exp Eq_exp s0)
        (compSubstRen_exp sigma_exp zeta_exp theta_exp Eq_exp s1)
  | exp_unit => congr_exp_unit
  end.

Lemma up_subst_subst_exp_exp (sigma : nat -> exp) (tau_exp : nat -> exp)
  (theta : nat -> exp)
  (Eq : forall x, funcomp (subst_exp tau_exp) sigma x = theta x) :
  forall x,
  funcomp (subst_exp (up_exp_exp tau_exp)) (up_exp_exp sigma) x =
  up_exp_exp theta x.
Proof.
exact (fun n =>
       match n with
       | S n' =>
           eq_trans
             (compRenSubst_exp shift (up_exp_exp tau_exp)
                (funcomp (up_exp_exp tau_exp) shift) (fun x => eq_refl)
                (sigma n'))
             (eq_trans
                (eq_sym
                   (compSubstRen_exp tau_exp shift
                      (funcomp (ren_exp shift) tau_exp) (fun x => eq_refl)
                      (sigma n'))) (ap (ren_exp shift) (Eq n')))
       | O => eq_refl
       end).
Qed.

Fixpoint compSubstSubst_exp (sigma_exp : nat -> exp) (tau_exp : nat -> exp)
(theta_exp : nat -> exp)
(Eq_exp : forall x, funcomp (subst_exp tau_exp) sigma_exp x = theta_exp x)
(s : exp) {struct s} :
subst_exp tau_exp (subst_exp sigma_exp s) = subst_exp theta_exp s :=
  match s with
  | exp_var s0 => Eq_exp s0
  | exp_abs s0 =>
      congr_exp_abs
        (compSubstSubst_exp (up_exp_exp sigma_exp) (up_exp_exp tau_exp)
           (up_exp_exp theta_exp) (up_subst_subst_exp_exp _ _ _ Eq_exp) s0)
  | exp_app s0 s1 =>
      congr_exp_app
        (compSubstSubst_exp sigma_exp tau_exp theta_exp Eq_exp s0)
        (compSubstSubst_exp sigma_exp tau_exp theta_exp Eq_exp s1)
  | exp_unit => congr_exp_unit
  end.

Lemma renRen_exp (xi_exp : nat -> nat) (zeta_exp : nat -> nat) (s : exp) :
  ren_exp zeta_exp (ren_exp xi_exp s) = ren_exp (funcomp zeta_exp xi_exp) s.
Proof.
exact (compRenRen_exp xi_exp zeta_exp _ (fun n => eq_refl) s).
Qed.

Lemma renRen'_exp_pointwise (xi_exp : nat -> nat) (zeta_exp : nat -> nat) :
  pointwise_relation _ eq (funcomp (ren_exp zeta_exp) (ren_exp xi_exp))
    (ren_exp (funcomp zeta_exp xi_exp)).
Proof.
exact (fun s => compRenRen_exp xi_exp zeta_exp _ (fun n => eq_refl) s).
Qed.

Lemma renSubst_exp (xi_exp : nat -> nat) (tau_exp : nat -> exp) (s : exp) :
  subst_exp tau_exp (ren_exp xi_exp s) = subst_exp (funcomp tau_exp xi_exp) s.
Proof.
exact (compRenSubst_exp xi_exp tau_exp _ (fun n => eq_refl) s).
Qed.

Lemma renSubst_exp_pointwise (xi_exp : nat -> nat) (tau_exp : nat -> exp) :
  pointwise_relation _ eq (funcomp (subst_exp tau_exp) (ren_exp xi_exp))
    (subst_exp (funcomp tau_exp xi_exp)).
Proof.
exact (fun s => compRenSubst_exp xi_exp tau_exp _ (fun n => eq_refl) s).
Qed.

Lemma substRen_exp (sigma_exp : nat -> exp) (zeta_exp : nat -> nat) (s : exp)
  :
  ren_exp zeta_exp (subst_exp sigma_exp s) =
  subst_exp (funcomp (ren_exp zeta_exp) sigma_exp) s.
Proof.
exact (compSubstRen_exp sigma_exp zeta_exp _ (fun n => eq_refl) s).
Qed.

Lemma substRen_exp_pointwise (sigma_exp : nat -> exp) (zeta_exp : nat -> nat)
  :
  pointwise_relation _ eq (funcomp (ren_exp zeta_exp) (subst_exp sigma_exp))
    (subst_exp (funcomp (ren_exp zeta_exp) sigma_exp)).
Proof.
exact (fun s => compSubstRen_exp sigma_exp zeta_exp _ (fun n => eq_refl) s).
Qed.

Lemma substSubst_exp (sigma_exp : nat -> exp) (tau_exp : nat -> exp)
  (s : exp) :
  subst_exp tau_exp (subst_exp sigma_exp s) =
  subst_exp (funcomp (subst_exp tau_exp) sigma_exp) s.
Proof.
exact (compSubstSubst_exp sigma_exp tau_exp _ (fun n => eq_refl) s).
Qed.

Lemma substSubst_exp_pointwise (sigma_exp : nat -> exp)
  (tau_exp : nat -> exp) :
  pointwise_relation _ eq (funcomp (subst_exp tau_exp) (subst_exp sigma_exp))
    (subst_exp (funcomp (subst_exp tau_exp) sigma_exp)).
Proof.
exact (fun s => compSubstSubst_exp sigma_exp tau_exp _ (fun n => eq_refl) s).
Qed.

Lemma rinstInst_up_exp_exp (xi : nat -> nat) (sigma : nat -> exp)
  (Eq : forall x, funcomp (exp_var) xi x = sigma x) :
  forall x, funcomp (exp_var) (upRen_exp_exp xi) x = up_exp_exp sigma x.
Proof.
exact (fun n =>
       match n with
       | S n' => ap (ren_exp shift) (Eq n')
       | O => eq_refl
       end).
Qed.

Fixpoint rinst_inst_exp (xi_exp : nat -> nat) (sigma_exp : nat -> exp)
(Eq_exp : forall x, funcomp (exp_var) xi_exp x = sigma_exp x) (s : exp)
{struct s} : ren_exp xi_exp s = subst_exp sigma_exp s :=
  match s with
  | exp_var s0 => Eq_exp s0
  | exp_abs s0 =>
      congr_exp_abs
        (rinst_inst_exp (upRen_exp_exp xi_exp) (up_exp_exp sigma_exp)
           (rinstInst_up_exp_exp _ _ Eq_exp) s0)
  | exp_app s0 s1 =>
      congr_exp_app (rinst_inst_exp xi_exp sigma_exp Eq_exp s0)
        (rinst_inst_exp xi_exp sigma_exp Eq_exp s1)
  | exp_unit => congr_exp_unit
  end.

Lemma rinstInst'_exp (xi_exp : nat -> nat) (s : exp) :
  ren_exp xi_exp s = subst_exp (funcomp (exp_var) xi_exp) s.
Proof.
exact (rinst_inst_exp xi_exp _ (fun n => eq_refl) s).
Qed.

Lemma rinstInst'_exp_pointwise (xi_exp : nat -> nat) :
  pointwise_relation _ eq (ren_exp xi_exp)
    (subst_exp (funcomp (exp_var) xi_exp)).
Proof.
exact (fun s => rinst_inst_exp xi_exp _ (fun n => eq_refl) s).
Qed.

Lemma instId'_exp (s : exp) : subst_exp (exp_var) s = s.
Proof.
exact (idSubst_exp (exp_var) (fun n => eq_refl) s).
Qed.

Lemma instId'_exp_pointwise :
  pointwise_relation _ eq (subst_exp (exp_var)) id.
Proof.
exact (fun s => idSubst_exp (exp_var) (fun n => eq_refl) s).
Qed.

Lemma rinstId'_exp (s : exp) : ren_exp id s = s.
Proof.
exact (eq_ind_r (fun t => t = s) (instId'_exp s) (rinstInst'_exp id s)).
Qed.

Lemma rinstId'_exp_pointwise : pointwise_relation _ eq (@ren_exp id) id.
Proof.
exact (fun s =>
       eq_ind_r (fun t => t = s) (instId'_exp s) (rinstInst'_exp id s)).
Qed.

Lemma varL'_exp (sigma_exp : nat -> exp) (x : nat) :
  subst_exp sigma_exp (exp_var x) = sigma_exp x.
Proof.
exact (eq_refl).
Qed.

Lemma varL'_exp_pointwise (sigma_exp : nat -> exp) :
  pointwise_relation _ eq (funcomp (subst_exp sigma_exp) (exp_var)) sigma_exp.
Proof.
exact (fun x => eq_refl).
Qed.

Lemma varLRen'_exp (xi_exp : nat -> nat) (x : nat) :
  ren_exp xi_exp (exp_var x) = exp_var (xi_exp x).
Proof.
exact (eq_refl).
Qed.

Lemma varLRen'_exp_pointwise (xi_exp : nat -> nat) :
  pointwise_relation _ eq (funcomp (ren_exp xi_exp) (exp_var))
    (funcomp (exp_var) xi_exp).
Proof.
exact (fun x => eq_refl).
Qed.

Inductive typ : Type :=
  | typ_unit : typ
  | typ_arr : typ -> typ -> typ.

Lemma congr_typ_unit : typ_unit = typ_unit.
Proof.
exact (eq_refl).
Qed.

Lemma congr_typ_arr {s0 : typ} {s1 : typ} {t0 : typ} {t1 : typ}
  (H0 : s0 = t0) (H1 : s1 = t1) : typ_arr s0 s1 = typ_arr t0 t1.
Proof.
exact (eq_trans (eq_trans eq_refl (ap (fun x => typ_arr x s1) H0))
         (ap (fun x => typ_arr t0 x) H1)).
Qed.

Class Up_exp X Y :=
    up_exp : X -> Y.

#[global]Instance Subst_exp : (Subst1 _ _ _) := @subst_exp.

#[global]Instance Up_exp_exp : (Up_exp _ _) := @up_exp_exp.

#[global]Instance Ren_exp : (Ren1 _ _ _) := @ren_exp.

#[global]
Instance VarInstance_exp : (Var _ _) := @exp_var.

Notation "[ sigma_exp ]" := (subst_exp sigma_exp)
( at level 1, left associativity, only printing)  : fscope.

Notation "s [ sigma_exp ]" := (subst_exp sigma_exp s)
( at level 7, left associativity, only printing)  : subst_scope.

Notation "↑__exp" := up_exp (only printing)  : subst_scope.

Notation "↑__exp" := up_exp_exp (only printing)  : subst_scope.

Notation "⟨ xi_exp ⟩" := (ren_exp xi_exp)
( at level 1, left associativity, only printing)  : fscope.

Notation "s ⟨ xi_exp ⟩" := (ren_exp xi_exp s)
( at level 7, left associativity, only printing)  : subst_scope.

Notation "'var'" := exp_var ( at level 1, only printing)  : subst_scope.

Notation "x '__exp'" := (@ids _ _ VarInstance_exp x)
( at level 5, format "x __exp", only printing)  : subst_scope.

Notation "x '__exp'" := (exp_var x) ( at level 5, format "x __exp")  :
subst_scope.

#[global]
Instance subst_exp_morphism :
 (Proper (respectful (pointwise_relation _ eq) (respectful eq eq))
    (@subst_exp)).
Proof.
exact (fun f_exp g_exp Eq_exp s t Eq_st =>
       eq_ind s (fun t' => subst_exp f_exp s = subst_exp g_exp t')
         (ext_exp f_exp g_exp Eq_exp s) t Eq_st).
Qed.

#[global]
Instance subst_exp_morphism2 :
 (Proper (respectful (pointwise_relation _ eq) (pointwise_relation _ eq))
    (@subst_exp)).
Proof.
exact (fun f_exp g_exp Eq_exp s => ext_exp f_exp g_exp Eq_exp s).
Qed.

#[global]
Instance ren_exp_morphism :
 (Proper (respectful (pointwise_relation _ eq) (respectful eq eq)) (@ren_exp)).
Proof.
exact (fun f_exp g_exp Eq_exp s t Eq_st =>
       eq_ind s (fun t' => ren_exp f_exp s = ren_exp g_exp t')
         (extRen_exp f_exp g_exp Eq_exp s) t Eq_st).
Qed.

#[global]
Instance ren_exp_morphism2 :
 (Proper (respectful (pointwise_relation _ eq) (pointwise_relation _ eq))
    (@ren_exp)).
Proof.
exact (fun f_exp g_exp Eq_exp s => extRen_exp f_exp g_exp Eq_exp s).
Qed.

Ltac auto_unfold := repeat
                     unfold VarInstance_exp, Var, ids, Ren_exp, Ren1, ren1,
                      Up_exp_exp, Up_exp, up_exp, Subst_exp, Subst1, subst1.

Tactic Notation "auto_unfold" "in" "*" := repeat
                                           unfold VarInstance_exp, Var, ids,
                                            Ren_exp, Ren1, ren1, Up_exp_exp,
                                            Up_exp, up_exp, Subst_exp,
                                            Subst1, subst1 in *.

Ltac asimpl' := repeat (first
                 [ progress setoid_rewrite substSubst_exp_pointwise
                 | progress setoid_rewrite substSubst_exp
                 | progress setoid_rewrite substRen_exp_pointwise
                 | progress setoid_rewrite substRen_exp
                 | progress setoid_rewrite renSubst_exp_pointwise
                 | progress setoid_rewrite renSubst_exp
                 | progress setoid_rewrite renRen'_exp_pointwise
                 | progress setoid_rewrite renRen_exp
                 | progress setoid_rewrite varLRen'_exp_pointwise
                 | progress setoid_rewrite varLRen'_exp
                 | progress setoid_rewrite varL'_exp_pointwise
                 | progress setoid_rewrite varL'_exp
                 | progress setoid_rewrite rinstId'_exp_pointwise
                 | progress setoid_rewrite rinstId'_exp
                 | progress setoid_rewrite instId'_exp_pointwise
                 | progress setoid_rewrite instId'_exp
                 | progress unfold up_exp_exp, upRen_exp_exp, up_ren
                 | progress cbn[subst_exp ren_exp]
                 | progress fsimpl ]).

Ltac asimpl := check_no_evars;
                repeat
                 unfold VarInstance_exp, Var, ids, Ren_exp, Ren1, ren1,
                  Up_exp_exp, Up_exp, up_exp, Subst_exp, Subst1, subst1 
                  in *; asimpl'; minimize.

Tactic Notation "asimpl" "in" hyp(J) := revert J; asimpl; intros J.

Tactic Notation "auto_case" := auto_case ltac:(asimpl; cbn; eauto).

Ltac substify := auto_unfold; try setoid_rewrite rinstInst'_exp_pointwise;
                  try setoid_rewrite rinstInst'_exp.

Ltac renamify := auto_unfold;
                  try setoid_rewrite_left rinstInst'_exp_pointwise;
                  try setoid_rewrite_left rinstInst'_exp.

End Core.

Module Extra.

Import Core.

#[global]Hint Opaque subst_exp: rewrite.

#[global]Hint Opaque ren_exp: rewrite.

End Extra.

Module interface.

Export Core.

Export Extra.

End interface.

Export interface.

