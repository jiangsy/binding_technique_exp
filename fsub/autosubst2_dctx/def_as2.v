Require Import common.prop_as_core common.prop_as_unscoped.

Require Import Setoid Morphisms Relation_Definitions.


Module Core.

Inductive typ : Type :=
  | typ_var : nat -> typ
  | typ_arr : typ -> typ -> typ
  | typ_all : typ -> typ -> typ
  | typ_top : typ.

Lemma congr_typ_arr {s0 : typ} {s1 : typ} {t0 : typ} {t1 : typ}
  (H0 : s0 = t0) (H1 : s1 = t1) : typ_arr s0 s1 = typ_arr t0 t1.
Proof.
exact (eq_trans (eq_trans eq_refl (ap (fun x => typ_arr x s1) H0))
         (ap (fun x => typ_arr t0 x) H1)).
Qed.

Lemma congr_typ_all {s0 : typ} {s1 : typ} {t0 : typ} {t1 : typ}
  (H0 : s0 = t0) (H1 : s1 = t1) : typ_all s0 s1 = typ_all t0 t1.
Proof.
exact (eq_trans (eq_trans eq_refl (ap (fun x => typ_all x s1) H0))
         (ap (fun x => typ_all t0 x) H1)).
Qed.

Lemma congr_typ_top : typ_top = typ_top.
Proof.
exact (eq_refl).
Qed.

Lemma upRen_typ_typ (xi : nat -> nat) : nat -> nat.
Proof.
exact (up_ren xi).
Defined.

Fixpoint ren_typ (xi_typ : nat -> nat) (s : typ) {struct s} : typ :=
  match s with
  | typ_var s0 => typ_var (xi_typ s0)
  | typ_arr s0 s1 => typ_arr (ren_typ xi_typ s0) (ren_typ xi_typ s1)
  | typ_all s0 s1 =>
      typ_all (ren_typ xi_typ s0) (ren_typ (upRen_typ_typ xi_typ) s1)
  | typ_top => typ_top
  end.

Lemma up_typ_typ (sigma : nat -> typ) : nat -> typ.
Proof.
exact (scons (typ_var var_zero) (funcomp (ren_typ shift) sigma)).
Defined.

Fixpoint subst_typ (sigma_typ : nat -> typ) (s : typ) {struct s} : typ :=
  match s with
  | typ_var s0 => sigma_typ s0
  | typ_arr s0 s1 =>
      typ_arr (subst_typ sigma_typ s0) (subst_typ sigma_typ s1)
  | typ_all s0 s1 =>
      typ_all (subst_typ sigma_typ s0) (subst_typ (up_typ_typ sigma_typ) s1)
  | typ_top => typ_top
  end.

Lemma upId_typ_typ (sigma : nat -> typ) (Eq : forall x, sigma x = typ_var x)
  : forall x, up_typ_typ sigma x = typ_var x.
Proof.
exact (fun n =>
       match n with
       | S n' => ap (ren_typ shift) (Eq n')
       | O => eq_refl
       end).
Qed.

Fixpoint idSubst_typ (sigma_typ : nat -> typ)
(Eq_typ : forall x, sigma_typ x = typ_var x) (s : typ) {struct s} :
subst_typ sigma_typ s = s :=
  match s with
  | typ_var s0 => Eq_typ s0
  | typ_arr s0 s1 =>
      congr_typ_arr (idSubst_typ sigma_typ Eq_typ s0)
        (idSubst_typ sigma_typ Eq_typ s1)
  | typ_all s0 s1 =>
      congr_typ_all (idSubst_typ sigma_typ Eq_typ s0)
        (idSubst_typ (up_typ_typ sigma_typ) (upId_typ_typ _ Eq_typ) s1)
  | typ_top => congr_typ_top
  end.

Lemma upExtRen_typ_typ (xi : nat -> nat) (zeta : nat -> nat)
  (Eq : forall x, xi x = zeta x) :
  forall x, upRen_typ_typ xi x = upRen_typ_typ zeta x.
Proof.
exact (fun n => match n with
                | S n' => ap shift (Eq n')
                | O => eq_refl
                end).
Qed.

Fixpoint extRen_typ (xi_typ : nat -> nat) (zeta_typ : nat -> nat)
(Eq_typ : forall x, xi_typ x = zeta_typ x) (s : typ) {struct s} :
ren_typ xi_typ s = ren_typ zeta_typ s :=
  match s with
  | typ_var s0 => ap (typ_var) (Eq_typ s0)
  | typ_arr s0 s1 =>
      congr_typ_arr (extRen_typ xi_typ zeta_typ Eq_typ s0)
        (extRen_typ xi_typ zeta_typ Eq_typ s1)
  | typ_all s0 s1 =>
      congr_typ_all (extRen_typ xi_typ zeta_typ Eq_typ s0)
        (extRen_typ (upRen_typ_typ xi_typ) (upRen_typ_typ zeta_typ)
           (upExtRen_typ_typ _ _ Eq_typ) s1)
  | typ_top => congr_typ_top
  end.

Lemma upExt_typ_typ (sigma : nat -> typ) (tau : nat -> typ)
  (Eq : forall x, sigma x = tau x) :
  forall x, up_typ_typ sigma x = up_typ_typ tau x.
Proof.
exact (fun n =>
       match n with
       | S n' => ap (ren_typ shift) (Eq n')
       | O => eq_refl
       end).
Qed.

Fixpoint ext_typ (sigma_typ : nat -> typ) (tau_typ : nat -> typ)
(Eq_typ : forall x, sigma_typ x = tau_typ x) (s : typ) {struct s} :
subst_typ sigma_typ s = subst_typ tau_typ s :=
  match s with
  | typ_var s0 => Eq_typ s0
  | typ_arr s0 s1 =>
      congr_typ_arr (ext_typ sigma_typ tau_typ Eq_typ s0)
        (ext_typ sigma_typ tau_typ Eq_typ s1)
  | typ_all s0 s1 =>
      congr_typ_all (ext_typ sigma_typ tau_typ Eq_typ s0)
        (ext_typ (up_typ_typ sigma_typ) (up_typ_typ tau_typ)
           (upExt_typ_typ _ _ Eq_typ) s1)
  | typ_top => congr_typ_top
  end.

Lemma up_ren_ren_typ_typ (xi : nat -> nat) (zeta : nat -> nat)
  (rho : nat -> nat) (Eq : forall x, funcomp zeta xi x = rho x) :
  forall x,
  funcomp (upRen_typ_typ zeta) (upRen_typ_typ xi) x = upRen_typ_typ rho x.
Proof.
exact (up_ren_ren xi zeta rho Eq).
Qed.

Fixpoint compRenRen_typ (xi_typ : nat -> nat) (zeta_typ : nat -> nat)
(rho_typ : nat -> nat)
(Eq_typ : forall x, funcomp zeta_typ xi_typ x = rho_typ x) (s : typ) {struct
 s} : ren_typ zeta_typ (ren_typ xi_typ s) = ren_typ rho_typ s :=
  match s with
  | typ_var s0 => ap (typ_var) (Eq_typ s0)
  | typ_arr s0 s1 =>
      congr_typ_arr (compRenRen_typ xi_typ zeta_typ rho_typ Eq_typ s0)
        (compRenRen_typ xi_typ zeta_typ rho_typ Eq_typ s1)
  | typ_all s0 s1 =>
      congr_typ_all (compRenRen_typ xi_typ zeta_typ rho_typ Eq_typ s0)
        (compRenRen_typ (upRen_typ_typ xi_typ) (upRen_typ_typ zeta_typ)
           (upRen_typ_typ rho_typ) (up_ren_ren _ _ _ Eq_typ) s1)
  | typ_top => congr_typ_top
  end.

Lemma up_ren_subst_typ_typ (xi : nat -> nat) (tau : nat -> typ)
  (theta : nat -> typ) (Eq : forall x, funcomp tau xi x = theta x) :
  forall x,
  funcomp (up_typ_typ tau) (upRen_typ_typ xi) x = up_typ_typ theta x.
Proof.
exact (fun n =>
       match n with
       | S n' => ap (ren_typ shift) (Eq n')
       | O => eq_refl
       end).
Qed.

Fixpoint compRenSubst_typ (xi_typ : nat -> nat) (tau_typ : nat -> typ)
(theta_typ : nat -> typ)
(Eq_typ : forall x, funcomp tau_typ xi_typ x = theta_typ x) (s : typ) {struct
 s} : subst_typ tau_typ (ren_typ xi_typ s) = subst_typ theta_typ s :=
  match s with
  | typ_var s0 => Eq_typ s0
  | typ_arr s0 s1 =>
      congr_typ_arr (compRenSubst_typ xi_typ tau_typ theta_typ Eq_typ s0)
        (compRenSubst_typ xi_typ tau_typ theta_typ Eq_typ s1)
  | typ_all s0 s1 =>
      congr_typ_all (compRenSubst_typ xi_typ tau_typ theta_typ Eq_typ s0)
        (compRenSubst_typ (upRen_typ_typ xi_typ) (up_typ_typ tau_typ)
           (up_typ_typ theta_typ) (up_ren_subst_typ_typ _ _ _ Eq_typ) s1)
  | typ_top => congr_typ_top
  end.

Lemma up_subst_ren_typ_typ (sigma : nat -> typ) (zeta_typ : nat -> nat)
  (theta : nat -> typ)
  (Eq : forall x, funcomp (ren_typ zeta_typ) sigma x = theta x) :
  forall x,
  funcomp (ren_typ (upRen_typ_typ zeta_typ)) (up_typ_typ sigma) x =
  up_typ_typ theta x.
Proof.
exact (fun n =>
       match n with
       | S n' =>
           eq_trans
             (compRenRen_typ shift (upRen_typ_typ zeta_typ)
                (funcomp shift zeta_typ) (fun x => eq_refl) (sigma n'))
             (eq_trans
                (eq_sym
                   (compRenRen_typ zeta_typ shift (funcomp shift zeta_typ)
                      (fun x => eq_refl) (sigma n')))
                (ap (ren_typ shift) (Eq n')))
       | O => eq_refl
       end).
Qed.

Fixpoint compSubstRen_typ (sigma_typ : nat -> typ) (zeta_typ : nat -> nat)
(theta_typ : nat -> typ)
(Eq_typ : forall x, funcomp (ren_typ zeta_typ) sigma_typ x = theta_typ x)
(s : typ) {struct s} :
ren_typ zeta_typ (subst_typ sigma_typ s) = subst_typ theta_typ s :=
  match s with
  | typ_var s0 => Eq_typ s0
  | typ_arr s0 s1 =>
      congr_typ_arr (compSubstRen_typ sigma_typ zeta_typ theta_typ Eq_typ s0)
        (compSubstRen_typ sigma_typ zeta_typ theta_typ Eq_typ s1)
  | typ_all s0 s1 =>
      congr_typ_all (compSubstRen_typ sigma_typ zeta_typ theta_typ Eq_typ s0)
        (compSubstRen_typ (up_typ_typ sigma_typ) (upRen_typ_typ zeta_typ)
           (up_typ_typ theta_typ) (up_subst_ren_typ_typ _ _ _ Eq_typ) s1)
  | typ_top => congr_typ_top
  end.

Lemma up_subst_subst_typ_typ (sigma : nat -> typ) (tau_typ : nat -> typ)
  (theta : nat -> typ)
  (Eq : forall x, funcomp (subst_typ tau_typ) sigma x = theta x) :
  forall x,
  funcomp (subst_typ (up_typ_typ tau_typ)) (up_typ_typ sigma) x =
  up_typ_typ theta x.
Proof.
exact (fun n =>
       match n with
       | S n' =>
           eq_trans
             (compRenSubst_typ shift (up_typ_typ tau_typ)
                (funcomp (up_typ_typ tau_typ) shift) (fun x => eq_refl)
                (sigma n'))
             (eq_trans
                (eq_sym
                   (compSubstRen_typ tau_typ shift
                      (funcomp (ren_typ shift) tau_typ) (fun x => eq_refl)
                      (sigma n'))) (ap (ren_typ shift) (Eq n')))
       | O => eq_refl
       end).
Qed.

Fixpoint compSubstSubst_typ (sigma_typ : nat -> typ) (tau_typ : nat -> typ)
(theta_typ : nat -> typ)
(Eq_typ : forall x, funcomp (subst_typ tau_typ) sigma_typ x = theta_typ x)
(s : typ) {struct s} :
subst_typ tau_typ (subst_typ sigma_typ s) = subst_typ theta_typ s :=
  match s with
  | typ_var s0 => Eq_typ s0
  | typ_arr s0 s1 =>
      congr_typ_arr
        (compSubstSubst_typ sigma_typ tau_typ theta_typ Eq_typ s0)
        (compSubstSubst_typ sigma_typ tau_typ theta_typ Eq_typ s1)
  | typ_all s0 s1 =>
      congr_typ_all
        (compSubstSubst_typ sigma_typ tau_typ theta_typ Eq_typ s0)
        (compSubstSubst_typ (up_typ_typ sigma_typ) (up_typ_typ tau_typ)
           (up_typ_typ theta_typ) (up_subst_subst_typ_typ _ _ _ Eq_typ) s1)
  | typ_top => congr_typ_top
  end.

Lemma renRen_typ (xi_typ : nat -> nat) (zeta_typ : nat -> nat) (s : typ) :
  ren_typ zeta_typ (ren_typ xi_typ s) = ren_typ (funcomp zeta_typ xi_typ) s.
Proof.
exact (compRenRen_typ xi_typ zeta_typ _ (fun n => eq_refl) s).
Qed.

Lemma renRen'_typ_pointwise (xi_typ : nat -> nat) (zeta_typ : nat -> nat) :
  pointwise_relation _ eq (funcomp (ren_typ zeta_typ) (ren_typ xi_typ))
    (ren_typ (funcomp zeta_typ xi_typ)).
Proof.
exact (fun s => compRenRen_typ xi_typ zeta_typ _ (fun n => eq_refl) s).
Qed.

Lemma renSubst_typ (xi_typ : nat -> nat) (tau_typ : nat -> typ) (s : typ) :
  subst_typ tau_typ (ren_typ xi_typ s) = subst_typ (funcomp tau_typ xi_typ) s.
Proof.
exact (compRenSubst_typ xi_typ tau_typ _ (fun n => eq_refl) s).
Qed.

Lemma renSubst_typ_pointwise (xi_typ : nat -> nat) (tau_typ : nat -> typ) :
  pointwise_relation _ eq (funcomp (subst_typ tau_typ) (ren_typ xi_typ))
    (subst_typ (funcomp tau_typ xi_typ)).
Proof.
exact (fun s => compRenSubst_typ xi_typ tau_typ _ (fun n => eq_refl) s).
Qed.

Lemma substRen_typ (sigma_typ : nat -> typ) (zeta_typ : nat -> nat) (s : typ)
  :
  ren_typ zeta_typ (subst_typ sigma_typ s) =
  subst_typ (funcomp (ren_typ zeta_typ) sigma_typ) s.
Proof.
exact (compSubstRen_typ sigma_typ zeta_typ _ (fun n => eq_refl) s).
Qed.

Lemma substRen_typ_pointwise (sigma_typ : nat -> typ) (zeta_typ : nat -> nat)
  :
  pointwise_relation _ eq (funcomp (ren_typ zeta_typ) (subst_typ sigma_typ))
    (subst_typ (funcomp (ren_typ zeta_typ) sigma_typ)).
Proof.
exact (fun s => compSubstRen_typ sigma_typ zeta_typ _ (fun n => eq_refl) s).
Qed.

Lemma substSubst_typ (sigma_typ : nat -> typ) (tau_typ : nat -> typ)
  (s : typ) :
  subst_typ tau_typ (subst_typ sigma_typ s) =
  subst_typ (funcomp (subst_typ tau_typ) sigma_typ) s.
Proof.
exact (compSubstSubst_typ sigma_typ tau_typ _ (fun n => eq_refl) s).
Qed.

Lemma substSubst_typ_pointwise (sigma_typ : nat -> typ)
  (tau_typ : nat -> typ) :
  pointwise_relation _ eq (funcomp (subst_typ tau_typ) (subst_typ sigma_typ))
    (subst_typ (funcomp (subst_typ tau_typ) sigma_typ)).
Proof.
exact (fun s => compSubstSubst_typ sigma_typ tau_typ _ (fun n => eq_refl) s).
Qed.

Lemma rinstInst_up_typ_typ (xi : nat -> nat) (sigma : nat -> typ)
  (Eq : forall x, funcomp (typ_var) xi x = sigma x) :
  forall x, funcomp (typ_var) (upRen_typ_typ xi) x = up_typ_typ sigma x.
Proof.
exact (fun n =>
       match n with
       | S n' => ap (ren_typ shift) (Eq n')
       | O => eq_refl
       end).
Qed.

Fixpoint rinst_inst_typ (xi_typ : nat -> nat) (sigma_typ : nat -> typ)
(Eq_typ : forall x, funcomp (typ_var) xi_typ x = sigma_typ x) (s : typ)
{struct s} : ren_typ xi_typ s = subst_typ sigma_typ s :=
  match s with
  | typ_var s0 => Eq_typ s0
  | typ_arr s0 s1 =>
      congr_typ_arr (rinst_inst_typ xi_typ sigma_typ Eq_typ s0)
        (rinst_inst_typ xi_typ sigma_typ Eq_typ s1)
  | typ_all s0 s1 =>
      congr_typ_all (rinst_inst_typ xi_typ sigma_typ Eq_typ s0)
        (rinst_inst_typ (upRen_typ_typ xi_typ) (up_typ_typ sigma_typ)
           (rinstInst_up_typ_typ _ _ Eq_typ) s1)
  | typ_top => congr_typ_top
  end.

Lemma rinstInst'_typ (xi_typ : nat -> nat) (s : typ) :
  ren_typ xi_typ s = subst_typ (funcomp (typ_var) xi_typ) s.
Proof.
exact (rinst_inst_typ xi_typ _ (fun n => eq_refl) s).
Qed.

Lemma rinstInst'_typ_pointwise (xi_typ : nat -> nat) :
  pointwise_relation _ eq (ren_typ xi_typ)
    (subst_typ (funcomp (typ_var) xi_typ)).
Proof.
exact (fun s => rinst_inst_typ xi_typ _ (fun n => eq_refl) s).
Qed.

Lemma instId'_typ (s : typ) : subst_typ (typ_var) s = s.
Proof.
exact (idSubst_typ (typ_var) (fun n => eq_refl) s).
Qed.

Lemma instId'_typ_pointwise :
  pointwise_relation _ eq (subst_typ (typ_var)) id.
Proof.
exact (fun s => idSubst_typ (typ_var) (fun n => eq_refl) s).
Qed.

Lemma rinstId'_typ (s : typ) : ren_typ id s = s.
Proof.
exact (eq_ind_r (fun t => t = s) (instId'_typ s) (rinstInst'_typ id s)).
Qed.

Lemma rinstId'_typ_pointwise : pointwise_relation _ eq (@ren_typ id) id.
Proof.
exact (fun s =>
       eq_ind_r (fun t => t = s) (instId'_typ s) (rinstInst'_typ id s)).
Qed.

Lemma varL'_typ (sigma_typ : nat -> typ) (x : nat) :
  subst_typ sigma_typ (typ_var x) = sigma_typ x.
Proof.
exact (eq_refl).
Qed.

Lemma varL'_typ_pointwise (sigma_typ : nat -> typ) :
  pointwise_relation _ eq (funcomp (subst_typ sigma_typ) (typ_var)) sigma_typ.
Proof.
exact (fun x => eq_refl).
Qed.

Lemma varLRen'_typ (xi_typ : nat -> nat) (x : nat) :
  ren_typ xi_typ (typ_var x) = typ_var (xi_typ x).
Proof.
exact (eq_refl).
Qed.

Lemma varLRen'_typ_pointwise (xi_typ : nat -> nat) :
  pointwise_relation _ eq (funcomp (ren_typ xi_typ) (typ_var))
    (funcomp (typ_var) xi_typ).
Proof.
exact (fun x => eq_refl).
Qed.

Inductive exp : Type :=
  | exp_var : nat -> exp
  | exp_app : exp -> exp -> exp
  | exp_abs : typ -> exp -> exp
  | exp_tapp : exp -> typ -> exp
  | exp_tabs : typ -> exp -> exp.

Lemma congr_exp_app {s0 : exp} {s1 : exp} {t0 : exp} {t1 : exp}
  (H0 : s0 = t0) (H1 : s1 = t1) : exp_app s0 s1 = exp_app t0 t1.
Proof.
exact (eq_trans (eq_trans eq_refl (ap (fun x => exp_app x s1) H0))
         (ap (fun x => exp_app t0 x) H1)).
Qed.

Lemma congr_exp_abs {s0 : typ} {s1 : exp} {t0 : typ} {t1 : exp}
  (H0 : s0 = t0) (H1 : s1 = t1) : exp_abs s0 s1 = exp_abs t0 t1.
Proof.
exact (eq_trans (eq_trans eq_refl (ap (fun x => exp_abs x s1) H0))
         (ap (fun x => exp_abs t0 x) H1)).
Qed.

Lemma congr_exp_tapp {s0 : exp} {s1 : typ} {t0 : exp} {t1 : typ}
  (H0 : s0 = t0) (H1 : s1 = t1) : exp_tapp s0 s1 = exp_tapp t0 t1.
Proof.
exact (eq_trans (eq_trans eq_refl (ap (fun x => exp_tapp x s1) H0))
         (ap (fun x => exp_tapp t0 x) H1)).
Qed.

Lemma congr_exp_tabs {s0 : typ} {s1 : exp} {t0 : typ} {t1 : exp}
  (H0 : s0 = t0) (H1 : s1 = t1) : exp_tabs s0 s1 = exp_tabs t0 t1.
Proof.
exact (eq_trans (eq_trans eq_refl (ap (fun x => exp_tabs x s1) H0))
         (ap (fun x => exp_tabs t0 x) H1)).
Qed.

Lemma upRen_typ_exp (xi : nat -> nat) : nat -> nat.
Proof.
exact (xi).
Defined.

Lemma upRen_exp_typ (xi : nat -> nat) : nat -> nat.
Proof.
exact (xi).
Defined.

Lemma upRen_exp_exp (xi : nat -> nat) : nat -> nat.
Proof.
exact (up_ren xi).
Defined.

Fixpoint ren_exp (xi_typ : nat -> nat) (xi_exp : nat -> nat) (s : exp)
{struct s} : exp :=
  match s with
  | exp_var s0 => exp_var (xi_exp s0)
  | exp_app s0 s1 =>
      exp_app (ren_exp xi_typ xi_exp s0) (ren_exp xi_typ xi_exp s1)
  | exp_abs s0 s1 =>
      exp_abs (ren_typ xi_typ s0)
        (ren_exp (upRen_exp_typ xi_typ) (upRen_exp_exp xi_exp) s1)
  | exp_tapp s0 s1 => exp_tapp (ren_exp xi_typ xi_exp s0) (ren_typ xi_typ s1)
  | exp_tabs s0 s1 =>
      exp_tabs (ren_typ xi_typ s0)
        (ren_exp (upRen_typ_typ xi_typ) (upRen_typ_exp xi_exp) s1)
  end.

Lemma up_typ_exp (sigma : nat -> exp) : nat -> exp.
Proof.
exact (funcomp (ren_exp shift id) sigma).
Defined.

Lemma up_exp_typ (sigma : nat -> typ) : nat -> typ.
Proof.
exact (funcomp (ren_typ id) sigma).
Defined.

Lemma up_exp_exp (sigma : nat -> exp) : nat -> exp.
Proof.
exact (scons (exp_var var_zero) (funcomp (ren_exp id shift) sigma)).
Defined.

Fixpoint subst_exp (sigma_typ : nat -> typ) (sigma_exp : nat -> exp)
(s : exp) {struct s} : exp :=
  match s with
  | exp_var s0 => sigma_exp s0
  | exp_app s0 s1 =>
      exp_app (subst_exp sigma_typ sigma_exp s0)
        (subst_exp sigma_typ sigma_exp s1)
  | exp_abs s0 s1 =>
      exp_abs (subst_typ sigma_typ s0)
        (subst_exp (up_exp_typ sigma_typ) (up_exp_exp sigma_exp) s1)
  | exp_tapp s0 s1 =>
      exp_tapp (subst_exp sigma_typ sigma_exp s0) (subst_typ sigma_typ s1)
  | exp_tabs s0 s1 =>
      exp_tabs (subst_typ sigma_typ s0)
        (subst_exp (up_typ_typ sigma_typ) (up_typ_exp sigma_exp) s1)
  end.

Lemma upId_typ_exp (sigma : nat -> exp) (Eq : forall x, sigma x = exp_var x)
  : forall x, up_typ_exp sigma x = exp_var x.
Proof.
exact (fun n => ap (ren_exp shift id) (Eq n)).
Qed.

Lemma upId_exp_typ (sigma : nat -> typ) (Eq : forall x, sigma x = typ_var x)
  : forall x, up_exp_typ sigma x = typ_var x.
Proof.
exact (fun n => ap (ren_typ id) (Eq n)).
Qed.

Lemma upId_exp_exp (sigma : nat -> exp) (Eq : forall x, sigma x = exp_var x)
  : forall x, up_exp_exp sigma x = exp_var x.
Proof.
exact (fun n =>
       match n with
       | S n' => ap (ren_exp id shift) (Eq n')
       | O => eq_refl
       end).
Qed.

Fixpoint idSubst_exp (sigma_typ : nat -> typ) (sigma_exp : nat -> exp)
(Eq_typ : forall x, sigma_typ x = typ_var x)
(Eq_exp : forall x, sigma_exp x = exp_var x) (s : exp) {struct s} :
subst_exp sigma_typ sigma_exp s = s :=
  match s with
  | exp_var s0 => Eq_exp s0
  | exp_app s0 s1 =>
      congr_exp_app (idSubst_exp sigma_typ sigma_exp Eq_typ Eq_exp s0)
        (idSubst_exp sigma_typ sigma_exp Eq_typ Eq_exp s1)
  | exp_abs s0 s1 =>
      congr_exp_abs (idSubst_typ sigma_typ Eq_typ s0)
        (idSubst_exp (up_exp_typ sigma_typ) (up_exp_exp sigma_exp)
           (upId_exp_typ _ Eq_typ) (upId_exp_exp _ Eq_exp) s1)
  | exp_tapp s0 s1 =>
      congr_exp_tapp (idSubst_exp sigma_typ sigma_exp Eq_typ Eq_exp s0)
        (idSubst_typ sigma_typ Eq_typ s1)
  | exp_tabs s0 s1 =>
      congr_exp_tabs (idSubst_typ sigma_typ Eq_typ s0)
        (idSubst_exp (up_typ_typ sigma_typ) (up_typ_exp sigma_exp)
           (upId_typ_typ _ Eq_typ) (upId_typ_exp _ Eq_exp) s1)
  end.

Lemma upExtRen_typ_exp (xi : nat -> nat) (zeta : nat -> nat)
  (Eq : forall x, xi x = zeta x) :
  forall x, upRen_typ_exp xi x = upRen_typ_exp zeta x.
Proof.
exact (fun n => Eq n).
Qed.

Lemma upExtRen_exp_typ (xi : nat -> nat) (zeta : nat -> nat)
  (Eq : forall x, xi x = zeta x) :
  forall x, upRen_exp_typ xi x = upRen_exp_typ zeta x.
Proof.
exact (fun n => Eq n).
Qed.

Lemma upExtRen_exp_exp (xi : nat -> nat) (zeta : nat -> nat)
  (Eq : forall x, xi x = zeta x) :
  forall x, upRen_exp_exp xi x = upRen_exp_exp zeta x.
Proof.
exact (fun n => match n with
                | S n' => ap shift (Eq n')
                | O => eq_refl
                end).
Qed.

Fixpoint extRen_exp (xi_typ : nat -> nat) (xi_exp : nat -> nat)
(zeta_typ : nat -> nat) (zeta_exp : nat -> nat)
(Eq_typ : forall x, xi_typ x = zeta_typ x)
(Eq_exp : forall x, xi_exp x = zeta_exp x) (s : exp) {struct s} :
ren_exp xi_typ xi_exp s = ren_exp zeta_typ zeta_exp s :=
  match s with
  | exp_var s0 => ap (exp_var) (Eq_exp s0)
  | exp_app s0 s1 =>
      congr_exp_app
        (extRen_exp xi_typ xi_exp zeta_typ zeta_exp Eq_typ Eq_exp s0)
        (extRen_exp xi_typ xi_exp zeta_typ zeta_exp Eq_typ Eq_exp s1)
  | exp_abs s0 s1 =>
      congr_exp_abs (extRen_typ xi_typ zeta_typ Eq_typ s0)
        (extRen_exp (upRen_exp_typ xi_typ) (upRen_exp_exp xi_exp)
           (upRen_exp_typ zeta_typ) (upRen_exp_exp zeta_exp)
           (upExtRen_exp_typ _ _ Eq_typ) (upExtRen_exp_exp _ _ Eq_exp) s1)
  | exp_tapp s0 s1 =>
      congr_exp_tapp
        (extRen_exp xi_typ xi_exp zeta_typ zeta_exp Eq_typ Eq_exp s0)
        (extRen_typ xi_typ zeta_typ Eq_typ s1)
  | exp_tabs s0 s1 =>
      congr_exp_tabs (extRen_typ xi_typ zeta_typ Eq_typ s0)
        (extRen_exp (upRen_typ_typ xi_typ) (upRen_typ_exp xi_exp)
           (upRen_typ_typ zeta_typ) (upRen_typ_exp zeta_exp)
           (upExtRen_typ_typ _ _ Eq_typ) (upExtRen_typ_exp _ _ Eq_exp) s1)
  end.

Lemma upExt_typ_exp (sigma : nat -> exp) (tau : nat -> exp)
  (Eq : forall x, sigma x = tau x) :
  forall x, up_typ_exp sigma x = up_typ_exp tau x.
Proof.
exact (fun n => ap (ren_exp shift id) (Eq n)).
Qed.

Lemma upExt_exp_typ (sigma : nat -> typ) (tau : nat -> typ)
  (Eq : forall x, sigma x = tau x) :
  forall x, up_exp_typ sigma x = up_exp_typ tau x.
Proof.
exact (fun n => ap (ren_typ id) (Eq n)).
Qed.

Lemma upExt_exp_exp (sigma : nat -> exp) (tau : nat -> exp)
  (Eq : forall x, sigma x = tau x) :
  forall x, up_exp_exp sigma x = up_exp_exp tau x.
Proof.
exact (fun n =>
       match n with
       | S n' => ap (ren_exp id shift) (Eq n')
       | O => eq_refl
       end).
Qed.

Fixpoint ext_exp (sigma_typ : nat -> typ) (sigma_exp : nat -> exp)
(tau_typ : nat -> typ) (tau_exp : nat -> exp)
(Eq_typ : forall x, sigma_typ x = tau_typ x)
(Eq_exp : forall x, sigma_exp x = tau_exp x) (s : exp) {struct s} :
subst_exp sigma_typ sigma_exp s = subst_exp tau_typ tau_exp s :=
  match s with
  | exp_var s0 => Eq_exp s0
  | exp_app s0 s1 =>
      congr_exp_app
        (ext_exp sigma_typ sigma_exp tau_typ tau_exp Eq_typ Eq_exp s0)
        (ext_exp sigma_typ sigma_exp tau_typ tau_exp Eq_typ Eq_exp s1)
  | exp_abs s0 s1 =>
      congr_exp_abs (ext_typ sigma_typ tau_typ Eq_typ s0)
        (ext_exp (up_exp_typ sigma_typ) (up_exp_exp sigma_exp)
           (up_exp_typ tau_typ) (up_exp_exp tau_exp)
           (upExt_exp_typ _ _ Eq_typ) (upExt_exp_exp _ _ Eq_exp) s1)
  | exp_tapp s0 s1 =>
      congr_exp_tapp
        (ext_exp sigma_typ sigma_exp tau_typ tau_exp Eq_typ Eq_exp s0)
        (ext_typ sigma_typ tau_typ Eq_typ s1)
  | exp_tabs s0 s1 =>
      congr_exp_tabs (ext_typ sigma_typ tau_typ Eq_typ s0)
        (ext_exp (up_typ_typ sigma_typ) (up_typ_exp sigma_exp)
           (up_typ_typ tau_typ) (up_typ_exp tau_exp)
           (upExt_typ_typ _ _ Eq_typ) (upExt_typ_exp _ _ Eq_exp) s1)
  end.

Lemma up_ren_ren_typ_exp (xi : nat -> nat) (zeta : nat -> nat)
  (rho : nat -> nat) (Eq : forall x, funcomp zeta xi x = rho x) :
  forall x,
  funcomp (upRen_typ_exp zeta) (upRen_typ_exp xi) x = upRen_typ_exp rho x.
Proof.
exact (Eq).
Qed.

Lemma up_ren_ren_exp_typ (xi : nat -> nat) (zeta : nat -> nat)
  (rho : nat -> nat) (Eq : forall x, funcomp zeta xi x = rho x) :
  forall x,
  funcomp (upRen_exp_typ zeta) (upRen_exp_typ xi) x = upRen_exp_typ rho x.
Proof.
exact (Eq).
Qed.

Lemma up_ren_ren_exp_exp (xi : nat -> nat) (zeta : nat -> nat)
  (rho : nat -> nat) (Eq : forall x, funcomp zeta xi x = rho x) :
  forall x,
  funcomp (upRen_exp_exp zeta) (upRen_exp_exp xi) x = upRen_exp_exp rho x.
Proof.
exact (up_ren_ren xi zeta rho Eq).
Qed.

Fixpoint compRenRen_exp (xi_typ : nat -> nat) (xi_exp : nat -> nat)
(zeta_typ : nat -> nat) (zeta_exp : nat -> nat) (rho_typ : nat -> nat)
(rho_exp : nat -> nat)
(Eq_typ : forall x, funcomp zeta_typ xi_typ x = rho_typ x)
(Eq_exp : forall x, funcomp zeta_exp xi_exp x = rho_exp x) (s : exp) {struct
 s} :
ren_exp zeta_typ zeta_exp (ren_exp xi_typ xi_exp s) =
ren_exp rho_typ rho_exp s :=
  match s with
  | exp_var s0 => ap (exp_var) (Eq_exp s0)
  | exp_app s0 s1 =>
      congr_exp_app
        (compRenRen_exp xi_typ xi_exp zeta_typ zeta_exp rho_typ rho_exp
           Eq_typ Eq_exp s0)
        (compRenRen_exp xi_typ xi_exp zeta_typ zeta_exp rho_typ rho_exp
           Eq_typ Eq_exp s1)
  | exp_abs s0 s1 =>
      congr_exp_abs (compRenRen_typ xi_typ zeta_typ rho_typ Eq_typ s0)
        (compRenRen_exp (upRen_exp_typ xi_typ) (upRen_exp_exp xi_exp)
           (upRen_exp_typ zeta_typ) (upRen_exp_exp zeta_exp)
           (upRen_exp_typ rho_typ) (upRen_exp_exp rho_exp) Eq_typ
           (up_ren_ren _ _ _ Eq_exp) s1)
  | exp_tapp s0 s1 =>
      congr_exp_tapp
        (compRenRen_exp xi_typ xi_exp zeta_typ zeta_exp rho_typ rho_exp
           Eq_typ Eq_exp s0)
        (compRenRen_typ xi_typ zeta_typ rho_typ Eq_typ s1)
  | exp_tabs s0 s1 =>
      congr_exp_tabs (compRenRen_typ xi_typ zeta_typ rho_typ Eq_typ s0)
        (compRenRen_exp (upRen_typ_typ xi_typ) (upRen_typ_exp xi_exp)
           (upRen_typ_typ zeta_typ) (upRen_typ_exp zeta_exp)
           (upRen_typ_typ rho_typ) (upRen_typ_exp rho_exp)
           (up_ren_ren _ _ _ Eq_typ) Eq_exp s1)
  end.

Lemma up_ren_subst_typ_exp (xi : nat -> nat) (tau : nat -> exp)
  (theta : nat -> exp) (Eq : forall x, funcomp tau xi x = theta x) :
  forall x,
  funcomp (up_typ_exp tau) (upRen_typ_exp xi) x = up_typ_exp theta x.
Proof.
exact (fun n => ap (ren_exp shift id) (Eq n)).
Qed.

Lemma up_ren_subst_exp_typ (xi : nat -> nat) (tau : nat -> typ)
  (theta : nat -> typ) (Eq : forall x, funcomp tau xi x = theta x) :
  forall x,
  funcomp (up_exp_typ tau) (upRen_exp_typ xi) x = up_exp_typ theta x.
Proof.
exact (fun n => ap (ren_typ id) (Eq n)).
Qed.

Lemma up_ren_subst_exp_exp (xi : nat -> nat) (tau : nat -> exp)
  (theta : nat -> exp) (Eq : forall x, funcomp tau xi x = theta x) :
  forall x,
  funcomp (up_exp_exp tau) (upRen_exp_exp xi) x = up_exp_exp theta x.
Proof.
exact (fun n =>
       match n with
       | S n' => ap (ren_exp id shift) (Eq n')
       | O => eq_refl
       end).
Qed.

Fixpoint compRenSubst_exp (xi_typ : nat -> nat) (xi_exp : nat -> nat)
(tau_typ : nat -> typ) (tau_exp : nat -> exp) (theta_typ : nat -> typ)
(theta_exp : nat -> exp)
(Eq_typ : forall x, funcomp tau_typ xi_typ x = theta_typ x)
(Eq_exp : forall x, funcomp tau_exp xi_exp x = theta_exp x) (s : exp) {struct
 s} :
subst_exp tau_typ tau_exp (ren_exp xi_typ xi_exp s) =
subst_exp theta_typ theta_exp s :=
  match s with
  | exp_var s0 => Eq_exp s0
  | exp_app s0 s1 =>
      congr_exp_app
        (compRenSubst_exp xi_typ xi_exp tau_typ tau_exp theta_typ theta_exp
           Eq_typ Eq_exp s0)
        (compRenSubst_exp xi_typ xi_exp tau_typ tau_exp theta_typ theta_exp
           Eq_typ Eq_exp s1)
  | exp_abs s0 s1 =>
      congr_exp_abs (compRenSubst_typ xi_typ tau_typ theta_typ Eq_typ s0)
        (compRenSubst_exp (upRen_exp_typ xi_typ) (upRen_exp_exp xi_exp)
           (up_exp_typ tau_typ) (up_exp_exp tau_exp) (up_exp_typ theta_typ)
           (up_exp_exp theta_exp) (up_ren_subst_exp_typ _ _ _ Eq_typ)
           (up_ren_subst_exp_exp _ _ _ Eq_exp) s1)
  | exp_tapp s0 s1 =>
      congr_exp_tapp
        (compRenSubst_exp xi_typ xi_exp tau_typ tau_exp theta_typ theta_exp
           Eq_typ Eq_exp s0)
        (compRenSubst_typ xi_typ tau_typ theta_typ Eq_typ s1)
  | exp_tabs s0 s1 =>
      congr_exp_tabs (compRenSubst_typ xi_typ tau_typ theta_typ Eq_typ s0)
        (compRenSubst_exp (upRen_typ_typ xi_typ) (upRen_typ_exp xi_exp)
           (up_typ_typ tau_typ) (up_typ_exp tau_exp) (up_typ_typ theta_typ)
           (up_typ_exp theta_exp) (up_ren_subst_typ_typ _ _ _ Eq_typ)
           (up_ren_subst_typ_exp _ _ _ Eq_exp) s1)
  end.

Lemma up_subst_ren_typ_exp (sigma : nat -> exp) (zeta_typ : nat -> nat)
  (zeta_exp : nat -> nat) (theta : nat -> exp)
  (Eq : forall x, funcomp (ren_exp zeta_typ zeta_exp) sigma x = theta x) :
  forall x,
  funcomp (ren_exp (upRen_typ_typ zeta_typ) (upRen_typ_exp zeta_exp))
    (up_typ_exp sigma) x = up_typ_exp theta x.
Proof.
exact (fun n =>
       eq_trans
         (compRenRen_exp shift id (upRen_typ_typ zeta_typ)
            (upRen_typ_exp zeta_exp) (funcomp shift zeta_typ)
            (funcomp id zeta_exp) (fun x => eq_refl) (fun x => eq_refl)
            (sigma n))
         (eq_trans
            (eq_sym
               (compRenRen_exp zeta_typ zeta_exp shift id
                  (funcomp shift zeta_typ) (funcomp id zeta_exp)
                  (fun x => eq_refl) (fun x => eq_refl) (sigma n)))
            (ap (ren_exp shift id) (Eq n)))).
Qed.

Lemma up_subst_ren_exp_typ (sigma : nat -> typ) (zeta_typ : nat -> nat)
  (theta : nat -> typ)
  (Eq : forall x, funcomp (ren_typ zeta_typ) sigma x = theta x) :
  forall x,
  funcomp (ren_typ (upRen_exp_typ zeta_typ)) (up_exp_typ sigma) x =
  up_exp_typ theta x.
Proof.
exact (fun n =>
       eq_trans
         (compRenRen_typ id (upRen_exp_typ zeta_typ) (funcomp id zeta_typ)
            (fun x => eq_refl) (sigma n))
         (eq_trans
            (eq_sym
               (compRenRen_typ zeta_typ id (funcomp id zeta_typ)
                  (fun x => eq_refl) (sigma n))) (ap (ren_typ id) (Eq n)))).
Qed.

Lemma up_subst_ren_exp_exp (sigma : nat -> exp) (zeta_typ : nat -> nat)
  (zeta_exp : nat -> nat) (theta : nat -> exp)
  (Eq : forall x, funcomp (ren_exp zeta_typ zeta_exp) sigma x = theta x) :
  forall x,
  funcomp (ren_exp (upRen_exp_typ zeta_typ) (upRen_exp_exp zeta_exp))
    (up_exp_exp sigma) x = up_exp_exp theta x.
Proof.
exact (fun n =>
       match n with
       | S n' =>
           eq_trans
             (compRenRen_exp id shift (upRen_exp_typ zeta_typ)
                (upRen_exp_exp zeta_exp) (funcomp id zeta_typ)
                (funcomp shift zeta_exp) (fun x => eq_refl)
                (fun x => eq_refl) (sigma n'))
             (eq_trans
                (eq_sym
                   (compRenRen_exp zeta_typ zeta_exp id shift
                      (funcomp id zeta_typ) (funcomp shift zeta_exp)
                      (fun x => eq_refl) (fun x => eq_refl) (sigma n')))
                (ap (ren_exp id shift) (Eq n')))
       | O => eq_refl
       end).
Qed.

Fixpoint compSubstRen_exp (sigma_typ : nat -> typ) (sigma_exp : nat -> exp)
(zeta_typ : nat -> nat) (zeta_exp : nat -> nat) (theta_typ : nat -> typ)
(theta_exp : nat -> exp)
(Eq_typ : forall x, funcomp (ren_typ zeta_typ) sigma_typ x = theta_typ x)
(Eq_exp : forall x,
          funcomp (ren_exp zeta_typ zeta_exp) sigma_exp x = theta_exp x)
(s : exp) {struct s} :
ren_exp zeta_typ zeta_exp (subst_exp sigma_typ sigma_exp s) =
subst_exp theta_typ theta_exp s :=
  match s with
  | exp_var s0 => Eq_exp s0
  | exp_app s0 s1 =>
      congr_exp_app
        (compSubstRen_exp sigma_typ sigma_exp zeta_typ zeta_exp theta_typ
           theta_exp Eq_typ Eq_exp s0)
        (compSubstRen_exp sigma_typ sigma_exp zeta_typ zeta_exp theta_typ
           theta_exp Eq_typ Eq_exp s1)
  | exp_abs s0 s1 =>
      congr_exp_abs (compSubstRen_typ sigma_typ zeta_typ theta_typ Eq_typ s0)
        (compSubstRen_exp (up_exp_typ sigma_typ) (up_exp_exp sigma_exp)
           (upRen_exp_typ zeta_typ) (upRen_exp_exp zeta_exp)
           (up_exp_typ theta_typ) (up_exp_exp theta_exp)
           (up_subst_ren_exp_typ _ _ _ Eq_typ)
           (up_subst_ren_exp_exp _ _ _ _ Eq_exp) s1)
  | exp_tapp s0 s1 =>
      congr_exp_tapp
        (compSubstRen_exp sigma_typ sigma_exp zeta_typ zeta_exp theta_typ
           theta_exp Eq_typ Eq_exp s0)
        (compSubstRen_typ sigma_typ zeta_typ theta_typ Eq_typ s1)
  | exp_tabs s0 s1 =>
      congr_exp_tabs
        (compSubstRen_typ sigma_typ zeta_typ theta_typ Eq_typ s0)
        (compSubstRen_exp (up_typ_typ sigma_typ) (up_typ_exp sigma_exp)
           (upRen_typ_typ zeta_typ) (upRen_typ_exp zeta_exp)
           (up_typ_typ theta_typ) (up_typ_exp theta_exp)
           (up_subst_ren_typ_typ _ _ _ Eq_typ)
           (up_subst_ren_typ_exp _ _ _ _ Eq_exp) s1)
  end.

Lemma up_subst_subst_typ_exp (sigma : nat -> exp) (tau_typ : nat -> typ)
  (tau_exp : nat -> exp) (theta : nat -> exp)
  (Eq : forall x, funcomp (subst_exp tau_typ tau_exp) sigma x = theta x) :
  forall x,
  funcomp (subst_exp (up_typ_typ tau_typ) (up_typ_exp tau_exp))
    (up_typ_exp sigma) x = up_typ_exp theta x.
Proof.
exact (fun n =>
       eq_trans
         (compRenSubst_exp shift id (up_typ_typ tau_typ) (up_typ_exp tau_exp)
            (funcomp (up_typ_typ tau_typ) shift)
            (funcomp (up_typ_exp tau_exp) id) (fun x => eq_refl)
            (fun x => eq_refl) (sigma n))
         (eq_trans
            (eq_sym
               (compSubstRen_exp tau_typ tau_exp shift id
                  (funcomp (ren_typ shift) tau_typ)
                  (funcomp (ren_exp shift id) tau_exp) (fun x => eq_refl)
                  (fun x => eq_refl) (sigma n)))
            (ap (ren_exp shift id) (Eq n)))).
Qed.

Lemma up_subst_subst_exp_typ (sigma : nat -> typ) (tau_typ : nat -> typ)
  (theta : nat -> typ)
  (Eq : forall x, funcomp (subst_typ tau_typ) sigma x = theta x) :
  forall x,
  funcomp (subst_typ (up_exp_typ tau_typ)) (up_exp_typ sigma) x =
  up_exp_typ theta x.
Proof.
exact (fun n =>
       eq_trans
         (compRenSubst_typ id (up_exp_typ tau_typ)
            (funcomp (up_exp_typ tau_typ) id) (fun x => eq_refl) (sigma n))
         (eq_trans
            (eq_sym
               (compSubstRen_typ tau_typ id (funcomp (ren_typ id) tau_typ)
                  (fun x => eq_refl) (sigma n))) (ap (ren_typ id) (Eq n)))).
Qed.

Lemma up_subst_subst_exp_exp (sigma : nat -> exp) (tau_typ : nat -> typ)
  (tau_exp : nat -> exp) (theta : nat -> exp)
  (Eq : forall x, funcomp (subst_exp tau_typ tau_exp) sigma x = theta x) :
  forall x,
  funcomp (subst_exp (up_exp_typ tau_typ) (up_exp_exp tau_exp))
    (up_exp_exp sigma) x = up_exp_exp theta x.
Proof.
exact (fun n =>
       match n with
       | S n' =>
           eq_trans
             (compRenSubst_exp id shift (up_exp_typ tau_typ)
                (up_exp_exp tau_exp) (funcomp (up_exp_typ tau_typ) id)
                (funcomp (up_exp_exp tau_exp) shift) (fun x => eq_refl)
                (fun x => eq_refl) (sigma n'))
             (eq_trans
                (eq_sym
                   (compSubstRen_exp tau_typ tau_exp id shift
                      (funcomp (ren_typ id) tau_typ)
                      (funcomp (ren_exp id shift) tau_exp) (fun x => eq_refl)
                      (fun x => eq_refl) (sigma n')))
                (ap (ren_exp id shift) (Eq n')))
       | O => eq_refl
       end).
Qed.

Fixpoint compSubstSubst_exp (sigma_typ : nat -> typ) (sigma_exp : nat -> exp)
(tau_typ : nat -> typ) (tau_exp : nat -> exp) (theta_typ : nat -> typ)
(theta_exp : nat -> exp)
(Eq_typ : forall x, funcomp (subst_typ tau_typ) sigma_typ x = theta_typ x)
(Eq_exp : forall x,
          funcomp (subst_exp tau_typ tau_exp) sigma_exp x = theta_exp x)
(s : exp) {struct s} :
subst_exp tau_typ tau_exp (subst_exp sigma_typ sigma_exp s) =
subst_exp theta_typ theta_exp s :=
  match s with
  | exp_var s0 => Eq_exp s0
  | exp_app s0 s1 =>
      congr_exp_app
        (compSubstSubst_exp sigma_typ sigma_exp tau_typ tau_exp theta_typ
           theta_exp Eq_typ Eq_exp s0)
        (compSubstSubst_exp sigma_typ sigma_exp tau_typ tau_exp theta_typ
           theta_exp Eq_typ Eq_exp s1)
  | exp_abs s0 s1 =>
      congr_exp_abs
        (compSubstSubst_typ sigma_typ tau_typ theta_typ Eq_typ s0)
        (compSubstSubst_exp (up_exp_typ sigma_typ) (up_exp_exp sigma_exp)
           (up_exp_typ tau_typ) (up_exp_exp tau_exp) (up_exp_typ theta_typ)
           (up_exp_exp theta_exp) (up_subst_subst_exp_typ _ _ _ Eq_typ)
           (up_subst_subst_exp_exp _ _ _ _ Eq_exp) s1)
  | exp_tapp s0 s1 =>
      congr_exp_tapp
        (compSubstSubst_exp sigma_typ sigma_exp tau_typ tau_exp theta_typ
           theta_exp Eq_typ Eq_exp s0)
        (compSubstSubst_typ sigma_typ tau_typ theta_typ Eq_typ s1)
  | exp_tabs s0 s1 =>
      congr_exp_tabs
        (compSubstSubst_typ sigma_typ tau_typ theta_typ Eq_typ s0)
        (compSubstSubst_exp (up_typ_typ sigma_typ) (up_typ_exp sigma_exp)
           (up_typ_typ tau_typ) (up_typ_exp tau_exp) (up_typ_typ theta_typ)
           (up_typ_exp theta_exp) (up_subst_subst_typ_typ _ _ _ Eq_typ)
           (up_subst_subst_typ_exp _ _ _ _ Eq_exp) s1)
  end.

Lemma renRen_exp (xi_typ : nat -> nat) (xi_exp : nat -> nat)
  (zeta_typ : nat -> nat) (zeta_exp : nat -> nat) (s : exp) :
  ren_exp zeta_typ zeta_exp (ren_exp xi_typ xi_exp s) =
  ren_exp (funcomp zeta_typ xi_typ) (funcomp zeta_exp xi_exp) s.
Proof.
exact (compRenRen_exp xi_typ xi_exp zeta_typ zeta_exp _ _ (fun n => eq_refl)
         (fun n => eq_refl) s).
Qed.

Lemma renRen'_exp_pointwise (xi_typ : nat -> nat) (xi_exp : nat -> nat)
  (zeta_typ : nat -> nat) (zeta_exp : nat -> nat) :
  pointwise_relation _ eq
    (funcomp (ren_exp zeta_typ zeta_exp) (ren_exp xi_typ xi_exp))
    (ren_exp (funcomp zeta_typ xi_typ) (funcomp zeta_exp xi_exp)).
Proof.
exact (fun s =>
       compRenRen_exp xi_typ xi_exp zeta_typ zeta_exp _ _ (fun n => eq_refl)
         (fun n => eq_refl) s).
Qed.

Lemma renSubst_exp (xi_typ : nat -> nat) (xi_exp : nat -> nat)
  (tau_typ : nat -> typ) (tau_exp : nat -> exp) (s : exp) :
  subst_exp tau_typ tau_exp (ren_exp xi_typ xi_exp s) =
  subst_exp (funcomp tau_typ xi_typ) (funcomp tau_exp xi_exp) s.
Proof.
exact (compRenSubst_exp xi_typ xi_exp tau_typ tau_exp _ _ (fun n => eq_refl)
         (fun n => eq_refl) s).
Qed.

Lemma renSubst_exp_pointwise (xi_typ : nat -> nat) (xi_exp : nat -> nat)
  (tau_typ : nat -> typ) (tau_exp : nat -> exp) :
  pointwise_relation _ eq
    (funcomp (subst_exp tau_typ tau_exp) (ren_exp xi_typ xi_exp))
    (subst_exp (funcomp tau_typ xi_typ) (funcomp tau_exp xi_exp)).
Proof.
exact (fun s =>
       compRenSubst_exp xi_typ xi_exp tau_typ tau_exp _ _ (fun n => eq_refl)
         (fun n => eq_refl) s).
Qed.

Lemma substRen_exp (sigma_typ : nat -> typ) (sigma_exp : nat -> exp)
  (zeta_typ : nat -> nat) (zeta_exp : nat -> nat) (s : exp) :
  ren_exp zeta_typ zeta_exp (subst_exp sigma_typ sigma_exp s) =
  subst_exp (funcomp (ren_typ zeta_typ) sigma_typ)
    (funcomp (ren_exp zeta_typ zeta_exp) sigma_exp) s.
Proof.
exact (compSubstRen_exp sigma_typ sigma_exp zeta_typ zeta_exp _ _
         (fun n => eq_refl) (fun n => eq_refl) s).
Qed.

Lemma substRen_exp_pointwise (sigma_typ : nat -> typ)
  (sigma_exp : nat -> exp) (zeta_typ : nat -> nat) (zeta_exp : nat -> nat) :
  pointwise_relation _ eq
    (funcomp (ren_exp zeta_typ zeta_exp) (subst_exp sigma_typ sigma_exp))
    (subst_exp (funcomp (ren_typ zeta_typ) sigma_typ)
       (funcomp (ren_exp zeta_typ zeta_exp) sigma_exp)).
Proof.
exact (fun s =>
       compSubstRen_exp sigma_typ sigma_exp zeta_typ zeta_exp _ _
         (fun n => eq_refl) (fun n => eq_refl) s).
Qed.

Lemma substSubst_exp (sigma_typ : nat -> typ) (sigma_exp : nat -> exp)
  (tau_typ : nat -> typ) (tau_exp : nat -> exp) (s : exp) :
  subst_exp tau_typ tau_exp (subst_exp sigma_typ sigma_exp s) =
  subst_exp (funcomp (subst_typ tau_typ) sigma_typ)
    (funcomp (subst_exp tau_typ tau_exp) sigma_exp) s.
Proof.
exact (compSubstSubst_exp sigma_typ sigma_exp tau_typ tau_exp _ _
         (fun n => eq_refl) (fun n => eq_refl) s).
Qed.

Lemma substSubst_exp_pointwise (sigma_typ : nat -> typ)
  (sigma_exp : nat -> exp) (tau_typ : nat -> typ) (tau_exp : nat -> exp) :
  pointwise_relation _ eq
    (funcomp (subst_exp tau_typ tau_exp) (subst_exp sigma_typ sigma_exp))
    (subst_exp (funcomp (subst_typ tau_typ) sigma_typ)
       (funcomp (subst_exp tau_typ tau_exp) sigma_exp)).
Proof.
exact (fun s =>
       compSubstSubst_exp sigma_typ sigma_exp tau_typ tau_exp _ _
         (fun n => eq_refl) (fun n => eq_refl) s).
Qed.

Lemma rinstInst_up_typ_exp (xi : nat -> nat) (sigma : nat -> exp)
  (Eq : forall x, funcomp (exp_var) xi x = sigma x) :
  forall x, funcomp (exp_var) (upRen_typ_exp xi) x = up_typ_exp sigma x.
Proof.
exact (fun n => ap (ren_exp shift id) (Eq n)).
Qed.

Lemma rinstInst_up_exp_typ (xi : nat -> nat) (sigma : nat -> typ)
  (Eq : forall x, funcomp (typ_var) xi x = sigma x) :
  forall x, funcomp (typ_var) (upRen_exp_typ xi) x = up_exp_typ sigma x.
Proof.
exact (fun n => ap (ren_typ id) (Eq n)).
Qed.

Lemma rinstInst_up_exp_exp (xi : nat -> nat) (sigma : nat -> exp)
  (Eq : forall x, funcomp (exp_var) xi x = sigma x) :
  forall x, funcomp (exp_var) (upRen_exp_exp xi) x = up_exp_exp sigma x.
Proof.
exact (fun n =>
       match n with
       | S n' => ap (ren_exp id shift) (Eq n')
       | O => eq_refl
       end).
Qed.

Fixpoint rinst_inst_exp (xi_typ : nat -> nat) (xi_exp : nat -> nat)
(sigma_typ : nat -> typ) (sigma_exp : nat -> exp)
(Eq_typ : forall x, funcomp (typ_var) xi_typ x = sigma_typ x)
(Eq_exp : forall x, funcomp (exp_var) xi_exp x = sigma_exp x) (s : exp)
{struct s} : ren_exp xi_typ xi_exp s = subst_exp sigma_typ sigma_exp s :=
  match s with
  | exp_var s0 => Eq_exp s0
  | exp_app s0 s1 =>
      congr_exp_app
        (rinst_inst_exp xi_typ xi_exp sigma_typ sigma_exp Eq_typ Eq_exp s0)
        (rinst_inst_exp xi_typ xi_exp sigma_typ sigma_exp Eq_typ Eq_exp s1)
  | exp_abs s0 s1 =>
      congr_exp_abs (rinst_inst_typ xi_typ sigma_typ Eq_typ s0)
        (rinst_inst_exp (upRen_exp_typ xi_typ) (upRen_exp_exp xi_exp)
           (up_exp_typ sigma_typ) (up_exp_exp sigma_exp)
           (rinstInst_up_exp_typ _ _ Eq_typ)
           (rinstInst_up_exp_exp _ _ Eq_exp) s1)
  | exp_tapp s0 s1 =>
      congr_exp_tapp
        (rinst_inst_exp xi_typ xi_exp sigma_typ sigma_exp Eq_typ Eq_exp s0)
        (rinst_inst_typ xi_typ sigma_typ Eq_typ s1)
  | exp_tabs s0 s1 =>
      congr_exp_tabs (rinst_inst_typ xi_typ sigma_typ Eq_typ s0)
        (rinst_inst_exp (upRen_typ_typ xi_typ) (upRen_typ_exp xi_exp)
           (up_typ_typ sigma_typ) (up_typ_exp sigma_exp)
           (rinstInst_up_typ_typ _ _ Eq_typ)
           (rinstInst_up_typ_exp _ _ Eq_exp) s1)
  end.

Lemma rinstInst'_exp (xi_typ : nat -> nat) (xi_exp : nat -> nat) (s : exp) :
  ren_exp xi_typ xi_exp s =
  subst_exp (funcomp (typ_var) xi_typ) (funcomp (exp_var) xi_exp) s.
Proof.
exact (rinst_inst_exp xi_typ xi_exp _ _ (fun n => eq_refl) (fun n => eq_refl)
         s).
Qed.

Lemma rinstInst'_exp_pointwise (xi_typ : nat -> nat) (xi_exp : nat -> nat) :
  pointwise_relation _ eq (ren_exp xi_typ xi_exp)
    (subst_exp (funcomp (typ_var) xi_typ) (funcomp (exp_var) xi_exp)).
Proof.
exact (fun s =>
       rinst_inst_exp xi_typ xi_exp _ _ (fun n => eq_refl) (fun n => eq_refl)
         s).
Qed.

Lemma instId'_exp (s : exp) : subst_exp (typ_var) (exp_var) s = s.
Proof.
exact (idSubst_exp (typ_var) (exp_var) (fun n => eq_refl) (fun n => eq_refl)
         s).
Qed.

Lemma instId'_exp_pointwise :
  pointwise_relation _ eq (subst_exp (typ_var) (exp_var)) id.
Proof.
exact (fun s =>
       idSubst_exp (typ_var) (exp_var) (fun n => eq_refl) (fun n => eq_refl)
         s).
Qed.

Lemma rinstId'_exp (s : exp) : ren_exp id id s = s.
Proof.
exact (eq_ind_r (fun t => t = s) (instId'_exp s) (rinstInst'_exp id id s)).
Qed.

Lemma rinstId'_exp_pointwise : pointwise_relation _ eq (@ren_exp id id) id.
Proof.
exact (fun s =>
       eq_ind_r (fun t => t = s) (instId'_exp s) (rinstInst'_exp id id s)).
Qed.

Lemma varL'_exp (sigma_typ : nat -> typ) (sigma_exp : nat -> exp) (x : nat) :
  subst_exp sigma_typ sigma_exp (exp_var x) = sigma_exp x.
Proof.
exact (eq_refl).
Qed.

Lemma varL'_exp_pointwise (sigma_typ : nat -> typ) (sigma_exp : nat -> exp) :
  pointwise_relation _ eq (funcomp (subst_exp sigma_typ sigma_exp) (exp_var))
    sigma_exp.
Proof.
exact (fun x => eq_refl).
Qed.

Lemma varLRen'_exp (xi_typ : nat -> nat) (xi_exp : nat -> nat) (x : nat) :
  ren_exp xi_typ xi_exp (exp_var x) = exp_var (xi_exp x).
Proof.
exact (eq_refl).
Qed.

Lemma varLRen'_exp_pointwise (xi_typ : nat -> nat) (xi_exp : nat -> nat) :
  pointwise_relation _ eq (funcomp (ren_exp xi_typ xi_exp) (exp_var))
    (funcomp (exp_var) xi_exp).
Proof.
exact (fun x => eq_refl).
Qed.

Class Up_exp X Y :=
    up_exp : X -> Y.

Class Up_typ X Y :=
    up_typ : X -> Y.

#[global]Instance Subst_exp : (Subst2 _ _ _ _) := @subst_exp.

#[global]Instance Up_exp_exp : (Up_exp _ _) := @up_exp_exp.

#[global]Instance Up_exp_typ : (Up_typ _ _) := @up_exp_typ.

#[global]Instance Up_typ_exp : (Up_exp _ _) := @up_typ_exp.

#[global]Instance Ren_exp : (Ren2 _ _ _ _) := @ren_exp.

#[global]Instance VarInstance_exp : (Var _ _) := @exp_var.

#[global]Instance Subst_typ : (Subst1 _ _ _) := @subst_typ.

#[global]Instance Up_typ_typ : (Up_typ _ _) := @up_typ_typ.

#[global]Instance Ren_typ : (Ren1 _ _ _) := @ren_typ.

#[global]
Instance VarInstance_typ : (Var _ _) := @typ_var.

Notation "[ sigma_typ ; sigma_exp ]" := (subst_exp sigma_typ sigma_exp)
( at level 1, left associativity, only printing)  : fscope.

Notation "s [ sigma_typ ; sigma_exp ]" := (subst_exp sigma_typ sigma_exp s)
( at level 7, left associativity, only printing)  : subst_scope.

Notation "↑__exp" := up_exp (only printing)  : subst_scope.

Notation "↑__exp" := up_exp_exp (only printing)  : subst_scope.

Notation "↑__typ" := up_exp_typ (only printing)  : subst_scope.

Notation "↑__exp" := up_typ_exp (only printing)  : subst_scope.

Notation "⟨ xi_typ ; xi_exp ⟩" := (ren_exp xi_typ xi_exp)
( at level 1, left associativity, only printing)  : fscope.

Notation "s ⟨ xi_typ ; xi_exp ⟩" := (ren_exp xi_typ xi_exp s)
( at level 7, left associativity, only printing)  : subst_scope.

Notation "'var'" := exp_var ( at level 1, only printing)  : subst_scope.

Notation "x '__exp'" := (@ids _ _ VarInstance_exp x)
( at level 5, format "x __exp", only printing)  : subst_scope.

Notation "x '__exp'" := (exp_var x) ( at level 5, format "x __exp")  :
subst_scope.

Notation "[ sigma_typ ]" := (subst_typ sigma_typ)
( at level 1, left associativity, only printing)  : fscope.

Notation "s [ sigma_typ ]" := (subst_typ sigma_typ s)
( at level 7, left associativity, only printing)  : subst_scope.

Notation "↑__typ" := up_typ (only printing)  : subst_scope.

Notation "↑__typ" := up_typ_typ (only printing)  : subst_scope.

Notation "⟨ xi_typ ⟩" := (ren_typ xi_typ)
( at level 1, left associativity, only printing)  : fscope.

Notation "s ⟨ xi_typ ⟩" := (ren_typ xi_typ s)
( at level 7, left associativity, only printing)  : subst_scope.

Notation "'var'" := typ_var ( at level 1, only printing)  : subst_scope.

Notation "x '__typ'" := (@ids _ _ VarInstance_typ x)
( at level 5, format "x __typ", only printing)  : subst_scope.

Notation "x '__typ'" := (typ_var x) ( at level 5, format "x __typ")  :
subst_scope.

#[global]
Instance subst_exp_morphism :
 (Proper
    (respectful (pointwise_relation _ eq)
       (respectful (pointwise_relation _ eq) (respectful eq eq)))
    (@subst_exp)).
Proof.
exact (fun f_typ g_typ Eq_typ f_exp g_exp Eq_exp s t Eq_st =>
       eq_ind s
         (fun t' => subst_exp f_typ f_exp s = subst_exp g_typ g_exp t')
         (ext_exp f_typ f_exp g_typ g_exp Eq_typ Eq_exp s) t Eq_st).
Qed.

#[global]
Instance subst_exp_morphism2 :
 (Proper
    (respectful (pointwise_relation _ eq)
       (respectful (pointwise_relation _ eq) (pointwise_relation _ eq)))
    (@subst_exp)).
Proof.
exact (fun f_typ g_typ Eq_typ f_exp g_exp Eq_exp s =>
       ext_exp f_typ f_exp g_typ g_exp Eq_typ Eq_exp s).
Qed.

#[global]
Instance ren_exp_morphism :
 (Proper
    (respectful (pointwise_relation _ eq)
       (respectful (pointwise_relation _ eq) (respectful eq eq))) (@ren_exp)).
Proof.
exact (fun f_typ g_typ Eq_typ f_exp g_exp Eq_exp s t Eq_st =>
       eq_ind s (fun t' => ren_exp f_typ f_exp s = ren_exp g_typ g_exp t')
         (extRen_exp f_typ f_exp g_typ g_exp Eq_typ Eq_exp s) t Eq_st).
Qed.

#[global]
Instance ren_exp_morphism2 :
 (Proper
    (respectful (pointwise_relation _ eq)
       (respectful (pointwise_relation _ eq) (pointwise_relation _ eq)))
    (@ren_exp)).
Proof.
exact (fun f_typ g_typ Eq_typ f_exp g_exp Eq_exp s =>
       extRen_exp f_typ f_exp g_typ g_exp Eq_typ Eq_exp s).
Qed.

#[global]
Instance subst_typ_morphism :
 (Proper (respectful (pointwise_relation _ eq) (respectful eq eq))
    (@subst_typ)).
Proof.
exact (fun f_typ g_typ Eq_typ s t Eq_st =>
       eq_ind s (fun t' => subst_typ f_typ s = subst_typ g_typ t')
         (ext_typ f_typ g_typ Eq_typ s) t Eq_st).
Qed.

#[global]
Instance subst_typ_morphism2 :
 (Proper (respectful (pointwise_relation _ eq) (pointwise_relation _ eq))
    (@subst_typ)).
Proof.
exact (fun f_typ g_typ Eq_typ s => ext_typ f_typ g_typ Eq_typ s).
Qed.

#[global]
Instance ren_typ_morphism :
 (Proper (respectful (pointwise_relation _ eq) (respectful eq eq)) (@ren_typ)).
Proof.
exact (fun f_typ g_typ Eq_typ s t Eq_st =>
       eq_ind s (fun t' => ren_typ f_typ s = ren_typ g_typ t')
         (extRen_typ f_typ g_typ Eq_typ s) t Eq_st).
Qed.

#[global]
Instance ren_typ_morphism2 :
 (Proper (respectful (pointwise_relation _ eq) (pointwise_relation _ eq))
    (@ren_typ)).
Proof.
exact (fun f_typ g_typ Eq_typ s => extRen_typ f_typ g_typ Eq_typ s).
Qed.

Ltac auto_unfold := repeat
                     unfold VarInstance_typ, Var, ids, Ren_typ, Ren1, ren1,
                      Up_typ_typ, Up_typ, up_typ, Subst_typ, Subst1, subst1,
                      VarInstance_exp, Var, ids, Ren_exp, Ren2, ren2,
                      Up_typ_exp, Up_exp, up_exp, Up_exp_typ, Up_typ, up_typ,
                      Up_exp_exp, Up_exp, up_exp, Subst_exp, Subst2, subst2.

Tactic Notation "auto_unfold" "in" "*" := repeat
                                           unfold VarInstance_typ, Var, ids,
                                            Ren_typ, Ren1, ren1, Up_typ_typ,
                                            Up_typ, up_typ, Subst_typ,
                                            Subst1, subst1, VarInstance_exp,
                                            Var, ids, Ren_exp, Ren2, ren2,
                                            Up_typ_exp, Up_exp, up_exp,
                                            Up_exp_typ, Up_typ, up_typ,
                                            Up_exp_exp, Up_exp, up_exp,
                                            Subst_exp, Subst2, subst2 
                                            in *.

Ltac asimpl' := repeat (first
                 [ progress setoid_rewrite substSubst_exp_pointwise
                 | progress setoid_rewrite substSubst_exp
                 | progress setoid_rewrite substRen_exp_pointwise
                 | progress setoid_rewrite substRen_exp
                 | progress setoid_rewrite renSubst_exp_pointwise
                 | progress setoid_rewrite renSubst_exp
                 | progress setoid_rewrite renRen'_exp_pointwise
                 | progress setoid_rewrite renRen_exp
                 | progress setoid_rewrite substSubst_typ_pointwise
                 | progress setoid_rewrite substSubst_typ
                 | progress setoid_rewrite substRen_typ_pointwise
                 | progress setoid_rewrite substRen_typ
                 | progress setoid_rewrite renSubst_typ_pointwise
                 | progress setoid_rewrite renSubst_typ
                 | progress setoid_rewrite renRen'_typ_pointwise
                 | progress setoid_rewrite renRen_typ
                 | progress setoid_rewrite varLRen'_exp_pointwise
                 | progress setoid_rewrite varLRen'_exp
                 | progress setoid_rewrite varL'_exp_pointwise
                 | progress setoid_rewrite varL'_exp
                 | progress setoid_rewrite rinstId'_exp_pointwise
                 | progress setoid_rewrite rinstId'_exp
                 | progress setoid_rewrite instId'_exp_pointwise
                 | progress setoid_rewrite instId'_exp
                 | progress setoid_rewrite varLRen'_typ_pointwise
                 | progress setoid_rewrite varLRen'_typ
                 | progress setoid_rewrite varL'_typ_pointwise
                 | progress setoid_rewrite varL'_typ
                 | progress setoid_rewrite rinstId'_typ_pointwise
                 | progress setoid_rewrite rinstId'_typ
                 | progress setoid_rewrite instId'_typ_pointwise
                 | progress setoid_rewrite instId'_typ
                 | progress
                    unfold up_exp_exp, up_exp_typ, up_typ_exp, upRen_exp_exp,
                     upRen_exp_typ, upRen_typ_exp, up_typ_typ, upRen_typ_typ,
                     up_ren
                 | progress cbn[subst_exp ren_exp subst_typ ren_typ]
                 | progress fsimpl ]).

Ltac asimpl := check_no_evars;
                repeat
                 unfold VarInstance_typ, Var, ids, Ren_typ, Ren1, ren1,
                  Up_typ_typ, Up_typ, up_typ, Subst_typ, Subst1, subst1,
                  VarInstance_exp, Var, ids, Ren_exp, Ren2, ren2, Up_typ_exp,
                  Up_exp, up_exp, Up_exp_typ, Up_typ, up_typ, Up_exp_exp,
                  Up_exp, up_exp, Subst_exp, Subst2, subst2 in *; asimpl';
                minimize.

Tactic Notation "asimpl" "in" hyp(J) := revert J; asimpl; intros J.

Tactic Notation "auto_case" := auto_case ltac:(asimpl; cbn; eauto).

Ltac substify := auto_unfold; try setoid_rewrite rinstInst'_exp_pointwise;
                  try setoid_rewrite rinstInst'_exp;
                  try setoid_rewrite rinstInst'_typ_pointwise;
                  try setoid_rewrite rinstInst'_typ.

Ltac renamify := auto_unfold;
                  try setoid_rewrite_left rinstInst'_exp_pointwise;
                  try setoid_rewrite_left rinstInst'_exp;
                  try setoid_rewrite_left rinstInst'_typ_pointwise;
                  try setoid_rewrite_left rinstInst'_typ.

End Core.

Module Extra.

Import Core.

#[global]Hint Opaque subst_exp: rewrite.

#[global]Hint Opaque ren_exp: rewrite.

#[global]Hint Opaque subst_typ: rewrite.

#[global]Hint Opaque ren_typ: rewrite.

End Extra.

Module interface.

Export Core.

Export Extra.

End interface.

Export interface.

