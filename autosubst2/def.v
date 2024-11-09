Require Import binder.autosubst2.prop_as_core binder.autosubst2.prop_as_unscoped.

Require Import Setoid Morphisms Relation_Definitions.


Module Core.

Inductive ftyp : Type :=
  | ftyp_var : nat -> ftyp
  | ftyp_arr : ftyp -> ftyp -> ftyp
  | ftyp_all : ftyp -> ftyp.

Lemma congr_ftyp_arr {s0 : ftyp} {s1 : ftyp} {t0 : ftyp} {t1 : ftyp}
  (H0 : s0 = t0) (H1 : s1 = t1) : ftyp_arr s0 s1 = ftyp_arr t0 t1.
Proof.
exact (eq_trans (eq_trans eq_refl (ap (fun x => ftyp_arr x s1) H0))
         (ap (fun x => ftyp_arr t0 x) H1)).
Qed.

Lemma congr_ftyp_all {s0 : ftyp} {t0 : ftyp} (H0 : s0 = t0) :
  ftyp_all s0 = ftyp_all t0.
Proof.
exact (eq_trans eq_refl (ap (fun x => ftyp_all x) H0)).
Qed.

Lemma upRen_ftyp_ftyp (xi : nat -> nat) : nat -> nat.
Proof.
exact (up_ren xi).
Defined.

Fixpoint ren_ftyp (xi_ftyp : nat -> nat) (s : ftyp) {struct s} : ftyp :=
  match s with
  | ftyp_var s0 => ftyp_var (xi_ftyp s0)
  | ftyp_arr s0 s1 => ftyp_arr (ren_ftyp xi_ftyp s0) (ren_ftyp xi_ftyp s1)
  | ftyp_all s0 => ftyp_all (ren_ftyp (upRen_ftyp_ftyp xi_ftyp) s0)
  end.

Lemma up_ftyp_ftyp (sigma : nat -> ftyp) : nat -> ftyp.
Proof.
exact (scons (ftyp_var var_zero) (funcomp (ren_ftyp shift) sigma)).
Defined.

Fixpoint subst_ftyp (sigma_ftyp : nat -> ftyp) (s : ftyp) {struct s} : 
ftyp :=
  match s with
  | ftyp_var s0 => sigma_ftyp s0
  | ftyp_arr s0 s1 =>
      ftyp_arr (subst_ftyp sigma_ftyp s0) (subst_ftyp sigma_ftyp s1)
  | ftyp_all s0 => ftyp_all (subst_ftyp (up_ftyp_ftyp sigma_ftyp) s0)
  end.

Lemma upId_ftyp_ftyp (sigma : nat -> ftyp)
  (Eq : forall x, sigma x = ftyp_var x) :
  forall x, up_ftyp_ftyp sigma x = ftyp_var x.
Proof.
exact (fun n =>
       match n with
       | S n' => ap (ren_ftyp shift) (Eq n')
       | O => eq_refl
       end).
Qed.

Fixpoint idSubst_ftyp (sigma_ftyp : nat -> ftyp)
(Eq_ftyp : forall x, sigma_ftyp x = ftyp_var x) (s : ftyp) {struct s} :
subst_ftyp sigma_ftyp s = s :=
  match s with
  | ftyp_var s0 => Eq_ftyp s0
  | ftyp_arr s0 s1 =>
      congr_ftyp_arr (idSubst_ftyp sigma_ftyp Eq_ftyp s0)
        (idSubst_ftyp sigma_ftyp Eq_ftyp s1)
  | ftyp_all s0 =>
      congr_ftyp_all
        (idSubst_ftyp (up_ftyp_ftyp sigma_ftyp) (upId_ftyp_ftyp _ Eq_ftyp) s0)
  end.

Lemma upExtRen_ftyp_ftyp (xi : nat -> nat) (zeta : nat -> nat)
  (Eq : forall x, xi x = zeta x) :
  forall x, upRen_ftyp_ftyp xi x = upRen_ftyp_ftyp zeta x.
Proof.
exact (fun n => match n with
                | S n' => ap shift (Eq n')
                | O => eq_refl
                end).
Qed.

Fixpoint extRen_ftyp (xi_ftyp : nat -> nat) (zeta_ftyp : nat -> nat)
(Eq_ftyp : forall x, xi_ftyp x = zeta_ftyp x) (s : ftyp) {struct s} :
ren_ftyp xi_ftyp s = ren_ftyp zeta_ftyp s :=
  match s with
  | ftyp_var s0 => ap (ftyp_var) (Eq_ftyp s0)
  | ftyp_arr s0 s1 =>
      congr_ftyp_arr (extRen_ftyp xi_ftyp zeta_ftyp Eq_ftyp s0)
        (extRen_ftyp xi_ftyp zeta_ftyp Eq_ftyp s1)
  | ftyp_all s0 =>
      congr_ftyp_all
        (extRen_ftyp (upRen_ftyp_ftyp xi_ftyp) (upRen_ftyp_ftyp zeta_ftyp)
           (upExtRen_ftyp_ftyp _ _ Eq_ftyp) s0)
  end.

Lemma upExt_ftyp_ftyp (sigma : nat -> ftyp) (tau : nat -> ftyp)
  (Eq : forall x, sigma x = tau x) :
  forall x, up_ftyp_ftyp sigma x = up_ftyp_ftyp tau x.
Proof.
exact (fun n =>
       match n with
       | S n' => ap (ren_ftyp shift) (Eq n')
       | O => eq_refl
       end).
Qed.

Fixpoint ext_ftyp (sigma_ftyp : nat -> ftyp) (tau_ftyp : nat -> ftyp)
(Eq_ftyp : forall x, sigma_ftyp x = tau_ftyp x) (s : ftyp) {struct s} :
subst_ftyp sigma_ftyp s = subst_ftyp tau_ftyp s :=
  match s with
  | ftyp_var s0 => Eq_ftyp s0
  | ftyp_arr s0 s1 =>
      congr_ftyp_arr (ext_ftyp sigma_ftyp tau_ftyp Eq_ftyp s0)
        (ext_ftyp sigma_ftyp tau_ftyp Eq_ftyp s1)
  | ftyp_all s0 =>
      congr_ftyp_all
        (ext_ftyp (up_ftyp_ftyp sigma_ftyp) (up_ftyp_ftyp tau_ftyp)
           (upExt_ftyp_ftyp _ _ Eq_ftyp) s0)
  end.

Lemma up_ren_ren_ftyp_ftyp (xi : nat -> nat) (zeta : nat -> nat)
  (rho : nat -> nat) (Eq : forall x, funcomp zeta xi x = rho x) :
  forall x,
  funcomp (upRen_ftyp_ftyp zeta) (upRen_ftyp_ftyp xi) x =
  upRen_ftyp_ftyp rho x.
Proof.
exact (up_ren_ren xi zeta rho Eq).
Qed.

Fixpoint compRenRen_ftyp (xi_ftyp : nat -> nat) (zeta_ftyp : nat -> nat)
(rho_ftyp : nat -> nat)
(Eq_ftyp : forall x, funcomp zeta_ftyp xi_ftyp x = rho_ftyp x) (s : ftyp)
{struct s} : ren_ftyp zeta_ftyp (ren_ftyp xi_ftyp s) = ren_ftyp rho_ftyp s :=
  match s with
  | ftyp_var s0 => ap (ftyp_var) (Eq_ftyp s0)
  | ftyp_arr s0 s1 =>
      congr_ftyp_arr (compRenRen_ftyp xi_ftyp zeta_ftyp rho_ftyp Eq_ftyp s0)
        (compRenRen_ftyp xi_ftyp zeta_ftyp rho_ftyp Eq_ftyp s1)
  | ftyp_all s0 =>
      congr_ftyp_all
        (compRenRen_ftyp (upRen_ftyp_ftyp xi_ftyp)
           (upRen_ftyp_ftyp zeta_ftyp) (upRen_ftyp_ftyp rho_ftyp)
           (up_ren_ren _ _ _ Eq_ftyp) s0)
  end.

Lemma up_ren_subst_ftyp_ftyp (xi : nat -> nat) (tau : nat -> ftyp)
  (theta : nat -> ftyp) (Eq : forall x, funcomp tau xi x = theta x) :
  forall x,
  funcomp (up_ftyp_ftyp tau) (upRen_ftyp_ftyp xi) x = up_ftyp_ftyp theta x.
Proof.
exact (fun n =>
       match n with
       | S n' => ap (ren_ftyp shift) (Eq n')
       | O => eq_refl
       end).
Qed.

Fixpoint compRenSubst_ftyp (xi_ftyp : nat -> nat) (tau_ftyp : nat -> ftyp)
(theta_ftyp : nat -> ftyp)
(Eq_ftyp : forall x, funcomp tau_ftyp xi_ftyp x = theta_ftyp x) (s : ftyp)
{struct s} :
subst_ftyp tau_ftyp (ren_ftyp xi_ftyp s) = subst_ftyp theta_ftyp s :=
  match s with
  | ftyp_var s0 => Eq_ftyp s0
  | ftyp_arr s0 s1 =>
      congr_ftyp_arr
        (compRenSubst_ftyp xi_ftyp tau_ftyp theta_ftyp Eq_ftyp s0)
        (compRenSubst_ftyp xi_ftyp tau_ftyp theta_ftyp Eq_ftyp s1)
  | ftyp_all s0 =>
      congr_ftyp_all
        (compRenSubst_ftyp (upRen_ftyp_ftyp xi_ftyp) (up_ftyp_ftyp tau_ftyp)
           (up_ftyp_ftyp theta_ftyp) (up_ren_subst_ftyp_ftyp _ _ _ Eq_ftyp)
           s0)
  end.

Lemma up_subst_ren_ftyp_ftyp (sigma : nat -> ftyp) (zeta_ftyp : nat -> nat)
  (theta : nat -> ftyp)
  (Eq : forall x, funcomp (ren_ftyp zeta_ftyp) sigma x = theta x) :
  forall x,
  funcomp (ren_ftyp (upRen_ftyp_ftyp zeta_ftyp)) (up_ftyp_ftyp sigma) x =
  up_ftyp_ftyp theta x.
Proof.
exact (fun n =>
       match n with
       | S n' =>
           eq_trans
             (compRenRen_ftyp shift (upRen_ftyp_ftyp zeta_ftyp)
                (funcomp shift zeta_ftyp) (fun x => eq_refl) (sigma n'))
             (eq_trans
                (eq_sym
                   (compRenRen_ftyp zeta_ftyp shift (funcomp shift zeta_ftyp)
                      (fun x => eq_refl) (sigma n')))
                (ap (ren_ftyp shift) (Eq n')))
       | O => eq_refl
       end).
Qed.

Fixpoint compSubstRen_ftyp (sigma_ftyp : nat -> ftyp)
(zeta_ftyp : nat -> nat) (theta_ftyp : nat -> ftyp)
(Eq_ftyp : forall x, funcomp (ren_ftyp zeta_ftyp) sigma_ftyp x = theta_ftyp x)
(s : ftyp) {struct s} :
ren_ftyp zeta_ftyp (subst_ftyp sigma_ftyp s) = subst_ftyp theta_ftyp s :=
  match s with
  | ftyp_var s0 => Eq_ftyp s0
  | ftyp_arr s0 s1 =>
      congr_ftyp_arr
        (compSubstRen_ftyp sigma_ftyp zeta_ftyp theta_ftyp Eq_ftyp s0)
        (compSubstRen_ftyp sigma_ftyp zeta_ftyp theta_ftyp Eq_ftyp s1)
  | ftyp_all s0 =>
      congr_ftyp_all
        (compSubstRen_ftyp (up_ftyp_ftyp sigma_ftyp)
           (upRen_ftyp_ftyp zeta_ftyp) (up_ftyp_ftyp theta_ftyp)
           (up_subst_ren_ftyp_ftyp _ _ _ Eq_ftyp) s0)
  end.

Lemma up_subst_subst_ftyp_ftyp (sigma : nat -> ftyp) (tau_ftyp : nat -> ftyp)
  (theta : nat -> ftyp)
  (Eq : forall x, funcomp (subst_ftyp tau_ftyp) sigma x = theta x) :
  forall x,
  funcomp (subst_ftyp (up_ftyp_ftyp tau_ftyp)) (up_ftyp_ftyp sigma) x =
  up_ftyp_ftyp theta x.
Proof.
exact (fun n =>
       match n with
       | S n' =>
           eq_trans
             (compRenSubst_ftyp shift (up_ftyp_ftyp tau_ftyp)
                (funcomp (up_ftyp_ftyp tau_ftyp) shift) (fun x => eq_refl)
                (sigma n'))
             (eq_trans
                (eq_sym
                   (compSubstRen_ftyp tau_ftyp shift
                      (funcomp (ren_ftyp shift) tau_ftyp) (fun x => eq_refl)
                      (sigma n'))) (ap (ren_ftyp shift) (Eq n')))
       | O => eq_refl
       end).
Qed.

Fixpoint compSubstSubst_ftyp (sigma_ftyp : nat -> ftyp)
(tau_ftyp : nat -> ftyp) (theta_ftyp : nat -> ftyp)
(Eq_ftyp : forall x,
           funcomp (subst_ftyp tau_ftyp) sigma_ftyp x = theta_ftyp x)
(s : ftyp) {struct s} :
subst_ftyp tau_ftyp (subst_ftyp sigma_ftyp s) = subst_ftyp theta_ftyp s :=
  match s with
  | ftyp_var s0 => Eq_ftyp s0
  | ftyp_arr s0 s1 =>
      congr_ftyp_arr
        (compSubstSubst_ftyp sigma_ftyp tau_ftyp theta_ftyp Eq_ftyp s0)
        (compSubstSubst_ftyp sigma_ftyp tau_ftyp theta_ftyp Eq_ftyp s1)
  | ftyp_all s0 =>
      congr_ftyp_all
        (compSubstSubst_ftyp (up_ftyp_ftyp sigma_ftyp)
           (up_ftyp_ftyp tau_ftyp) (up_ftyp_ftyp theta_ftyp)
           (up_subst_subst_ftyp_ftyp _ _ _ Eq_ftyp) s0)
  end.

Lemma renRen_ftyp (xi_ftyp : nat -> nat) (zeta_ftyp : nat -> nat) (s : ftyp)
  :
  ren_ftyp zeta_ftyp (ren_ftyp xi_ftyp s) =
  ren_ftyp (funcomp zeta_ftyp xi_ftyp) s.
Proof.
exact (compRenRen_ftyp xi_ftyp zeta_ftyp _ (fun n => eq_refl) s).
Qed.

Lemma renRen'_ftyp_pointwise (xi_ftyp : nat -> nat) (zeta_ftyp : nat -> nat)
  :
  pointwise_relation _ eq (funcomp (ren_ftyp zeta_ftyp) (ren_ftyp xi_ftyp))
    (ren_ftyp (funcomp zeta_ftyp xi_ftyp)).
Proof.
exact (fun s => compRenRen_ftyp xi_ftyp zeta_ftyp _ (fun n => eq_refl) s).
Qed.

Lemma renSubst_ftyp (xi_ftyp : nat -> nat) (tau_ftyp : nat -> ftyp)
  (s : ftyp) :
  subst_ftyp tau_ftyp (ren_ftyp xi_ftyp s) =
  subst_ftyp (funcomp tau_ftyp xi_ftyp) s.
Proof.
exact (compRenSubst_ftyp xi_ftyp tau_ftyp _ (fun n => eq_refl) s).
Qed.

Lemma renSubst_ftyp_pointwise (xi_ftyp : nat -> nat) (tau_ftyp : nat -> ftyp)
  :
  pointwise_relation _ eq (funcomp (subst_ftyp tau_ftyp) (ren_ftyp xi_ftyp))
    (subst_ftyp (funcomp tau_ftyp xi_ftyp)).
Proof.
exact (fun s => compRenSubst_ftyp xi_ftyp tau_ftyp _ (fun n => eq_refl) s).
Qed.

Lemma substRen_ftyp (sigma_ftyp : nat -> ftyp) (zeta_ftyp : nat -> nat)
  (s : ftyp) :
  ren_ftyp zeta_ftyp (subst_ftyp sigma_ftyp s) =
  subst_ftyp (funcomp (ren_ftyp zeta_ftyp) sigma_ftyp) s.
Proof.
exact (compSubstRen_ftyp sigma_ftyp zeta_ftyp _ (fun n => eq_refl) s).
Qed.

Lemma substRen_ftyp_pointwise (sigma_ftyp : nat -> ftyp)
  (zeta_ftyp : nat -> nat) :
  pointwise_relation _ eq
    (funcomp (ren_ftyp zeta_ftyp) (subst_ftyp sigma_ftyp))
    (subst_ftyp (funcomp (ren_ftyp zeta_ftyp) sigma_ftyp)).
Proof.
exact (fun s => compSubstRen_ftyp sigma_ftyp zeta_ftyp _ (fun n => eq_refl) s).
Qed.

Lemma substSubst_ftyp (sigma_ftyp : nat -> ftyp) (tau_ftyp : nat -> ftyp)
  (s : ftyp) :
  subst_ftyp tau_ftyp (subst_ftyp sigma_ftyp s) =
  subst_ftyp (funcomp (subst_ftyp tau_ftyp) sigma_ftyp) s.
Proof.
exact (compSubstSubst_ftyp sigma_ftyp tau_ftyp _ (fun n => eq_refl) s).
Qed.

Lemma substSubst_ftyp_pointwise (sigma_ftyp : nat -> ftyp)
  (tau_ftyp : nat -> ftyp) :
  pointwise_relation _ eq
    (funcomp (subst_ftyp tau_ftyp) (subst_ftyp sigma_ftyp))
    (subst_ftyp (funcomp (subst_ftyp tau_ftyp) sigma_ftyp)).
Proof.
exact (fun s =>
       compSubstSubst_ftyp sigma_ftyp tau_ftyp _ (fun n => eq_refl) s).
Qed.

Lemma rinstInst_up_ftyp_ftyp (xi : nat -> nat) (sigma : nat -> ftyp)
  (Eq : forall x, funcomp (ftyp_var) xi x = sigma x) :
  forall x, funcomp (ftyp_var) (upRen_ftyp_ftyp xi) x = up_ftyp_ftyp sigma x.
Proof.
exact (fun n =>
       match n with
       | S n' => ap (ren_ftyp shift) (Eq n')
       | O => eq_refl
       end).
Qed.

Fixpoint rinst_inst_ftyp (xi_ftyp : nat -> nat) (sigma_ftyp : nat -> ftyp)
(Eq_ftyp : forall x, funcomp (ftyp_var) xi_ftyp x = sigma_ftyp x) (s : ftyp)
{struct s} : ren_ftyp xi_ftyp s = subst_ftyp sigma_ftyp s :=
  match s with
  | ftyp_var s0 => Eq_ftyp s0
  | ftyp_arr s0 s1 =>
      congr_ftyp_arr (rinst_inst_ftyp xi_ftyp sigma_ftyp Eq_ftyp s0)
        (rinst_inst_ftyp xi_ftyp sigma_ftyp Eq_ftyp s1)
  | ftyp_all s0 =>
      congr_ftyp_all
        (rinst_inst_ftyp (upRen_ftyp_ftyp xi_ftyp) (up_ftyp_ftyp sigma_ftyp)
           (rinstInst_up_ftyp_ftyp _ _ Eq_ftyp) s0)
  end.

Lemma rinstInst'_ftyp (xi_ftyp : nat -> nat) (s : ftyp) :
  ren_ftyp xi_ftyp s = subst_ftyp (funcomp (ftyp_var) xi_ftyp) s.
Proof.
exact (rinst_inst_ftyp xi_ftyp _ (fun n => eq_refl) s).
Qed.

Lemma rinstInst'_ftyp_pointwise (xi_ftyp : nat -> nat) :
  pointwise_relation _ eq (ren_ftyp xi_ftyp)
    (subst_ftyp (funcomp (ftyp_var) xi_ftyp)).
Proof.
exact (fun s => rinst_inst_ftyp xi_ftyp _ (fun n => eq_refl) s).
Qed.

Lemma instId'_ftyp (s : ftyp) : subst_ftyp (ftyp_var) s = s.
Proof.
exact (idSubst_ftyp (ftyp_var) (fun n => eq_refl) s).
Qed.

Lemma instId'_ftyp_pointwise :
  pointwise_relation _ eq (subst_ftyp (ftyp_var)) id.
Proof.
exact (fun s => idSubst_ftyp (ftyp_var) (fun n => eq_refl) s).
Qed.

Lemma rinstId'_ftyp (s : ftyp) : ren_ftyp id s = s.
Proof.
exact (eq_ind_r (fun t => t = s) (instId'_ftyp s) (rinstInst'_ftyp id s)).
Qed.

Lemma rinstId'_ftyp_pointwise : pointwise_relation _ eq (@ren_ftyp id) id.
Proof.
exact (fun s =>
       eq_ind_r (fun t => t = s) (instId'_ftyp s) (rinstInst'_ftyp id s)).
Qed.

Lemma varL'_ftyp (sigma_ftyp : nat -> ftyp) (x : nat) :
  subst_ftyp sigma_ftyp (ftyp_var x) = sigma_ftyp x.
Proof.
exact (eq_refl).
Qed.

Lemma varL'_ftyp_pointwise (sigma_ftyp : nat -> ftyp) :
  pointwise_relation _ eq (funcomp (subst_ftyp sigma_ftyp) (ftyp_var))
    sigma_ftyp.
Proof.
exact (fun x => eq_refl).
Qed.

Lemma varLRen'_ftyp (xi_ftyp : nat -> nat) (x : nat) :
  ren_ftyp xi_ftyp (ftyp_var x) = ftyp_var (xi_ftyp x).
Proof.
exact (eq_refl).
Qed.

Lemma varLRen'_ftyp_pointwise (xi_ftyp : nat -> nat) :
  pointwise_relation _ eq (funcomp (ren_ftyp xi_ftyp) (ftyp_var))
    (funcomp (ftyp_var) xi_ftyp).
Proof.
exact (fun x => eq_refl).
Qed.

Inductive fexp : Type :=
  | fexp_var : nat -> fexp
  | fexp_app : fexp -> fexp -> fexp
  | fexp_abs : ftyp -> fexp -> fexp
  | fexp_tapp : fexp -> ftyp -> fexp
  | fexp_tabs : fexp -> fexp.

Lemma congr_fexp_app {s0 : fexp} {s1 : fexp} {t0 : fexp} {t1 : fexp}
  (H0 : s0 = t0) (H1 : s1 = t1) : fexp_app s0 s1 = fexp_app t0 t1.
Proof.
exact (eq_trans (eq_trans eq_refl (ap (fun x => fexp_app x s1) H0))
         (ap (fun x => fexp_app t0 x) H1)).
Qed.

Lemma congr_fexp_abs {s0 : ftyp} {s1 : fexp} {t0 : ftyp} {t1 : fexp}
  (H0 : s0 = t0) (H1 : s1 = t1) : fexp_abs s0 s1 = fexp_abs t0 t1.
Proof.
exact (eq_trans (eq_trans eq_refl (ap (fun x => fexp_abs x s1) H0))
         (ap (fun x => fexp_abs t0 x) H1)).
Qed.

Lemma congr_fexp_tapp {s0 : fexp} {s1 : ftyp} {t0 : fexp} {t1 : ftyp}
  (H0 : s0 = t0) (H1 : s1 = t1) : fexp_tapp s0 s1 = fexp_tapp t0 t1.
Proof.
exact (eq_trans (eq_trans eq_refl (ap (fun x => fexp_tapp x s1) H0))
         (ap (fun x => fexp_tapp t0 x) H1)).
Qed.

Lemma congr_fexp_tabs {s0 : fexp} {t0 : fexp} (H0 : s0 = t0) :
  fexp_tabs s0 = fexp_tabs t0.
Proof.
exact (eq_trans eq_refl (ap (fun x => fexp_tabs x) H0)).
Qed.

Lemma upRen_ftyp_fexp (xi : nat -> nat) : nat -> nat.
Proof.
exact (xi).
Defined.

Lemma upRen_fexp_ftyp (xi : nat -> nat) : nat -> nat.
Proof.
exact (xi).
Defined.

Lemma upRen_fexp_fexp (xi : nat -> nat) : nat -> nat.
Proof.
exact (up_ren xi).
Defined.

Fixpoint ren_fexp (xi_ftyp : nat -> nat) (xi_fexp : nat -> nat) (s : fexp)
{struct s} : fexp :=
  match s with
  | fexp_var s0 => fexp_var (xi_fexp s0)
  | fexp_app s0 s1 =>
      fexp_app (ren_fexp xi_ftyp xi_fexp s0) (ren_fexp xi_ftyp xi_fexp s1)
  | fexp_abs s0 s1 =>
      fexp_abs (ren_ftyp xi_ftyp s0)
        (ren_fexp (upRen_fexp_ftyp xi_ftyp) (upRen_fexp_fexp xi_fexp) s1)
  | fexp_tapp s0 s1 =>
      fexp_tapp (ren_fexp xi_ftyp xi_fexp s0) (ren_ftyp xi_ftyp s1)
  | fexp_tabs s0 =>
      fexp_tabs
        (ren_fexp (upRen_ftyp_ftyp xi_ftyp) (upRen_ftyp_fexp xi_fexp) s0)
  end.

Lemma up_ftyp_fexp (sigma : nat -> fexp) : nat -> fexp.
Proof.
exact (funcomp (ren_fexp shift id) sigma).
Defined.

Lemma up_fexp_ftyp (sigma : nat -> ftyp) : nat -> ftyp.
Proof.
exact (funcomp (ren_ftyp id) sigma).
Defined.

Lemma up_fexp_fexp (sigma : nat -> fexp) : nat -> fexp.
Proof.
exact (scons (fexp_var var_zero) (funcomp (ren_fexp id shift) sigma)).
Defined.

Fixpoint subst_fexp (sigma_ftyp : nat -> ftyp) (sigma_fexp : nat -> fexp)
(s : fexp) {struct s} : fexp :=
  match s with
  | fexp_var s0 => sigma_fexp s0
  | fexp_app s0 s1 =>
      fexp_app (subst_fexp sigma_ftyp sigma_fexp s0)
        (subst_fexp sigma_ftyp sigma_fexp s1)
  | fexp_abs s0 s1 =>
      fexp_abs (subst_ftyp sigma_ftyp s0)
        (subst_fexp (up_fexp_ftyp sigma_ftyp) (up_fexp_fexp sigma_fexp) s1)
  | fexp_tapp s0 s1 =>
      fexp_tapp (subst_fexp sigma_ftyp sigma_fexp s0)
        (subst_ftyp sigma_ftyp s1)
  | fexp_tabs s0 =>
      fexp_tabs
        (subst_fexp (up_ftyp_ftyp sigma_ftyp) (up_ftyp_fexp sigma_fexp) s0)
  end.

Lemma upId_ftyp_fexp (sigma : nat -> fexp)
  (Eq : forall x, sigma x = fexp_var x) :
  forall x, up_ftyp_fexp sigma x = fexp_var x.
Proof.
exact (fun n => ap (ren_fexp shift id) (Eq n)).
Qed.

Lemma upId_fexp_ftyp (sigma : nat -> ftyp)
  (Eq : forall x, sigma x = ftyp_var x) :
  forall x, up_fexp_ftyp sigma x = ftyp_var x.
Proof.
exact (fun n => ap (ren_ftyp id) (Eq n)).
Qed.

Lemma upId_fexp_fexp (sigma : nat -> fexp)
  (Eq : forall x, sigma x = fexp_var x) :
  forall x, up_fexp_fexp sigma x = fexp_var x.
Proof.
exact (fun n =>
       match n with
       | S n' => ap (ren_fexp id shift) (Eq n')
       | O => eq_refl
       end).
Qed.

Fixpoint idSubst_fexp (sigma_ftyp : nat -> ftyp) (sigma_fexp : nat -> fexp)
(Eq_ftyp : forall x, sigma_ftyp x = ftyp_var x)
(Eq_fexp : forall x, sigma_fexp x = fexp_var x) (s : fexp) {struct s} :
subst_fexp sigma_ftyp sigma_fexp s = s :=
  match s with
  | fexp_var s0 => Eq_fexp s0
  | fexp_app s0 s1 =>
      congr_fexp_app (idSubst_fexp sigma_ftyp sigma_fexp Eq_ftyp Eq_fexp s0)
        (idSubst_fexp sigma_ftyp sigma_fexp Eq_ftyp Eq_fexp s1)
  | fexp_abs s0 s1 =>
      congr_fexp_abs (idSubst_ftyp sigma_ftyp Eq_ftyp s0)
        (idSubst_fexp (up_fexp_ftyp sigma_ftyp) (up_fexp_fexp sigma_fexp)
           (upId_fexp_ftyp _ Eq_ftyp) (upId_fexp_fexp _ Eq_fexp) s1)
  | fexp_tapp s0 s1 =>
      congr_fexp_tapp (idSubst_fexp sigma_ftyp sigma_fexp Eq_ftyp Eq_fexp s0)
        (idSubst_ftyp sigma_ftyp Eq_ftyp s1)
  | fexp_tabs s0 =>
      congr_fexp_tabs
        (idSubst_fexp (up_ftyp_ftyp sigma_ftyp) (up_ftyp_fexp sigma_fexp)
           (upId_ftyp_ftyp _ Eq_ftyp) (upId_ftyp_fexp _ Eq_fexp) s0)
  end.

Lemma upExtRen_ftyp_fexp (xi : nat -> nat) (zeta : nat -> nat)
  (Eq : forall x, xi x = zeta x) :
  forall x, upRen_ftyp_fexp xi x = upRen_ftyp_fexp zeta x.
Proof.
exact (fun n => Eq n).
Qed.

Lemma upExtRen_fexp_ftyp (xi : nat -> nat) (zeta : nat -> nat)
  (Eq : forall x, xi x = zeta x) :
  forall x, upRen_fexp_ftyp xi x = upRen_fexp_ftyp zeta x.
Proof.
exact (fun n => Eq n).
Qed.

Lemma upExtRen_fexp_fexp (xi : nat -> nat) (zeta : nat -> nat)
  (Eq : forall x, xi x = zeta x) :
  forall x, upRen_fexp_fexp xi x = upRen_fexp_fexp zeta x.
Proof.
exact (fun n => match n with
                | S n' => ap shift (Eq n')
                | O => eq_refl
                end).
Qed.

Fixpoint extRen_fexp (xi_ftyp : nat -> nat) (xi_fexp : nat -> nat)
(zeta_ftyp : nat -> nat) (zeta_fexp : nat -> nat)
(Eq_ftyp : forall x, xi_ftyp x = zeta_ftyp x)
(Eq_fexp : forall x, xi_fexp x = zeta_fexp x) (s : fexp) {struct s} :
ren_fexp xi_ftyp xi_fexp s = ren_fexp zeta_ftyp zeta_fexp s :=
  match s with
  | fexp_var s0 => ap (fexp_var) (Eq_fexp s0)
  | fexp_app s0 s1 =>
      congr_fexp_app
        (extRen_fexp xi_ftyp xi_fexp zeta_ftyp zeta_fexp Eq_ftyp Eq_fexp s0)
        (extRen_fexp xi_ftyp xi_fexp zeta_ftyp zeta_fexp Eq_ftyp Eq_fexp s1)
  | fexp_abs s0 s1 =>
      congr_fexp_abs (extRen_ftyp xi_ftyp zeta_ftyp Eq_ftyp s0)
        (extRen_fexp (upRen_fexp_ftyp xi_ftyp) (upRen_fexp_fexp xi_fexp)
           (upRen_fexp_ftyp zeta_ftyp) (upRen_fexp_fexp zeta_fexp)
           (upExtRen_fexp_ftyp _ _ Eq_ftyp) (upExtRen_fexp_fexp _ _ Eq_fexp)
           s1)
  | fexp_tapp s0 s1 =>
      congr_fexp_tapp
        (extRen_fexp xi_ftyp xi_fexp zeta_ftyp zeta_fexp Eq_ftyp Eq_fexp s0)
        (extRen_ftyp xi_ftyp zeta_ftyp Eq_ftyp s1)
  | fexp_tabs s0 =>
      congr_fexp_tabs
        (extRen_fexp (upRen_ftyp_ftyp xi_ftyp) (upRen_ftyp_fexp xi_fexp)
           (upRen_ftyp_ftyp zeta_ftyp) (upRen_ftyp_fexp zeta_fexp)
           (upExtRen_ftyp_ftyp _ _ Eq_ftyp) (upExtRen_ftyp_fexp _ _ Eq_fexp)
           s0)
  end.

Lemma upExt_ftyp_fexp (sigma : nat -> fexp) (tau : nat -> fexp)
  (Eq : forall x, sigma x = tau x) :
  forall x, up_ftyp_fexp sigma x = up_ftyp_fexp tau x.
Proof.
exact (fun n => ap (ren_fexp shift id) (Eq n)).
Qed.

Lemma upExt_fexp_ftyp (sigma : nat -> ftyp) (tau : nat -> ftyp)
  (Eq : forall x, sigma x = tau x) :
  forall x, up_fexp_ftyp sigma x = up_fexp_ftyp tau x.
Proof.
exact (fun n => ap (ren_ftyp id) (Eq n)).
Qed.

Lemma upExt_fexp_fexp (sigma : nat -> fexp) (tau : nat -> fexp)
  (Eq : forall x, sigma x = tau x) :
  forall x, up_fexp_fexp sigma x = up_fexp_fexp tau x.
Proof.
exact (fun n =>
       match n with
       | S n' => ap (ren_fexp id shift) (Eq n')
       | O => eq_refl
       end).
Qed.

Fixpoint ext_fexp (sigma_ftyp : nat -> ftyp) (sigma_fexp : nat -> fexp)
(tau_ftyp : nat -> ftyp) (tau_fexp : nat -> fexp)
(Eq_ftyp : forall x, sigma_ftyp x = tau_ftyp x)
(Eq_fexp : forall x, sigma_fexp x = tau_fexp x) (s : fexp) {struct s} :
subst_fexp sigma_ftyp sigma_fexp s = subst_fexp tau_ftyp tau_fexp s :=
  match s with
  | fexp_var s0 => Eq_fexp s0
  | fexp_app s0 s1 =>
      congr_fexp_app
        (ext_fexp sigma_ftyp sigma_fexp tau_ftyp tau_fexp Eq_ftyp Eq_fexp s0)
        (ext_fexp sigma_ftyp sigma_fexp tau_ftyp tau_fexp Eq_ftyp Eq_fexp s1)
  | fexp_abs s0 s1 =>
      congr_fexp_abs (ext_ftyp sigma_ftyp tau_ftyp Eq_ftyp s0)
        (ext_fexp (up_fexp_ftyp sigma_ftyp) (up_fexp_fexp sigma_fexp)
           (up_fexp_ftyp tau_ftyp) (up_fexp_fexp tau_fexp)
           (upExt_fexp_ftyp _ _ Eq_ftyp) (upExt_fexp_fexp _ _ Eq_fexp) s1)
  | fexp_tapp s0 s1 =>
      congr_fexp_tapp
        (ext_fexp sigma_ftyp sigma_fexp tau_ftyp tau_fexp Eq_ftyp Eq_fexp s0)
        (ext_ftyp sigma_ftyp tau_ftyp Eq_ftyp s1)
  | fexp_tabs s0 =>
      congr_fexp_tabs
        (ext_fexp (up_ftyp_ftyp sigma_ftyp) (up_ftyp_fexp sigma_fexp)
           (up_ftyp_ftyp tau_ftyp) (up_ftyp_fexp tau_fexp)
           (upExt_ftyp_ftyp _ _ Eq_ftyp) (upExt_ftyp_fexp _ _ Eq_fexp) s0)
  end.

Lemma up_ren_ren_ftyp_fexp (xi : nat -> nat) (zeta : nat -> nat)
  (rho : nat -> nat) (Eq : forall x, funcomp zeta xi x = rho x) :
  forall x,
  funcomp (upRen_ftyp_fexp zeta) (upRen_ftyp_fexp xi) x =
  upRen_ftyp_fexp rho x.
Proof.
exact (Eq).
Qed.

Lemma up_ren_ren_fexp_ftyp (xi : nat -> nat) (zeta : nat -> nat)
  (rho : nat -> nat) (Eq : forall x, funcomp zeta xi x = rho x) :
  forall x,
  funcomp (upRen_fexp_ftyp zeta) (upRen_fexp_ftyp xi) x =
  upRen_fexp_ftyp rho x.
Proof.
exact (Eq).
Qed.

Lemma up_ren_ren_fexp_fexp (xi : nat -> nat) (zeta : nat -> nat)
  (rho : nat -> nat) (Eq : forall x, funcomp zeta xi x = rho x) :
  forall x,
  funcomp (upRen_fexp_fexp zeta) (upRen_fexp_fexp xi) x =
  upRen_fexp_fexp rho x.
Proof.
exact (up_ren_ren xi zeta rho Eq).
Qed.

Fixpoint compRenRen_fexp (xi_ftyp : nat -> nat) (xi_fexp : nat -> nat)
(zeta_ftyp : nat -> nat) (zeta_fexp : nat -> nat) (rho_ftyp : nat -> nat)
(rho_fexp : nat -> nat)
(Eq_ftyp : forall x, funcomp zeta_ftyp xi_ftyp x = rho_ftyp x)
(Eq_fexp : forall x, funcomp zeta_fexp xi_fexp x = rho_fexp x) (s : fexp)
{struct s} :
ren_fexp zeta_ftyp zeta_fexp (ren_fexp xi_ftyp xi_fexp s) =
ren_fexp rho_ftyp rho_fexp s :=
  match s with
  | fexp_var s0 => ap (fexp_var) (Eq_fexp s0)
  | fexp_app s0 s1 =>
      congr_fexp_app
        (compRenRen_fexp xi_ftyp xi_fexp zeta_ftyp zeta_fexp rho_ftyp
           rho_fexp Eq_ftyp Eq_fexp s0)
        (compRenRen_fexp xi_ftyp xi_fexp zeta_ftyp zeta_fexp rho_ftyp
           rho_fexp Eq_ftyp Eq_fexp s1)
  | fexp_abs s0 s1 =>
      congr_fexp_abs (compRenRen_ftyp xi_ftyp zeta_ftyp rho_ftyp Eq_ftyp s0)
        (compRenRen_fexp (upRen_fexp_ftyp xi_ftyp) (upRen_fexp_fexp xi_fexp)
           (upRen_fexp_ftyp zeta_ftyp) (upRen_fexp_fexp zeta_fexp)
           (upRen_fexp_ftyp rho_ftyp) (upRen_fexp_fexp rho_fexp) Eq_ftyp
           (up_ren_ren _ _ _ Eq_fexp) s1)
  | fexp_tapp s0 s1 =>
      congr_fexp_tapp
        (compRenRen_fexp xi_ftyp xi_fexp zeta_ftyp zeta_fexp rho_ftyp
           rho_fexp Eq_ftyp Eq_fexp s0)
        (compRenRen_ftyp xi_ftyp zeta_ftyp rho_ftyp Eq_ftyp s1)
  | fexp_tabs s0 =>
      congr_fexp_tabs
        (compRenRen_fexp (upRen_ftyp_ftyp xi_ftyp) (upRen_ftyp_fexp xi_fexp)
           (upRen_ftyp_ftyp zeta_ftyp) (upRen_ftyp_fexp zeta_fexp)
           (upRen_ftyp_ftyp rho_ftyp) (upRen_ftyp_fexp rho_fexp)
           (up_ren_ren _ _ _ Eq_ftyp) Eq_fexp s0)
  end.

Lemma up_ren_subst_ftyp_fexp (xi : nat -> nat) (tau : nat -> fexp)
  (theta : nat -> fexp) (Eq : forall x, funcomp tau xi x = theta x) :
  forall x,
  funcomp (up_ftyp_fexp tau) (upRen_ftyp_fexp xi) x = up_ftyp_fexp theta x.
Proof.
exact (fun n => ap (ren_fexp shift id) (Eq n)).
Qed.

Lemma up_ren_subst_fexp_ftyp (xi : nat -> nat) (tau : nat -> ftyp)
  (theta : nat -> ftyp) (Eq : forall x, funcomp tau xi x = theta x) :
  forall x,
  funcomp (up_fexp_ftyp tau) (upRen_fexp_ftyp xi) x = up_fexp_ftyp theta x.
Proof.
exact (fun n => ap (ren_ftyp id) (Eq n)).
Qed.

Lemma up_ren_subst_fexp_fexp (xi : nat -> nat) (tau : nat -> fexp)
  (theta : nat -> fexp) (Eq : forall x, funcomp tau xi x = theta x) :
  forall x,
  funcomp (up_fexp_fexp tau) (upRen_fexp_fexp xi) x = up_fexp_fexp theta x.
Proof.
exact (fun n =>
       match n with
       | S n' => ap (ren_fexp id shift) (Eq n')
       | O => eq_refl
       end).
Qed.

Fixpoint compRenSubst_fexp (xi_ftyp : nat -> nat) (xi_fexp : nat -> nat)
(tau_ftyp : nat -> ftyp) (tau_fexp : nat -> fexp) (theta_ftyp : nat -> ftyp)
(theta_fexp : nat -> fexp)
(Eq_ftyp : forall x, funcomp tau_ftyp xi_ftyp x = theta_ftyp x)
(Eq_fexp : forall x, funcomp tau_fexp xi_fexp x = theta_fexp x) (s : fexp)
{struct s} :
subst_fexp tau_ftyp tau_fexp (ren_fexp xi_ftyp xi_fexp s) =
subst_fexp theta_ftyp theta_fexp s :=
  match s with
  | fexp_var s0 => Eq_fexp s0
  | fexp_app s0 s1 =>
      congr_fexp_app
        (compRenSubst_fexp xi_ftyp xi_fexp tau_ftyp tau_fexp theta_ftyp
           theta_fexp Eq_ftyp Eq_fexp s0)
        (compRenSubst_fexp xi_ftyp xi_fexp tau_ftyp tau_fexp theta_ftyp
           theta_fexp Eq_ftyp Eq_fexp s1)
  | fexp_abs s0 s1 =>
      congr_fexp_abs
        (compRenSubst_ftyp xi_ftyp tau_ftyp theta_ftyp Eq_ftyp s0)
        (compRenSubst_fexp (upRen_fexp_ftyp xi_ftyp)
           (upRen_fexp_fexp xi_fexp) (up_fexp_ftyp tau_ftyp)
           (up_fexp_fexp tau_fexp) (up_fexp_ftyp theta_ftyp)
           (up_fexp_fexp theta_fexp) (up_ren_subst_fexp_ftyp _ _ _ Eq_ftyp)
           (up_ren_subst_fexp_fexp _ _ _ Eq_fexp) s1)
  | fexp_tapp s0 s1 =>
      congr_fexp_tapp
        (compRenSubst_fexp xi_ftyp xi_fexp tau_ftyp tau_fexp theta_ftyp
           theta_fexp Eq_ftyp Eq_fexp s0)
        (compRenSubst_ftyp xi_ftyp tau_ftyp theta_ftyp Eq_ftyp s1)
  | fexp_tabs s0 =>
      congr_fexp_tabs
        (compRenSubst_fexp (upRen_ftyp_ftyp xi_ftyp)
           (upRen_ftyp_fexp xi_fexp) (up_ftyp_ftyp tau_ftyp)
           (up_ftyp_fexp tau_fexp) (up_ftyp_ftyp theta_ftyp)
           (up_ftyp_fexp theta_fexp) (up_ren_subst_ftyp_ftyp _ _ _ Eq_ftyp)
           (up_ren_subst_ftyp_fexp _ _ _ Eq_fexp) s0)
  end.

Lemma up_subst_ren_ftyp_fexp (sigma : nat -> fexp) (zeta_ftyp : nat -> nat)
  (zeta_fexp : nat -> nat) (theta : nat -> fexp)
  (Eq : forall x, funcomp (ren_fexp zeta_ftyp zeta_fexp) sigma x = theta x) :
  forall x,
  funcomp (ren_fexp (upRen_ftyp_ftyp zeta_ftyp) (upRen_ftyp_fexp zeta_fexp))
    (up_ftyp_fexp sigma) x = up_ftyp_fexp theta x.
Proof.
exact (fun n =>
       eq_trans
         (compRenRen_fexp shift id (upRen_ftyp_ftyp zeta_ftyp)
            (upRen_ftyp_fexp zeta_fexp) (funcomp shift zeta_ftyp)
            (funcomp id zeta_fexp) (fun x => eq_refl) (fun x => eq_refl)
            (sigma n))
         (eq_trans
            (eq_sym
               (compRenRen_fexp zeta_ftyp zeta_fexp shift id
                  (funcomp shift zeta_ftyp) (funcomp id zeta_fexp)
                  (fun x => eq_refl) (fun x => eq_refl) (sigma n)))
            (ap (ren_fexp shift id) (Eq n)))).
Qed.

Lemma up_subst_ren_fexp_ftyp (sigma : nat -> ftyp) (zeta_ftyp : nat -> nat)
  (theta : nat -> ftyp)
  (Eq : forall x, funcomp (ren_ftyp zeta_ftyp) sigma x = theta x) :
  forall x,
  funcomp (ren_ftyp (upRen_fexp_ftyp zeta_ftyp)) (up_fexp_ftyp sigma) x =
  up_fexp_ftyp theta x.
Proof.
exact (fun n =>
       eq_trans
         (compRenRen_ftyp id (upRen_fexp_ftyp zeta_ftyp)
            (funcomp id zeta_ftyp) (fun x => eq_refl) (sigma n))
         (eq_trans
            (eq_sym
               (compRenRen_ftyp zeta_ftyp id (funcomp id zeta_ftyp)
                  (fun x => eq_refl) (sigma n))) (ap (ren_ftyp id) (Eq n)))).
Qed.

Lemma up_subst_ren_fexp_fexp (sigma : nat -> fexp) (zeta_ftyp : nat -> nat)
  (zeta_fexp : nat -> nat) (theta : nat -> fexp)
  (Eq : forall x, funcomp (ren_fexp zeta_ftyp zeta_fexp) sigma x = theta x) :
  forall x,
  funcomp (ren_fexp (upRen_fexp_ftyp zeta_ftyp) (upRen_fexp_fexp zeta_fexp))
    (up_fexp_fexp sigma) x = up_fexp_fexp theta x.
Proof.
exact (fun n =>
       match n with
       | S n' =>
           eq_trans
             (compRenRen_fexp id shift (upRen_fexp_ftyp zeta_ftyp)
                (upRen_fexp_fexp zeta_fexp) (funcomp id zeta_ftyp)
                (funcomp shift zeta_fexp) (fun x => eq_refl)
                (fun x => eq_refl) (sigma n'))
             (eq_trans
                (eq_sym
                   (compRenRen_fexp zeta_ftyp zeta_fexp id shift
                      (funcomp id zeta_ftyp) (funcomp shift zeta_fexp)
                      (fun x => eq_refl) (fun x => eq_refl) (sigma n')))
                (ap (ren_fexp id shift) (Eq n')))
       | O => eq_refl
       end).
Qed.

Fixpoint compSubstRen_fexp (sigma_ftyp : nat -> ftyp)
(sigma_fexp : nat -> fexp) (zeta_ftyp : nat -> nat) (zeta_fexp : nat -> nat)
(theta_ftyp : nat -> ftyp) (theta_fexp : nat -> fexp)
(Eq_ftyp : forall x, funcomp (ren_ftyp zeta_ftyp) sigma_ftyp x = theta_ftyp x)
(Eq_fexp : forall x,
           funcomp (ren_fexp zeta_ftyp zeta_fexp) sigma_fexp x = theta_fexp x)
(s : fexp) {struct s} :
ren_fexp zeta_ftyp zeta_fexp (subst_fexp sigma_ftyp sigma_fexp s) =
subst_fexp theta_ftyp theta_fexp s :=
  match s with
  | fexp_var s0 => Eq_fexp s0
  | fexp_app s0 s1 =>
      congr_fexp_app
        (compSubstRen_fexp sigma_ftyp sigma_fexp zeta_ftyp zeta_fexp
           theta_ftyp theta_fexp Eq_ftyp Eq_fexp s0)
        (compSubstRen_fexp sigma_ftyp sigma_fexp zeta_ftyp zeta_fexp
           theta_ftyp theta_fexp Eq_ftyp Eq_fexp s1)
  | fexp_abs s0 s1 =>
      congr_fexp_abs
        (compSubstRen_ftyp sigma_ftyp zeta_ftyp theta_ftyp Eq_ftyp s0)
        (compSubstRen_fexp (up_fexp_ftyp sigma_ftyp)
           (up_fexp_fexp sigma_fexp) (upRen_fexp_ftyp zeta_ftyp)
           (upRen_fexp_fexp zeta_fexp) (up_fexp_ftyp theta_ftyp)
           (up_fexp_fexp theta_fexp) (up_subst_ren_fexp_ftyp _ _ _ Eq_ftyp)
           (up_subst_ren_fexp_fexp _ _ _ _ Eq_fexp) s1)
  | fexp_tapp s0 s1 =>
      congr_fexp_tapp
        (compSubstRen_fexp sigma_ftyp sigma_fexp zeta_ftyp zeta_fexp
           theta_ftyp theta_fexp Eq_ftyp Eq_fexp s0)
        (compSubstRen_ftyp sigma_ftyp zeta_ftyp theta_ftyp Eq_ftyp s1)
  | fexp_tabs s0 =>
      congr_fexp_tabs
        (compSubstRen_fexp (up_ftyp_ftyp sigma_ftyp)
           (up_ftyp_fexp sigma_fexp) (upRen_ftyp_ftyp zeta_ftyp)
           (upRen_ftyp_fexp zeta_fexp) (up_ftyp_ftyp theta_ftyp)
           (up_ftyp_fexp theta_fexp) (up_subst_ren_ftyp_ftyp _ _ _ Eq_ftyp)
           (up_subst_ren_ftyp_fexp _ _ _ _ Eq_fexp) s0)
  end.

Lemma up_subst_subst_ftyp_fexp (sigma : nat -> fexp) (tau_ftyp : nat -> ftyp)
  (tau_fexp : nat -> fexp) (theta : nat -> fexp)
  (Eq : forall x, funcomp (subst_fexp tau_ftyp tau_fexp) sigma x = theta x) :
  forall x,
  funcomp (subst_fexp (up_ftyp_ftyp tau_ftyp) (up_ftyp_fexp tau_fexp))
    (up_ftyp_fexp sigma) x = up_ftyp_fexp theta x.
Proof.
exact (fun n =>
       eq_trans
         (compRenSubst_fexp shift id (up_ftyp_ftyp tau_ftyp)
            (up_ftyp_fexp tau_fexp) (funcomp (up_ftyp_ftyp tau_ftyp) shift)
            (funcomp (up_ftyp_fexp tau_fexp) id) (fun x => eq_refl)
            (fun x => eq_refl) (sigma n))
         (eq_trans
            (eq_sym
               (compSubstRen_fexp tau_ftyp tau_fexp shift id
                  (funcomp (ren_ftyp shift) tau_ftyp)
                  (funcomp (ren_fexp shift id) tau_fexp) (fun x => eq_refl)
                  (fun x => eq_refl) (sigma n)))
            (ap (ren_fexp shift id) (Eq n)))).
Qed.

Lemma up_subst_subst_fexp_ftyp (sigma : nat -> ftyp) (tau_ftyp : nat -> ftyp)
  (theta : nat -> ftyp)
  (Eq : forall x, funcomp (subst_ftyp tau_ftyp) sigma x = theta x) :
  forall x,
  funcomp (subst_ftyp (up_fexp_ftyp tau_ftyp)) (up_fexp_ftyp sigma) x =
  up_fexp_ftyp theta x.
Proof.
exact (fun n =>
       eq_trans
         (compRenSubst_ftyp id (up_fexp_ftyp tau_ftyp)
            (funcomp (up_fexp_ftyp tau_ftyp) id) (fun x => eq_refl) (sigma n))
         (eq_trans
            (eq_sym
               (compSubstRen_ftyp tau_ftyp id
                  (funcomp (ren_ftyp id) tau_ftyp) (fun x => eq_refl)
                  (sigma n))) (ap (ren_ftyp id) (Eq n)))).
Qed.

Lemma up_subst_subst_fexp_fexp (sigma : nat -> fexp) (tau_ftyp : nat -> ftyp)
  (tau_fexp : nat -> fexp) (theta : nat -> fexp)
  (Eq : forall x, funcomp (subst_fexp tau_ftyp tau_fexp) sigma x = theta x) :
  forall x,
  funcomp (subst_fexp (up_fexp_ftyp tau_ftyp) (up_fexp_fexp tau_fexp))
    (up_fexp_fexp sigma) x = up_fexp_fexp theta x.
Proof.
exact (fun n =>
       match n with
       | S n' =>
           eq_trans
             (compRenSubst_fexp id shift (up_fexp_ftyp tau_ftyp)
                (up_fexp_fexp tau_fexp) (funcomp (up_fexp_ftyp tau_ftyp) id)
                (funcomp (up_fexp_fexp tau_fexp) shift) (fun x => eq_refl)
                (fun x => eq_refl) (sigma n'))
             (eq_trans
                (eq_sym
                   (compSubstRen_fexp tau_ftyp tau_fexp id shift
                      (funcomp (ren_ftyp id) tau_ftyp)
                      (funcomp (ren_fexp id shift) tau_fexp)
                      (fun x => eq_refl) (fun x => eq_refl) (sigma n')))
                (ap (ren_fexp id shift) (Eq n')))
       | O => eq_refl
       end).
Qed.

Fixpoint compSubstSubst_fexp (sigma_ftyp : nat -> ftyp)
(sigma_fexp : nat -> fexp) (tau_ftyp : nat -> ftyp) (tau_fexp : nat -> fexp)
(theta_ftyp : nat -> ftyp) (theta_fexp : nat -> fexp)
(Eq_ftyp : forall x,
           funcomp (subst_ftyp tau_ftyp) sigma_ftyp x = theta_ftyp x)
(Eq_fexp : forall x,
           funcomp (subst_fexp tau_ftyp tau_fexp) sigma_fexp x = theta_fexp x)
(s : fexp) {struct s} :
subst_fexp tau_ftyp tau_fexp (subst_fexp sigma_ftyp sigma_fexp s) =
subst_fexp theta_ftyp theta_fexp s :=
  match s with
  | fexp_var s0 => Eq_fexp s0
  | fexp_app s0 s1 =>
      congr_fexp_app
        (compSubstSubst_fexp sigma_ftyp sigma_fexp tau_ftyp tau_fexp
           theta_ftyp theta_fexp Eq_ftyp Eq_fexp s0)
        (compSubstSubst_fexp sigma_ftyp sigma_fexp tau_ftyp tau_fexp
           theta_ftyp theta_fexp Eq_ftyp Eq_fexp s1)
  | fexp_abs s0 s1 =>
      congr_fexp_abs
        (compSubstSubst_ftyp sigma_ftyp tau_ftyp theta_ftyp Eq_ftyp s0)
        (compSubstSubst_fexp (up_fexp_ftyp sigma_ftyp)
           (up_fexp_fexp sigma_fexp) (up_fexp_ftyp tau_ftyp)
           (up_fexp_fexp tau_fexp) (up_fexp_ftyp theta_ftyp)
           (up_fexp_fexp theta_fexp) (up_subst_subst_fexp_ftyp _ _ _ Eq_ftyp)
           (up_subst_subst_fexp_fexp _ _ _ _ Eq_fexp) s1)
  | fexp_tapp s0 s1 =>
      congr_fexp_tapp
        (compSubstSubst_fexp sigma_ftyp sigma_fexp tau_ftyp tau_fexp
           theta_ftyp theta_fexp Eq_ftyp Eq_fexp s0)
        (compSubstSubst_ftyp sigma_ftyp tau_ftyp theta_ftyp Eq_ftyp s1)
  | fexp_tabs s0 =>
      congr_fexp_tabs
        (compSubstSubst_fexp (up_ftyp_ftyp sigma_ftyp)
           (up_ftyp_fexp sigma_fexp) (up_ftyp_ftyp tau_ftyp)
           (up_ftyp_fexp tau_fexp) (up_ftyp_ftyp theta_ftyp)
           (up_ftyp_fexp theta_fexp) (up_subst_subst_ftyp_ftyp _ _ _ Eq_ftyp)
           (up_subst_subst_ftyp_fexp _ _ _ _ Eq_fexp) s0)
  end.

Lemma renRen_fexp (xi_ftyp : nat -> nat) (xi_fexp : nat -> nat)
  (zeta_ftyp : nat -> nat) (zeta_fexp : nat -> nat) (s : fexp) :
  ren_fexp zeta_ftyp zeta_fexp (ren_fexp xi_ftyp xi_fexp s) =
  ren_fexp (funcomp zeta_ftyp xi_ftyp) (funcomp zeta_fexp xi_fexp) s.
Proof.
exact (compRenRen_fexp xi_ftyp xi_fexp zeta_ftyp zeta_fexp _ _
         (fun n => eq_refl) (fun n => eq_refl) s).
Qed.

Lemma renRen'_fexp_pointwise (xi_ftyp : nat -> nat) (xi_fexp : nat -> nat)
  (zeta_ftyp : nat -> nat) (zeta_fexp : nat -> nat) :
  pointwise_relation _ eq
    (funcomp (ren_fexp zeta_ftyp zeta_fexp) (ren_fexp xi_ftyp xi_fexp))
    (ren_fexp (funcomp zeta_ftyp xi_ftyp) (funcomp zeta_fexp xi_fexp)).
Proof.
exact (fun s =>
       compRenRen_fexp xi_ftyp xi_fexp zeta_ftyp zeta_fexp _ _
         (fun n => eq_refl) (fun n => eq_refl) s).
Qed.

Lemma renSubst_fexp (xi_ftyp : nat -> nat) (xi_fexp : nat -> nat)
  (tau_ftyp : nat -> ftyp) (tau_fexp : nat -> fexp) (s : fexp) :
  subst_fexp tau_ftyp tau_fexp (ren_fexp xi_ftyp xi_fexp s) =
  subst_fexp (funcomp tau_ftyp xi_ftyp) (funcomp tau_fexp xi_fexp) s.
Proof.
exact (compRenSubst_fexp xi_ftyp xi_fexp tau_ftyp tau_fexp _ _
         (fun n => eq_refl) (fun n => eq_refl) s).
Qed.

Lemma renSubst_fexp_pointwise (xi_ftyp : nat -> nat) (xi_fexp : nat -> nat)
  (tau_ftyp : nat -> ftyp) (tau_fexp : nat -> fexp) :
  pointwise_relation _ eq
    (funcomp (subst_fexp tau_ftyp tau_fexp) (ren_fexp xi_ftyp xi_fexp))
    (subst_fexp (funcomp tau_ftyp xi_ftyp) (funcomp tau_fexp xi_fexp)).
Proof.
exact (fun s =>
       compRenSubst_fexp xi_ftyp xi_fexp tau_ftyp tau_fexp _ _
         (fun n => eq_refl) (fun n => eq_refl) s).
Qed.

Lemma substRen_fexp (sigma_ftyp : nat -> ftyp) (sigma_fexp : nat -> fexp)
  (zeta_ftyp : nat -> nat) (zeta_fexp : nat -> nat) (s : fexp) :
  ren_fexp zeta_ftyp zeta_fexp (subst_fexp sigma_ftyp sigma_fexp s) =
  subst_fexp (funcomp (ren_ftyp zeta_ftyp) sigma_ftyp)
    (funcomp (ren_fexp zeta_ftyp zeta_fexp) sigma_fexp) s.
Proof.
exact (compSubstRen_fexp sigma_ftyp sigma_fexp zeta_ftyp zeta_fexp _ _
         (fun n => eq_refl) (fun n => eq_refl) s).
Qed.

Lemma substRen_fexp_pointwise (sigma_ftyp : nat -> ftyp)
  (sigma_fexp : nat -> fexp) (zeta_ftyp : nat -> nat)
  (zeta_fexp : nat -> nat) :
  pointwise_relation _ eq
    (funcomp (ren_fexp zeta_ftyp zeta_fexp)
       (subst_fexp sigma_ftyp sigma_fexp))
    (subst_fexp (funcomp (ren_ftyp zeta_ftyp) sigma_ftyp)
       (funcomp (ren_fexp zeta_ftyp zeta_fexp) sigma_fexp)).
Proof.
exact (fun s =>
       compSubstRen_fexp sigma_ftyp sigma_fexp zeta_ftyp zeta_fexp _ _
         (fun n => eq_refl) (fun n => eq_refl) s).
Qed.

Lemma substSubst_fexp (sigma_ftyp : nat -> ftyp) (sigma_fexp : nat -> fexp)
  (tau_ftyp : nat -> ftyp) (tau_fexp : nat -> fexp) (s : fexp) :
  subst_fexp tau_ftyp tau_fexp (subst_fexp sigma_ftyp sigma_fexp s) =
  subst_fexp (funcomp (subst_ftyp tau_ftyp) sigma_ftyp)
    (funcomp (subst_fexp tau_ftyp tau_fexp) sigma_fexp) s.
Proof.
exact (compSubstSubst_fexp sigma_ftyp sigma_fexp tau_ftyp tau_fexp _ _
         (fun n => eq_refl) (fun n => eq_refl) s).
Qed.

Lemma substSubst_fexp_pointwise (sigma_ftyp : nat -> ftyp)
  (sigma_fexp : nat -> fexp) (tau_ftyp : nat -> ftyp)
  (tau_fexp : nat -> fexp) :
  pointwise_relation _ eq
    (funcomp (subst_fexp tau_ftyp tau_fexp)
       (subst_fexp sigma_ftyp sigma_fexp))
    (subst_fexp (funcomp (subst_ftyp tau_ftyp) sigma_ftyp)
       (funcomp (subst_fexp tau_ftyp tau_fexp) sigma_fexp)).
Proof.
exact (fun s =>
       compSubstSubst_fexp sigma_ftyp sigma_fexp tau_ftyp tau_fexp _ _
         (fun n => eq_refl) (fun n => eq_refl) s).
Qed.

Lemma rinstInst_up_ftyp_fexp (xi : nat -> nat) (sigma : nat -> fexp)
  (Eq : forall x, funcomp (fexp_var) xi x = sigma x) :
  forall x, funcomp (fexp_var) (upRen_ftyp_fexp xi) x = up_ftyp_fexp sigma x.
Proof.
exact (fun n => ap (ren_fexp shift id) (Eq n)).
Qed.

Lemma rinstInst_up_fexp_ftyp (xi : nat -> nat) (sigma : nat -> ftyp)
  (Eq : forall x, funcomp (ftyp_var) xi x = sigma x) :
  forall x, funcomp (ftyp_var) (upRen_fexp_ftyp xi) x = up_fexp_ftyp sigma x.
Proof.
exact (fun n => ap (ren_ftyp id) (Eq n)).
Qed.

Lemma rinstInst_up_fexp_fexp (xi : nat -> nat) (sigma : nat -> fexp)
  (Eq : forall x, funcomp (fexp_var) xi x = sigma x) :
  forall x, funcomp (fexp_var) (upRen_fexp_fexp xi) x = up_fexp_fexp sigma x.
Proof.
exact (fun n =>
       match n with
       | S n' => ap (ren_fexp id shift) (Eq n')
       | O => eq_refl
       end).
Qed.

Fixpoint rinst_inst_fexp (xi_ftyp : nat -> nat) (xi_fexp : nat -> nat)
(sigma_ftyp : nat -> ftyp) (sigma_fexp : nat -> fexp)
(Eq_ftyp : forall x, funcomp (ftyp_var) xi_ftyp x = sigma_ftyp x)
(Eq_fexp : forall x, funcomp (fexp_var) xi_fexp x = sigma_fexp x) (s : fexp)
{struct s} : ren_fexp xi_ftyp xi_fexp s = subst_fexp sigma_ftyp sigma_fexp s
:=
  match s with
  | fexp_var s0 => Eq_fexp s0
  | fexp_app s0 s1 =>
      congr_fexp_app
        (rinst_inst_fexp xi_ftyp xi_fexp sigma_ftyp sigma_fexp Eq_ftyp
           Eq_fexp s0)
        (rinst_inst_fexp xi_ftyp xi_fexp sigma_ftyp sigma_fexp Eq_ftyp
           Eq_fexp s1)
  | fexp_abs s0 s1 =>
      congr_fexp_abs (rinst_inst_ftyp xi_ftyp sigma_ftyp Eq_ftyp s0)
        (rinst_inst_fexp (upRen_fexp_ftyp xi_ftyp) (upRen_fexp_fexp xi_fexp)
           (up_fexp_ftyp sigma_ftyp) (up_fexp_fexp sigma_fexp)
           (rinstInst_up_fexp_ftyp _ _ Eq_ftyp)
           (rinstInst_up_fexp_fexp _ _ Eq_fexp) s1)
  | fexp_tapp s0 s1 =>
      congr_fexp_tapp
        (rinst_inst_fexp xi_ftyp xi_fexp sigma_ftyp sigma_fexp Eq_ftyp
           Eq_fexp s0) (rinst_inst_ftyp xi_ftyp sigma_ftyp Eq_ftyp s1)
  | fexp_tabs s0 =>
      congr_fexp_tabs
        (rinst_inst_fexp (upRen_ftyp_ftyp xi_ftyp) (upRen_ftyp_fexp xi_fexp)
           (up_ftyp_ftyp sigma_ftyp) (up_ftyp_fexp sigma_fexp)
           (rinstInst_up_ftyp_ftyp _ _ Eq_ftyp)
           (rinstInst_up_ftyp_fexp _ _ Eq_fexp) s0)
  end.

Lemma rinstInst'_fexp (xi_ftyp : nat -> nat) (xi_fexp : nat -> nat)
  (s : fexp) :
  ren_fexp xi_ftyp xi_fexp s =
  subst_fexp (funcomp (ftyp_var) xi_ftyp) (funcomp (fexp_var) xi_fexp) s.
Proof.
exact (rinst_inst_fexp xi_ftyp xi_fexp _ _ (fun n => eq_refl)
         (fun n => eq_refl) s).
Qed.

Lemma rinstInst'_fexp_pointwise (xi_ftyp : nat -> nat) (xi_fexp : nat -> nat)
  :
  pointwise_relation _ eq (ren_fexp xi_ftyp xi_fexp)
    (subst_fexp (funcomp (ftyp_var) xi_ftyp) (funcomp (fexp_var) xi_fexp)).
Proof.
exact (fun s =>
       rinst_inst_fexp xi_ftyp xi_fexp _ _ (fun n => eq_refl)
         (fun n => eq_refl) s).
Qed.

Lemma instId'_fexp (s : fexp) : subst_fexp (ftyp_var) (fexp_var) s = s.
Proof.
exact (idSubst_fexp (ftyp_var) (fexp_var) (fun n => eq_refl)
         (fun n => eq_refl) s).
Qed.

Lemma instId'_fexp_pointwise :
  pointwise_relation _ eq (subst_fexp (ftyp_var) (fexp_var)) id.
Proof.
exact (fun s =>
       idSubst_fexp (ftyp_var) (fexp_var) (fun n => eq_refl)
         (fun n => eq_refl) s).
Qed.

Lemma rinstId'_fexp (s : fexp) : ren_fexp id id s = s.
Proof.
exact (eq_ind_r (fun t => t = s) (instId'_fexp s) (rinstInst'_fexp id id s)).
Qed.

Lemma rinstId'_fexp_pointwise : pointwise_relation _ eq (@ren_fexp id id) id.
Proof.
exact (fun s =>
       eq_ind_r (fun t => t = s) (instId'_fexp s) (rinstInst'_fexp id id s)).
Qed.

Lemma varL'_fexp (sigma_ftyp : nat -> ftyp) (sigma_fexp : nat -> fexp)
  (x : nat) : subst_fexp sigma_ftyp sigma_fexp (fexp_var x) = sigma_fexp x.
Proof.
exact (eq_refl).
Qed.

Lemma varL'_fexp_pointwise (sigma_ftyp : nat -> ftyp)
  (sigma_fexp : nat -> fexp) :
  pointwise_relation _ eq
    (funcomp (subst_fexp sigma_ftyp sigma_fexp) (fexp_var)) sigma_fexp.
Proof.
exact (fun x => eq_refl).
Qed.

Lemma varLRen'_fexp (xi_ftyp : nat -> nat) (xi_fexp : nat -> nat) (x : nat) :
  ren_fexp xi_ftyp xi_fexp (fexp_var x) = fexp_var (xi_fexp x).
Proof.
exact (eq_refl).
Qed.

Lemma varLRen'_fexp_pointwise (xi_ftyp : nat -> nat) (xi_fexp : nat -> nat) :
  pointwise_relation _ eq (funcomp (ren_fexp xi_ftyp xi_fexp) (fexp_var))
    (funcomp (fexp_var) xi_fexp).
Proof.
exact (fun x => eq_refl).
Qed.

Class Up_fexp X Y :=
    up_fexp : X -> Y.

Class Up_ftyp X Y :=
    up_ftyp : X -> Y.

#[global]Instance Subst_fexp : (Subst2 _ _ _ _) := @subst_fexp.

#[global]Instance Up_fexp_fexp : (Up_fexp _ _) := @up_fexp_fexp.

#[global]Instance Up_fexp_ftyp : (Up_ftyp _ _) := @up_fexp_ftyp.

#[global]Instance Up_ftyp_fexp : (Up_fexp _ _) := @up_ftyp_fexp.

#[global]Instance Ren_fexp : (Ren2 _ _ _ _) := @ren_fexp.

#[global]Instance VarInstance_fexp : (Var _ _) := @fexp_var.

#[global]Instance Subst_ftyp : (Subst1 _ _ _) := @subst_ftyp.

#[global]Instance Up_ftyp_ftyp : (Up_ftyp _ _) := @up_ftyp_ftyp.

#[global]Instance Ren_ftyp : (Ren1 _ _ _) := @ren_ftyp.

#[global]
Instance VarInstance_ftyp : (Var _ _) := @ftyp_var.

Notation "[ sigma_ftyp ; sigma_fexp ]" := (subst_fexp sigma_ftyp sigma_fexp)
( at level 1, left associativity, only printing)  : fscope.

Notation "s [ sigma_ftyp ; sigma_fexp ]" :=
(subst_fexp sigma_ftyp sigma_fexp s)
( at level 7, left associativity, only printing)  : subst_scope.

Notation "↑__fexp" := up_fexp (only printing)  : subst_scope.

Notation "↑__fexp" := up_fexp_fexp (only printing)  : subst_scope.

Notation "↑__ftyp" := up_fexp_ftyp (only printing)  : subst_scope.

Notation "↑__fexp" := up_ftyp_fexp (only printing)  : subst_scope.

Notation "⟨ xi_ftyp ; xi_fexp ⟩" := (ren_fexp xi_ftyp xi_fexp)
( at level 1, left associativity, only printing)  : fscope.

Notation "s ⟨ xi_ftyp ; xi_fexp ⟩" := (ren_fexp xi_ftyp xi_fexp s)
( at level 7, left associativity, only printing)  : subst_scope.

Notation "'var'" := fexp_var ( at level 1, only printing)  : subst_scope.

Notation "x '__fexp'" := (@ids _ _ VarInstance_fexp x)
( at level 5, format "x __fexp", only printing)  : subst_scope.

Notation "x '__fexp'" := (fexp_var x) ( at level 5, format "x __fexp")  :
subst_scope.

Notation "[ sigma_ftyp ]" := (subst_ftyp sigma_ftyp)
( at level 1, left associativity, only printing)  : fscope.

Notation "s [ sigma_ftyp ]" := (subst_ftyp sigma_ftyp s)
( at level 7, left associativity, only printing)  : subst_scope.

Notation "↑__ftyp" := up_ftyp (only printing)  : subst_scope.

Notation "↑__ftyp" := up_ftyp_ftyp (only printing)  : subst_scope.

Notation "⟨ xi_ftyp ⟩" := (ren_ftyp xi_ftyp)
( at level 1, left associativity, only printing)  : fscope.

Notation "s ⟨ xi_ftyp ⟩" := (ren_ftyp xi_ftyp s)
( at level 7, left associativity, only printing)  : subst_scope.

Notation "'var'" := ftyp_var ( at level 1, only printing)  : subst_scope.

Notation "x '__ftyp'" := (@ids _ _ VarInstance_ftyp x)
( at level 5, format "x __ftyp", only printing)  : subst_scope.

Notation "x '__ftyp'" := (ftyp_var x) ( at level 5, format "x __ftyp")  :
subst_scope.

#[global]
Instance subst_fexp_morphism :
 (Proper
    (respectful (pointwise_relation _ eq)
       (respectful (pointwise_relation _ eq) (respectful eq eq)))
    (@subst_fexp)).
Proof.
exact (fun f_ftyp g_ftyp Eq_ftyp f_fexp g_fexp Eq_fexp s t Eq_st =>
       eq_ind s
         (fun t' => subst_fexp f_ftyp f_fexp s = subst_fexp g_ftyp g_fexp t')
         (ext_fexp f_ftyp f_fexp g_ftyp g_fexp Eq_ftyp Eq_fexp s) t Eq_st).
Qed.

#[global]
Instance subst_fexp_morphism2 :
 (Proper
    (respectful (pointwise_relation _ eq)
       (respectful (pointwise_relation _ eq) (pointwise_relation _ eq)))
    (@subst_fexp)).
Proof.
exact (fun f_ftyp g_ftyp Eq_ftyp f_fexp g_fexp Eq_fexp s =>
       ext_fexp f_ftyp f_fexp g_ftyp g_fexp Eq_ftyp Eq_fexp s).
Qed.

#[global]
Instance ren_fexp_morphism :
 (Proper
    (respectful (pointwise_relation _ eq)
       (respectful (pointwise_relation _ eq) (respectful eq eq))) (@ren_fexp)).
Proof.
exact (fun f_ftyp g_ftyp Eq_ftyp f_fexp g_fexp Eq_fexp s t Eq_st =>
       eq_ind s
         (fun t' => ren_fexp f_ftyp f_fexp s = ren_fexp g_ftyp g_fexp t')
         (extRen_fexp f_ftyp f_fexp g_ftyp g_fexp Eq_ftyp Eq_fexp s) t Eq_st).
Qed.

#[global]
Instance ren_fexp_morphism2 :
 (Proper
    (respectful (pointwise_relation _ eq)
       (respectful (pointwise_relation _ eq) (pointwise_relation _ eq)))
    (@ren_fexp)).
Proof.
exact (fun f_ftyp g_ftyp Eq_ftyp f_fexp g_fexp Eq_fexp s =>
       extRen_fexp f_ftyp f_fexp g_ftyp g_fexp Eq_ftyp Eq_fexp s).
Qed.

#[global]
Instance subst_ftyp_morphism :
 (Proper (respectful (pointwise_relation _ eq) (respectful eq eq))
    (@subst_ftyp)).
Proof.
exact (fun f_ftyp g_ftyp Eq_ftyp s t Eq_st =>
       eq_ind s (fun t' => subst_ftyp f_ftyp s = subst_ftyp g_ftyp t')
         (ext_ftyp f_ftyp g_ftyp Eq_ftyp s) t Eq_st).
Qed.

#[global]
Instance subst_ftyp_morphism2 :
 (Proper (respectful (pointwise_relation _ eq) (pointwise_relation _ eq))
    (@subst_ftyp)).
Proof.
exact (fun f_ftyp g_ftyp Eq_ftyp s => ext_ftyp f_ftyp g_ftyp Eq_ftyp s).
Qed.

#[global]
Instance ren_ftyp_morphism :
 (Proper (respectful (pointwise_relation _ eq) (respectful eq eq))
    (@ren_ftyp)).
Proof.
exact (fun f_ftyp g_ftyp Eq_ftyp s t Eq_st =>
       eq_ind s (fun t' => ren_ftyp f_ftyp s = ren_ftyp g_ftyp t')
         (extRen_ftyp f_ftyp g_ftyp Eq_ftyp s) t Eq_st).
Qed.

#[global]
Instance ren_ftyp_morphism2 :
 (Proper (respectful (pointwise_relation _ eq) (pointwise_relation _ eq))
    (@ren_ftyp)).
Proof.
exact (fun f_ftyp g_ftyp Eq_ftyp s => extRen_ftyp f_ftyp g_ftyp Eq_ftyp s).
Qed.

Ltac auto_unfold := repeat
                     unfold VarInstance_ftyp, Var, ids, Ren_ftyp, Ren1, ren1,
                      Up_ftyp_ftyp, Up_ftyp, up_ftyp, Subst_ftyp, Subst1,
                      subst1, VarInstance_fexp, Var, ids, Ren_fexp, Ren2,
                      ren2, Up_ftyp_fexp, Up_fexp, up_fexp, Up_fexp_ftyp,
                      Up_ftyp, up_ftyp, Up_fexp_fexp, Up_fexp, up_fexp,
                      Subst_fexp, Subst2, subst2.

Tactic Notation "auto_unfold" "in" "*" := repeat
                                           unfold VarInstance_ftyp, Var, ids,
                                            Ren_ftyp, Ren1, ren1,
                                            Up_ftyp_ftyp, Up_ftyp, up_ftyp,
                                            Subst_ftyp, Subst1, subst1,
                                            VarInstance_fexp, Var, ids,
                                            Ren_fexp, Ren2, ren2,
                                            Up_ftyp_fexp, Up_fexp, up_fexp,
                                            Up_fexp_ftyp, Up_ftyp, up_ftyp,
                                            Up_fexp_fexp, Up_fexp, up_fexp,
                                            Subst_fexp, Subst2, subst2 
                                            in *.

Ltac asimpl' := repeat (first
                 [ progress setoid_rewrite substSubst_fexp_pointwise
                 | progress setoid_rewrite substSubst_fexp
                 | progress setoid_rewrite substRen_fexp_pointwise
                 | progress setoid_rewrite substRen_fexp
                 | progress setoid_rewrite renSubst_fexp_pointwise
                 | progress setoid_rewrite renSubst_fexp
                 | progress setoid_rewrite renRen'_fexp_pointwise
                 | progress setoid_rewrite renRen_fexp
                 | progress setoid_rewrite substSubst_ftyp_pointwise
                 | progress setoid_rewrite substSubst_ftyp
                 | progress setoid_rewrite substRen_ftyp_pointwise
                 | progress setoid_rewrite substRen_ftyp
                 | progress setoid_rewrite renSubst_ftyp_pointwise
                 | progress setoid_rewrite renSubst_ftyp
                 | progress setoid_rewrite renRen'_ftyp_pointwise
                 | progress setoid_rewrite renRen_ftyp
                 | progress setoid_rewrite varLRen'_fexp_pointwise
                 | progress setoid_rewrite varLRen'_fexp
                 | progress setoid_rewrite varL'_fexp_pointwise
                 | progress setoid_rewrite varL'_fexp
                 | progress setoid_rewrite rinstId'_fexp_pointwise
                 | progress setoid_rewrite rinstId'_fexp
                 | progress setoid_rewrite instId'_fexp_pointwise
                 | progress setoid_rewrite instId'_fexp
                 | progress setoid_rewrite varLRen'_ftyp_pointwise
                 | progress setoid_rewrite varLRen'_ftyp
                 | progress setoid_rewrite varL'_ftyp_pointwise
                 | progress setoid_rewrite varL'_ftyp
                 | progress setoid_rewrite rinstId'_ftyp_pointwise
                 | progress setoid_rewrite rinstId'_ftyp
                 | progress setoid_rewrite instId'_ftyp_pointwise
                 | progress setoid_rewrite instId'_ftyp
                 | progress
                    unfold up_fexp_fexp, up_fexp_ftyp, up_ftyp_fexp,
                     upRen_fexp_fexp, upRen_fexp_ftyp, upRen_ftyp_fexp,
                     up_ftyp_ftyp, upRen_ftyp_ftyp, up_ren
                 | progress cbn[subst_fexp ren_fexp subst_ftyp ren_ftyp]
                 | progress fsimpl ]).

Ltac asimpl := check_no_evars;
                repeat
                 unfold VarInstance_ftyp, Var, ids, Ren_ftyp, Ren1, ren1,
                  Up_ftyp_ftyp, Up_ftyp, up_ftyp, Subst_ftyp, Subst1, subst1,
                  VarInstance_fexp, Var, ids, Ren_fexp, Ren2, ren2,
                  Up_ftyp_fexp, Up_fexp, up_fexp, Up_fexp_ftyp, Up_ftyp,
                  up_ftyp, Up_fexp_fexp, Up_fexp, up_fexp, Subst_fexp,
                  Subst2, subst2 in *; asimpl'; minimize.

Tactic Notation "asimpl" "in" hyp(J) := revert J; asimpl; intros J.

Tactic Notation "auto_case" := auto_case ltac:(asimpl; cbn; eauto).

Ltac substify := auto_unfold; try setoid_rewrite rinstInst'_fexp_pointwise;
                  try setoid_rewrite rinstInst'_fexp;
                  try setoid_rewrite rinstInst'_ftyp_pointwise;
                  try setoid_rewrite rinstInst'_ftyp.

Ltac renamify := auto_unfold;
                  try setoid_rewrite_left rinstInst'_fexp_pointwise;
                  try setoid_rewrite_left rinstInst'_fexp;
                  try setoid_rewrite_left rinstInst'_ftyp_pointwise;
                  try setoid_rewrite_left rinstInst'_ftyp.

End Core.

Module Extra.

Import Core.

#[global]Hint Opaque subst_fexp: rewrite.

#[global]Hint Opaque ren_fexp: rewrite.

#[global]Hint Opaque subst_ftyp: rewrite.

#[global]Hint Opaque ren_ftyp: rewrite.

End Extra.

Module interface.

Export Core.

Export Extra.

End interface.

Export interface.

