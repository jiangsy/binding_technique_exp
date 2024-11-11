Require Import Coq.Program.Equality.
Require Export Metalib.Metatheory.

Require Import stlc.lngen.def_ott.
Require Import stlc.lngen.def_extra.

Ltac inst_cofinite_impl H x :=
  match type of H with
    | forall x, x `notin` ?L -> _ =>
        let Fr := fresh "Fr" in
          assert (x `notin` L) as Fr by auto;
        specialize (H x Fr); clear Fr
  end.

Ltac inst_cofinites_with x :=
  repeat
    match goal with
      | H : forall x0, x0 `notin` ?L -> _ |- _ =>
          inst_cofinite_impl H x
    end.

Ltac inst_cofinite_impl_keep H x :=
  match type of H with
    | forall x, x `notin` ?L -> _ =>
      let H_1 := fresh "H" in
        let Fr := fresh "Fr" in
          assert (x `notin` L) as Fr by auto;
          specialize (H x Fr) as H_1; generalize dependent H
  end.

Ltac inst_cofinites_with_keep x :=
  repeat
    match goal with
      | H : forall x0, x0 `notin` ?L -> _ |- _ =>
          inst_cofinite_impl_keep H x
    end;
  intros.

Tactic Notation "inst_cofinites_with" ident(x) := 
  inst_cofinites_with x.

Tactic Notation "inst_cofinites_with" ident(x) "(keep)" := 
  inst_cofinites_with_keep x.

Ltac inst_cofinites :=
  match goal with
  | x : atom |- _ => inst_cofinites_with x
  end.

Ltac inst_cofinites_with_new :=
  let x := fresh "x" in
  pick fresh x; inst_cofinites_with x.

Ltac inst_cofinites_by F :=
  let L := F in
  let x := fresh "x" in
  pick fresh x for L; inst_cofinites_with x.
  
Tactic Notation "inst_cofinites_by" constr(F) :=
  let x := fresh "x" in let L:=F in pick fresh x for L; inst_cofinites_with x.
Tactic Notation "inst_cofinites_by" constr(L) "using_name" ident(x) := 
  let x := fresh x in pick fresh x for L; inst_cofinites_with x.

Ltac solve_notin_eq X :=
  let H := fresh "H" in
    assert (H: X `notin` singleton X) by auto;
    apply notin_singleton_1 in H; contradiction.

Ltac destruct_eq_atom :=
  unfold eq_dec in *;
  repeat
    lazymatch goal with
    | H : context [EqDec_eq_of_X ?X ?X] |- _ => destruct (EqDec_eq_of_X X X); [ idtac | contradiction]
    | H : _ |- context [EqDec_eq_of_X ?X ?X] => destruct (EqDec_eq_of_X X X); [ idtac | contradiction]
    | H : context [EqDec_eq_of_X ?X0 ?X] |- _ => destruct (EqDec_eq_of_X X0 X); subst;
        try contradiction; try solve_notin_eq X0; try solve_notin_eq X
    | H : _ |- context [EqDec_eq_of_X ?X0 ?X] => destruct (EqDec_eq_of_X X0 X); subst;
        try contradiction; try solve_notin_eq X0; try solve_notin_eq X
    end.

Ltac auto_apply :=
  match goal with
  | H : context [ ?P -> ?Q ] |- ?Q => apply H
  end.

Ltac gather_atoms ::=
  let A := gather_atoms_with (fun x : vars => x) in
  let B := gather_atoms_with (fun x : var => {{ x }}) in
  let C := gather_atoms_with (fun x => var_in_exp x) in
  let D := gather_atoms_with (fun x : ctx => dom x) in

  constr:(A \u B \u C \u D).

Tactic Notation "inst_cofinites_for" constr(H) := 
  let L1 := gather_atoms in
  let L1 := beautify_fset L1 in
  apply H with (L:=L1).

Tactic Notation "inst_cofinites_for" constr(H) ident(name)":="constr(Args1) := 
  let L1 := gather_atoms in
  let L1 := beautify_fset L1 in
  apply H with (L:=L1) (name:=Args1).

Tactic Notation "inst_cofinites_for" constr(H) ident(argname1)":="constr(arg1) "," ident(argname2) ":=" constr(arg2):= 
  let L1 := gather_atoms in
  let L1 := beautify_fset L1 in
  apply H with (L:=L1) (argname1:=arg1) (argname2:=arg2).

Tactic Notation "inst_cofinites_for" constr(H) ident(argname1)":="constr(arg1) "," ident(argname2) ":=" constr(arg2)"," ident(argname3) ":=" constr(arg3):= 
  let L1 := gather_atoms in
  let L1 := beautify_fset L1 in
  apply H with (L:=L1) (argname1:=arg1) (argname2:=arg2)  (argname3:=arg3).

(* destruct conjunctions *)
Ltac destruct_conj :=
  repeat match goal with H: ?T |- _ =>
                         lazymatch T with
                         | exists _ , _ => destruct H
                         | _ /\ _ => destruct H
                         end
    end.

Ltac solve_by_inverts n :=
  match goal with | H : ?T |- _ =>
  match type of T with Prop =>
    solve [
      inversion H;
      match n with S (S (?n')) => subst; solve_by_inverts (S n') end ]
  end end.

Ltac solve_by_invert :=
  solve_by_inverts 1.

Ltac destruct_binds_eq :=
  repeat
    lazymatch goal with
    | H1 : (?X1, ?b1) = (?X2, ?b2) |- _ =>
      dependent destruction H1
    end.

Ltac destruct_binds :=
  simpl in *;
  repeat
  match goal with
  | H1 : binds ?X ?b ((?X', ?b') :: ?θ) |- _ =>
    let H_1 := fresh "H" in
    let H_2 := fresh "H" in
    inversion H1 as [H_1 | H_2];
    clear H1;
    try destruct_binds_eq;
    try solve [solve_notin_eq X];
    try solve [solve_notin_eq X']
  end.

Ltac destruct_in :=
  simpl in *;
  match goal with
  | H1 : ((?X, ?b) = (?X', ?b')) \/  In ?b'' ?θ |- _ =>
    let H1_1 := fresh "H" in
    let H1_2 := fresh "H" in
    inversion H1 as [H1_1 | H1_2];
    clear H1;
    try destruct_binds_eq;
    try solve [solve_notin_eq X];
    try solve [solve_notin_eq X']
  end.
                                