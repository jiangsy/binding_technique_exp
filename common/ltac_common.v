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

Ltac auto_apply :=
  match goal with
  | H : context [ ?P -> ?Q ] |- ?Q => apply H
  end.