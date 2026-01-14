Module LateDays.
  Inductive letter : Type :=
    | A | B | C | D | E | F.
  Inductive modifier : Type :=
    | Plus | Natural | Minus.
  Inductive grade : Type :=
    Grade (l : letter) (m : modifier).
  Inductive comparison : Type :=
    | Eq
    | Lt
    | Gt.
  Definition letter_comparison (l1 l2 : letter) : comparison :=
    match l1, l2 with
    | A, A => Eq
    | A, _ => Gt
    | B, A => Lt
    | B, B => Eq
    | B, _ => Gt
    | C, (A | B) => Lt
    | C, C => Eq
    | C, _ => Gt
    | D, (A | B | C) => Lt
    | D, D => Eq
    | D, _ => Gt
    | E, F => Gt
    | E, E => Eq
    | E, _ => Lt
    | F, F => Eq
    | F, _ => Lt
    end.

  Compute letter_comparison B A.
  Compute letter_comparison D D.
  Compute letter_comparison B F.

  (* Comparing a letter against itself gives `Eq` *)
  Theorem letter_comparison_Eq :
    forall l, letter_comparison l l = Eq.
  Proof.
    intros l.
    destruct l eqn:El.
    - reflexivity.
    - reflexivity.
    - reflexivity.
    - reflexivity.
    - reflexivity.
    - reflexivity.
  Qed.
End LateDays.
