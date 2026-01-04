(* vim:ft=coq *)

(* Recursive definition to define an unary representation of natural numbers *)
Inductive nat : Type :=
  | O             (* zero *)
  | S (n : nat).  (* successor/scratch *)

(** At this point, nat and otherNat just use different markers, other than that, they have no differences **)
Inductive otherNat : Type :=
  | stop
  | tick (foo : otherNat).

(* Give an interpretation to nat to distinguish it from otherNat *)
Definition pred (n : nat) : nat :=
  match n with
  | O => O
  | S n' => n'
  end.
