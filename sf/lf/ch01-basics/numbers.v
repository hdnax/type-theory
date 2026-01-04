(* vim:ft=coq *)

(* Recursive definition to define an unary representation of natural numbers *)
Inductive nat : Type :=
  | O             (* zero *)
  | S (n : nat).  (* successor/scratch *)
