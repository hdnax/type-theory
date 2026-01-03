(* vim:ft=coq *)

Inductive bool : Type :=
  | true
  | false.

(* More complex inductive types - Constructors with arguments *)

Inductive rgb : Type :=
  | red
  | green
  | blue.

Inductive color : Type :=
  | black
  | white
  | primary (p : rgb).

(* Pattern matching for complex constructors *)
Definition monochrome (c : color) : bool :=
  match c with
  | black => true
  | white => true
  | primary p => false
  end.
