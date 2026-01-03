(* vim:ft=coq *)

(* Enumerated data type - days of the week *)
Inductive day : Type :=
  | monday
  | tuesday
  | wednesday
  | thursday
  | friday
  | saturday
  | sunday.

(* Pattern matching *)
(** The type signature is optional due to Rocq's ability to perform type inference - but it is included anyway to enhance readability **)
Definition next_working_day (d : day) : day :=
  match d with
  | monday => tuesday
  | tuesday => wednesday
  | wednesday => thursday
  | thursday => friday
  | friday => monday
  | saturday => monday
  | sunday => monday
  end.
