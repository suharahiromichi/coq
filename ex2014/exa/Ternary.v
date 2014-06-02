(* Ternary.v *)

Delimit Scope tern_scope with tern.

Inductive tern := true | intermed | false.

Definition andt a b :=
  match a, b with
  | false, _ | _, false => false
  | intermed, _ | _, intermed => intermed
  | _, _ => true
  end.

Notation "a && b" := (andt a b) : tern_scope.

Definition ort a b :=
  match a, b with
  | true, _ | _, true => true
  | intermed, _ | _, intermed => intermed
  | _, _ => false
  end.

Notation "a || b" := (ort a b) : tern_scope.

(* end *)
