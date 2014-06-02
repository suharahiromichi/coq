(* TernaryProperties.v *)

Require Import Ternary.

Lemma andt_assoc a b c : (a && (b && c) = (a && b) && c)%tern.
Proof.
  destruct a; destruct b; destruct c; reflexivity.
Qed.

Lemma andt_comm a b : (a && b = b && a)%tern.
Proof.
  destruct a; destruct b; reflexivity.
Qed.

Lemma ort_assoc a b c : (a || (b || c) = (a || b) || c)%tern.
Proof.
  destruct a; destruct b; destruct c; reflexivity.
Qed.

Lemma ort_comm a b : (a || b = b || a)%tern.
Proof.
  destruct a; destruct b; reflexivity.
Qed.

(* end *)
