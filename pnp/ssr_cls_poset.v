Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq.
Require Import fintype finfun finset.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Module POSETDef.
  Class POSET (T : Type) :=
    Mixin
      {
        rel_op : T -> T -> bool;
        refl (x : T) : rel_op x x;
        asym (x y : T) : rel_op x y -> rel_op y x -> x = y;
        trans (y x z : T) : rel_op x y -> rel_op y z -> rel_op x z
      }.
  Notation "x <== y" := (rel_op x y) (at level 70, no associativity).
End POSETDef.  
Export POSETDef.

Section NatPosetExamples.
  Check leqnn : forall n : nat, n <= n.
  Lemma eqn_leq' : forall m n, m <= n -> n <= m -> m = n.
  Proof.
    move=> m n.
    elim: m n => [|m IHm] [|n] //.
      move=> H1 H2; congr (_ .+1); move: H1 H2.
      by apply (IHm n).
  Qed.
  Check leq_trans : forall n m p : nat, m <= n -> n <= p -> m <= p.
  
  Instance natPOSET : POSET nat :=
    {
    (* *** *)
    }.
  Proof.
    by apply leqnn.
    by apply eqn_leq'.
    by apply leq_trans.
  Qed.
  
  Variables x y z : nat.
  
  Goal x <== x.
  Proof.
    by apply: refl.
  Qed.

  Goal x <== y -> y <== x -> x = y.
  Proof.
    by apply: asym.
  Qed.
  
  Goal x <== y -> y <== z -> x <== z.
  Proof.
    by apply: trans.
  Qed.
End NatPosetExamples.

(* END *)
