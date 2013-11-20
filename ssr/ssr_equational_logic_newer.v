(* 等式論理 *)

Require Import ssreflect ssrbool eqtype ssrnat.
Require Import seq ssrfun.

Section Equational_logic.

  Check eq_op.                              (* == *)
  Check eqP.                                (* reflect (?2 = ?3) (?2 == ?3) *)
  Check _ =P _.                             (* reflect (?2 = ?3) (?2 == ?3) *)
  
  Check eqb.                                (* bool -> bool -> bool *)

(*
  Lemma predU1P : reflect (x = y \/ b) ((x == y) || b).
  Lemma pred2P : reflect (x = y \/ z = u) ((x == y) || (z == u)).
*)

  Theorem eqb_refl : forall (x : bool), x == x.
  Proof.
    move=> x.
    by apply/eqP.
  Qed.

  Theorem eqb_sym : forall (x y : bool), x == y -> y == x.
  Proof.
    move=> x y.
    move/eqP => H. rewrite -H.
      by apply/eqP.
  Qed.

  Lemma eqb_sym' : forall (x y : bool), (x == y) = (y == x).
  Proof.
    move=> x y.
      by case: x.
  Qed.
  
  Lemma del_true' : forall (x : bool), x <-> true == x.
  Proof.
    done.
  Qed.
(*
    move=> x.
    split.
    (* -> *)
    move=> H. case H.
    done.
    (* <- *)
    move/eqP=> H.
    by rewrite -H.
*)

  Lemma del_false' : forall (x : bool), ~~ x <-> false == x.
  Proof.
    done. 
  Qed.
(*
    move=> x.
    split.
    case x.
      rewrite /negb. move=> H. inversion H.
      done.
    move/eqP.
    move=> H. rewrite -H. done.
*)

  Lemma del_true : forall (x : bool), reflect x (true == x).
  Proof.
    move=> x. case: x.
    by apply ReflectT.
    by apply ReflectF.
  Qed.

  Lemma del_true_eq : forall (x : bool), (x == true) = x.
  Proof.
    move=> x.
    Admitted.

  Lemma del_false_eq : forall (x : bool), (x == false) = ~~x.
  Proof.
    move=> x.
    Admitted.

  Lemma del_true_eq' : forall (x : bool), (true == x) = x.
  Proof.
    move=> x.
    Admitted.

  Lemma eqb_trans3 : forall (x y z : bool),
                      reflect (x == y /\ y == z) (x == y == z).
  (* これは、成立しない。 *)
  Admitted.

  Lemma eqb_trans2 : forall (x y z : bool),
                       reflect (x = z) (x == y == z).
  Proof.
    move=> x y z.
    case .
    rewrite del_true_eq.
      by apply eqP.
    rewrite del_false_eq.
    case: (x == z).
  

  

