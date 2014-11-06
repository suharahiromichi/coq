(**
An introduction to small scale reflection in Coq

6. Finite objects in SSReflect

http://hal.inria.fr/docs/00/55/53/79/PDF/main-rr.pdf
*)

Require Import ssreflect ssrfun ssrbool eqtype ssrnat div seq.
Require Import path choice fintype tuple finfun finset.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

(**
6.3 Finite functions, finite sets

CIC (Calculus of Inductive Constructions) では、以下は成立しない。
forall f1 f2 : aT -> rT, (forall x : aT, f1 x = f2 x) -> f1 = f2
しかし、aTが有限型ならば、成立する。
*)

Check ffunP.
(**
forall (aT : finType) (rT : Type) (f1 f2 : {ffun aT -> rT}),
  f1 =1 f2 <-> f1 = f2.

ただし、(f1 =1 f2) == (forall x, f1 x = f2 x)
*)
Lemma tuto_ffunP : forall (f1 f2 : {ffun 'I_6 -> nat}),
       (forall x, f1 x = f2 x) <-> f1 = f2.
Proof.
  move=> f1 f2.
  by apply ffunP.
Qed.

(** 同様に *)

Check setP.
(**
forall (T : finType) (A B : {set T}), A =i B <-> A = B
*)
Lemma tuto_setP : forall (A B : {set 'I_6}),
       A =i B <-> A = B.
Proof.
  move=> A B.
  by apply setP.
Qed.

(** 有限集合の例 *)

(*
Definition S : {set 'I_6}.
Proof.
  rewrite /set_of.
  apply FinSet.
  rewrite /pred.
  apply finfun.
  apply (testn ).
Defined.
*)

Definition q0 : 'I_6. Proof. have : 0 < 6 by []. apply Ordinal. Defined.
Definition q1 : 'I_6. Proof. have : 1 < 6 by []. apply Ordinal. Defined.
Definition q2 : 'I_6. Proof. have : 2 < 6 by []. apply Ordinal. Defined.
Definition q3 : 'I_6. Proof. have : 3 < 6 by []. apply Ordinal. Defined.
Definition q4 : 'I_6. Proof. have : 4 < 6 by []. apply Ordinal. Defined.
Definition q5 : 'I_6. Proof. have : 5 < 6 by []. apply Ordinal. Defined.

Check [set q0] : {set 'I_6}.
Check [set x in 'I_6] : {set 'I_6}.
Check [set x | x \in 'I_6] : {set 'I_6}.    (* [set x in 'I_6] の構文糖 *)
Check [set x | x in 'I_6] : {set 'I_6}.
Check [set: 'I_6] : {set 'I_6}.

(** よく使うコンストラクション *)
Goal q0 \in [set q0].
Proof.
  by apply/set1P.
Qed.

Goal mem [set q0] q0.
Proof.
  by apply/set1P.
Qed.

Goal q0 \in q0 |: set0.
Proof.
  Search (_ |: _).
  by apply setU11.
Qed.

Goal q0 \in [set q0; q1].
Proof.
  Search ([set _]).
  apply/set2P.
  by left.
Qed.

Goal q0 |: set0 = [set q0].
Proof.
  by rewrite setU0.
Qed.

Goal [set q0] \subset [set q0; q1].
Proof.
  rewrite -{1}(setU0 [set q0]).
  (* 構文糖のせいで解りにくいが： *)
  (* [set q0] :|: set0 = [set q0] :|: [set q1] *)
  Search (_ \subset _).
  apply setUS.
  by apply sub0set.
Qed.

Goal [set q0] \proper [set q0; q1].
Proof.
  Search (_ \proper _).  
  apply properUl.
  apply negbT.
  admit.
Qed.

Goal q0 \in [set q0] :|: [set q1].
Proof.
  (* q0 \in [set q0; q1] *)
  apply/set2P.
  by left.
Qed.

Goal q0 \in [set q0; q1] :&: [set q0; q2].
Proof.
  admit.
Qed.

Goal q0 \in [set q0] :&: [set: 'I_6].
Proof.
  Search (_ :&: _).
  rewrite setIT.
  by apply/set1P.
Qed.

Goal q0 \in ~: [set q1].
Proof.
  Search ([set~ _]).
  rewrite in_setC1.
  by [].
Qed.

Goal q0 \in [set~ q1].
Proof.
  rewrite in_setC1.
  by [].
Qed.

Goal q0 \in [set q0; q1] :\: [set q1].
Proof.
  apply/setD1P.
  split.
  - by [].
  - apply/set2P.
    by left.
Qed.

Goal q0 \in [set q0; q1] :\ q1.
Proof.
  apply/setD1P.
  split.
  - by [].
  - apply/set2P.
    by left.
Qed.

(**
Exercise 6.3.1
 *)
Section setOpsExos.
  Variable T : finType.
  Implicit Types a x : T.
  Implicit Types A B C D : {set T}.

  Lemma tuto_eqEsubset : forall A B,
                           (A == B) = (A \subset B) && (B \subset A).
  Proof.
    move=> A B.
    apply/eqP/subset_eqP.
    - by move=> <-.
    - by move/setP.
  Qed.
  
  Lemma tuto_set1P : forall x a, reflect (x = a) (x \in [set a]).
  Proof.
    admit.
  Qed.

  Lemma tuto_setD1P : forall x A b,
                        reflect (x != b /\ x \in A) (x \in A :\ b).
  Proof.
    admit.
  Qed.
  
  Lemma tuto_setIA : forall A B C, A :&: (B :&: C) = A :&: B :&: C.
  Proof.
    admit.
  Qed.

  Lemma tuto_setUIl : forall A B C,
                        (A :&: B) :|: C = (A :|: C) :&: (B :|: C).
  Proof.
    admit.
  Qed.
  
  Lemma tuto_setCU : forall A B, ~: (A :|: B) = ~: A :&: ~: B.
  Proof.
    admit.
  Qed.
End setOpsExos.


(* END *)
