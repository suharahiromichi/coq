From HB Require Import structures.          (* coq-hierarchy-builder. *)
From mathcomp Require Import all_ssreflect.
From mathcomp Require Import all_algebra.
From mathcomp Require Import all_field.     (* 必要な場合のみ *)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Num.Def.
Import Num.Theory.
Import GRing.Theory.

Import intZmod.

Open Scope ring_scope.
(* Open Scope int_scope. *)

Local Notation "-%Z" := (@oppz) : int_scope.
Local Notation "- x" := (oppz x) : int_scope.
Local Notation "+%Z" := (@addz) : int_scope.
Local Notation "x + y" := (addz x y) : int_scope.
Local Notation "x - y" := (x + - y) : int_scope.

Lemma int_ind (P : int -> Type) :
  P 0
  -> (forall n : nat, P n -> P (n.+1))
  -> (forall n : nat, P (- n)%Z -> P (- (n.+1))%Z) (* ``-`` が oppz になるように、int_scope にする。 *)
  -> forall i : int, P i.
Proof.
  move=> P0 hPp hPn.
  case.
  (* i が 0 以上の場合 *)
  (* forall n : nat, P n *)
  (* n は任意の自然数で、nが0以上の整数に対応する。 *)
  - elim=> [| n ihn].
    + done.                                 (* 0 の場合 *)
    + by apply: hPp.                        (* n.+1 の場合 *)
      
  (* i が -1 以下の場合 *)
  (* forall n : nat, P (Negz n) *)
  (* n は任意の自然数で、``Negz n``が、-1以下の整数に対応する。``Neg 0 = -1`` *)
  - elim=> [| n ihn].
    + apply: hPn.                         (* ``Negz 0 = -1`` の場合 *)
      (* Goal *) Check P (- 0%Z)%Z.
      rewrite /oppz.
      (* Goal *) Check P 0%Z.
      done.
    + apply: hPn.
      (* Goal *) Check P (- n.+1)%Z.
      rewrite /oppz.
      (* Goal *) Check P (Negz n).
      done.
Qed.

(**
``morphism : - (m + n) = - m - n`` の補題
*)
Fail Check oppzD : {morph -%Z : m n / m + n}.
Check oppzD : {morph -%Z : m n / m + n}%Z.
(* -%Z はそれだけで演算子なので、それが使えるように int_scope にする。*)
Check oppzD : {morph oppz : m n / m + n}.
Check oppzD : forall m n, oppz (addz m n) = addz (oppz m) (oppz n).
Check oppzD : forall m n, - (m + n) = - m - n.

(**
以下は成り立ように見えるが、内部では複雑なことは起きている。
  Check oppzD : {morph GRing.opp : m n / m + n}.
  Check oppzD : {morph -%R : m n / m + n}.

int ではなく、GRing の世界の補題には、以下がある。
 *)
Check GRing.opprD : forall V : zmodType, {morph -%R : x y / x + y}.
Check GRing.opprD : forall V : zmodType,
  forall m n : V, GRing.opp (GRing.add m n) = GRing.add (GRing.opp m) (GRing.opp n).
Check GRing.opprD : forall V : zmodType, forall m n : V, - (m + n) = - m - n.

(**
単に elim とすると、``-`` が GRing.opp (-%R) になる。
elim/int_ind とすると、``-`` が oppz (-%Z) となり、うまく証明できる。
*)
Goal forall x y z : int, addz x (addz y z) = addz (addz x y) z :> int.
Proof.
  elim/int_ind => [| m ihm | m ihm] n p.
  - by rewrite !add0z.
  - by rewrite -add1n PoszD !addSz ihm.
  - rewrite -add1n addnC PoszD.
    rewrite oppzD.
    by rewrite !addPz ihm.
Qed.

(* END *)


    Unset Printing Notations.
  - rewrite -add1n addnC PoszD.
    (* ゴールは -%R になってしまっている。 *)
    Check - (m + 1%Z)%Z + (n + p)%Z = (- (m + 1%Z)%Z + n)%Z + p :> int.
    Check (GRing.opp ((Posz m) + (Posz 1))) + (n + p) = (GRing.opp (((Posz m) + (Posz 1))) + n) + p.
    Check (GRing.opp (m%:Z + 1%Z)) + (n + p) = (GRing.opp ((m%:Z + 1%Z) + n)) + p.    

    (* oppzD は -%Z なので、 *)
    Check forall (m n : nat), - (m%:Z + 1%Z) = - m%:Z - 1%Z :> int.
    Set Printing All.
    Check oppzD : {morph oppz : m n / m + n}.
    Check oppzD : {morph -%Z : m n / m + n}.
    (*
    Check oppzD : {morph GRing.opp : m n / m + n}.
    Check oppzD : {morph -%R : m n / m + n}.
    *)

    Check oppzD : forall m n, oppz (addz m n) = addz (oppz m) (oppz n).
    Check oppzD : forall m n, - (m + n) = - m - n.
    Check oppzD : forall m n, -%R (m + n) = -%R m - n :> int.
    Check oppzD : forall m n, - (m + n)%Z = - m%Z - n%Z.
    Check oppzD m 1%N : - (m%:Z + 1%Z)%Z = - m%:Z - 1%Z :> int.

    Fail rewrite oppzD.


    
