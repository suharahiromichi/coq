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

(* ディフォルトのScopeはintにしないが、後で ``%Z`` や ``:>int`` で int scope を指定する。 *)
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

Goal associative addz.
Proof.
  rewrite /associative.
  Check forall x y z : int, x + (y + z) = (x + y) + z :> int.
  Check forall x y z : int, addz x (addz y z) = addz (addz x y) z :> int.
  
  elim/int_ind => [| m IHm | m IHm] n p.
  Check 0 + (n + p) = ((0 + n)%Z + p) :> int.
  Check @add0z : forall x, 0 + x = x :> int.
  - by rewrite !add0z.

  Check m.+1 + (n + p) = (m.+1 + n)%Z + p :> int.
  Check PoszD : forall (m n : nat), (m + n)%N = m + n :> int.
  Check addSz : forall x y : int, (1 + x) + y = 1 + (x + y) :> int.
  - rewrite -add1n.
    rewrite PoszD !addSz IHm.
    done.
    
  Check (- m.+1)%Z + (n + p) = ((- m.+1)%Z + n) + p :> int.
  Check oppzD : forall (x y : int), - (x + y) = -x + -y :> int.
  Check addPz : forall x y : int, (x + -1) + y = (x + y) +  -1 :> int.
  - rewrite -add1n addnC.
    rewrite PoszD.
    rewrite oppzD.
    rewrite !addPz IHm.
    done.
Qed.

Goal left_inverse (0 : int) oppz addz.
Proof.
  rewrite /left_inverse.
  Check forall x : int, - x + x = 0 :> int.
  
  elim/int_ind.                             (* elim : int *)
  Check - 0 + 0 = 0 :> int.
  - done.
    Unset Printing Notations.
  Check forall n : nat, (- n)%Z + n = 0 :> int -> (- n.+1)%Z + n.+1 = 0 :> int.
  - elim.                                   (* elim : nat *)
    + done.
    + done.
  - elim.                                   (* elim : nat *)
    + done.
    + done.
Qed.

(* END *)
