(**
整数の証明
*)
From HB Require Import structures.
From mathcomp Require Import all_ssreflect.
(* From mathcomp Require Import all_algebra. *)
From mathcomp Require Import ssralg ssrnum ssrint.

(**
# ssrnum までの構造を使えるようにする。
 *)
Import Order.TTheory.                       (* order.v *)
Import GRing.Theory.                        (* ssralg.v *)
Import Num.Def Num.Theory.                  (* ssrnum.v *)

(**
# scope
*)
Open Scope ring_scope.
Check 1 : (_ : semiRingType).

(*
Open Scope int_scope.
*)
Check 1 : int.

(**
# import
*)
Import intZmod.
Import intRing.
Import intUnitRing.
Import intOrdered.

(**
# いくつかの公理 (alg/int_sample.v)
*)

(**
## nonzero1z 1は0ではない。
*)
Goal 1 != 0 :> int.
Proof.
Admitted.

(**
## mulVx
*)
Print left_inverse.
Goal {in unitz, left_inverse 1 invz  *%R}.
Proof.
  move=> n.
  Check n \is a unitz -> (invz n) * n = 1 :> int.
  (* n が逆元を持つなら、nの逆元とnの積は1である。 *)
  
  rewrite /unitz.
  Check n \is a [qualify a n0 | (n0 == 1) || (n0 == -1)].
  (* n は 1 または -1 である。 *)
  
  Check @pred2P int int
    : forall x y z u : int, reflect (x = y \/ z = u) ((x == y) || (z == u)).
Admitted.

(**
# 帰納法 (alg/int_ind.v)
 *)

(**
使う補題
 *)
Check @add0z : left_id 0%Z addz.
Check @add0z : forall x, addz 0 x = x.

Check PoszD : {morph Posz : m n / (m + n)%N >-> m + n}.
Check PoszD : forall (m n : nat), (m + n)%N = m + n :> int.

Check oppzD : {morph oppz : x y / addz x y}.
Check oppzD : forall (x y : int), - (x + y) = -x + -y :> int.

Check addSz : forall x y : int, (1 + x) + y = 1 + (x + y) :> int.
Check addPz : forall x y : int, (x + -1) + y = (x + y) +  -1 :> int.

Goal associative addz.
Proof.
  rewrite /associative.
  Check forall x y z : int, x + (y + z) = (x + y) + z :> int.
  Check forall x y z : int, addz x (addz y z) = addz (addz x y) z :> int.
  
  elim/int_ind => [| m ihm | m ihm] n p.

Admitted.

Goal left_inverse (0 : int) oppz addz.
Proof.
  elim/int_ind.                             (* elim : int *)
Admitted.


(* END *)
