(**
整数の証明
*)
From HB Require Import structures.
From mathcomp Require Import all_ssreflect.
(* From mathcomp Require Import all_algebra. *)
From mathcomp Require Import ssralg ssrnum ssrint.

From mathcomp Require Import zify ring lra. (* テスト *)

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

int の Notation は宣言されていないので、int_scope を open しても良いことはない。
だから、int_scope を open する必要はないのだろう。

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
  done.
Qed.

(**
## mulVx
*)
Print left_inverse.
Goal {in unitz, left_inverse 1 invz *%R}.
Proof.
  move=> n.
  
  Check invz : int -> int.
  Check n \is a unitz -> (invz n) * n = 1 :> int.
  (* n が逆元を持つなら、nの逆元とnの積は1である。 *)
  
  rewrite /unitz.
  Check n \is a [qualify a n0 | (n0 == 1) || (n0 == -1)].
  Check n \in [qualify a n0 | (n0 == 1) || (n0 == -1)].  
  
  rewrite /has_quality.
  Check n \in (fun x : int => (x == 1) || (x == -1)) -> invz n * n = 1.
  (* n は 1 または -1 である。 *)
  
  Check @pred2P int int
    : forall x y z u : int, reflect (x = y \/ z = u) ((x == y) || (z == u)).
  
  by case/pred2P => ->.
Qed.
(**
- ``is a`` は ``in`` と同じ。 ``isn't a`` などもある。

- ``{in A, P}`` も ``[qualify x | P]`` の coq-core の ssrbool.v で定義されている。
coq-core.8.18.0/theories/ssr/ssrbool.v

  - ``{in A, P}`` は隠れている束縛変数で intro する。
  - ``[qualify x | P]`` は、has_quality (語尾注意) で unfold する。
*)

(**
# 帰納法 (alg/int_ind.v)
 *)

Print int_ind.
(**
int_ind = int_rect
   : forall P : int -> Type,
       P 0%Z ->
       (forall n : nat, P n        -> P n.+1) ->
       (forall n : nat, P (oppz n) -> P (oppz n.+1)) ->
       forall i : int, P i

n は自然数だが、P は整数の述語なので、整数で証明する必要がある。
*)

(**
使う補題
 *)
Check @add0z : left_id 0%Z addz.
Check @add0z : forall x, 0 + x = x :> int.

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
  
  elim/int_ind => [| m IHm | m IHm] n p.
  (* 0 の場合 *)
  Check addz 0%Z (addz n p) = addz (addz 0%Z n) p.
  - by rewrite 2!add0z.
    
  (* 正の場合 *)
  Check IHm : forall y z : int, addz m (addz y z) = addz (addz m y) z.
  Check addz m.+1 (addz n p) = addz (addz m.+1 n) p.
  - rewrite -add1n.
    rewrite PoszD.
    rewrite 3!addSz.
    rewrite IHm.
    done.
    
  (* 負の場合 *)
  Check IHm : forall y z : int, addz (oppz m) (addz y z) = addz (addz (oppz m) y) z.
  Check addz (oppz m.+1) (addz n p) = addz (addz (oppz m.+1) n) p.
  - rewrite -add1n.
    rewrite addnC.
    rewrite PoszD.
    rewrite oppzD.
    rewrite 3!addPz.
    rewrite IHm.
    done.
Qed.

Goal left_inverse (0 : int) oppz addz.
Proof.
  rewrite /left_inverse.
  elim/int_ind.                             (* int の帰納法 *)
  - done.
  - by elim.                                (* nat の帰納法 *)
  - by elim.                                (* nat の帰納法 *)
Qed.

(* END *)
