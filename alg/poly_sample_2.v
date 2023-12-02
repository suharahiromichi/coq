From elpi Require Import elpi.
From HB Require Import structures.
From mathcomp Require Import all_ssreflect.
From mathcomp Require Import all_algebra.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Num.Def.
Import Num.Theory.
Import GRing.Theory.

Local Open Scope ring_scope.

(**
本資料は ``{poly R}`` が ringType であることまで扱うので、R も ringType とする。
*)
Variable R : ringType.
Variable (a b c x y z : R) (p q r d : {poly R}).

(**
# 根
## n乗根 (1の冪乗根) Root of Unity

n乗して1になる数。
 *)

Check 3.-unity_root : pred R.
Locate "n .-unity_root". (* := (root_of_unity n) : ring_scope (default interpretation) *)
Print root_of_unity. (* = fun (R : ringType) (n : nat) => root ('X^n - 1) *)

Check @unity_rootE R : forall (n : nat) (z : R), n.-unity_root z = (z ^+ n == 1).
Check @unity_rootP R : forall (n : nat) (z : R), reflect (z ^+ n = 1) (n.-unity_root z).

Goal 3.-unity_root (1 : R).
Proof.
  rewrite unity_rootE.
  (* 1 ^+ 3 == 1 *)
  by rewrite expr1n.
Qed.

Goal (1 : R) \in 3.-unity_root.
Proof.
  Check unfold_in : forall (T : Type) (x : T) (p : pred T), (x \in [eta p]) = p x.
  rewrite unfold_in.                        (* coq/theorem/ssr/ssrbool.v *)
  (* ('X^3 - 1).[1] == 0 *)
  rewrite !hornerE hornerXn.
  (* 1 ^+ 3 - 1 == 0 *)
  by rewrite expr1n subr_eq0.
Qed.

(**
## 原始n乗根 Primitive Root of Unity

i (< n) 乗しても1にならず、n乗してはじめて1になる数
 *)

Check 3.-primitive_root : pred R.
Locate "n .-primitive_root". (* := (primitive_root_of_unity n) : ring_scope (default interpretation) *)
Print primitive_root_of_unity. (* = fun (R : ringType) (n : nat) (z : R) => (0 < n)%N
                                  && [forall i, (i.+1).-unity_root z == (i.+1 == n)] *)

(* 原始n乗根である。 *)
Check @prim_order_exists R : forall (n : nat) (z : R), (0 < n)%N -> z ^+ n = 1 ->
                                                       {m : nat | m.-primitive_root z & (m %| n)%N}.
(* 原始n乗根なら。 *)
Check @prim_expr_order R : forall (n : nat) (z : R), n.-primitive_root z -> z ^+ n = 1.

Search (_ .-primitive_root).
Section NUMBER.
  Variable R : numDomainType.

  Goal 2.-primitive_root (-1 : R).
  Proof.
    apply/andP.
    split=> //=.
    apply/forallP => /= i.
    rewrite unity_rootE.
    case: i.
    case; [| case] => //= _.
    - rewrite expr1.
      by rewrite eqNr oner_eq0.
    - rewrite expr2 mulNr mul1r opprK.
      by rewrite 2!eq_refl.
  Qed.
End NUMBER.

(**
# 環の述語を多項式に持ち上げる(lift)。
 *)
(* Variable S : {pred R}. *)
Print polyOver. (* = fun (R : ringType) (S : {pred R}) => [qualify a p | polyOver_pred S p] *)
Print polyOver_pred. (* = fun (R : ringType) (S : {pred R}) (p : {poly R}) => all (mem S) *)

Section ADDCLOSED.
  Variable S : addrClosed R.                (* 環の述語 *)
  Check S : {pred R}.                       (* 環の述語 *)
(**
述語Sが環の加法で閉じた述語であるとき、
多項式pの係数のすべてが``S``を成り立たせることと、多項式pは``polyOver S``を成り立たせることは、同値。
*)
  Check @polyOverP R S : forall p : {poly R}, reflect (forall i : nat, p`_i \in S) (p \is a polyOver S).

(**
述語Sが環の加法で閉じた述語であるとき、
定数多項式 c が``polyOver S``を成り立たせることこ、cが``S``を成り立たせることは、同値。
*)
  Check @polyOverC R S : forall c : R, (c%:P \is a polyOver S) = (c \in S).
  
  HB.about GRing.isAddClosed.
End ADDCLOSED.

Section SEMIRING.
  Variable S : semiringClosed R.
  Check S : {pred R}.
  Check S : addrClosed R.
  Fail Check S : zmodClosed R.
  Check S : mulrClosed R.
  Check S : semiringClosed R.
  
  Check @rpredM R S : GRing.mulr_2closed S.
  HB.about GRing.isMul2Closed.  
  
  Check @rpred1 R S : 1 \in S.
  (* isMul2 を継承するわけではない。 *)
  HB.about GRing.isMul1Closed.
End SEMIRING.

Section ZMOD.
  Variable S : zmodClosed R.
  Check S : {pred R}.
  Check S : addrClosed R.
  Check S : zmodClosed R.
  Fail Check S : mulrClosed R.
  Fail Check S : semiringClosed R.
  
  Check @rpredNr R S : oppr_closed S.
  HB.about GRing.isOppClosed.
End ZMOD.

Section RING.
  Variable S : subringClosed R.
  Check S : zmodClosed R.
  Check S : semiringClosed R.

  Check @rpred1 R S : 1 \in S.
  (* GRing.Mul2Closed を継承する。 *)
  HB.about GRing.MulClosed.
End RING.

(**
# 1変数関数の微分法 (single derivation)
*)
Locate "a ^` ()". (* := (deriv a) : ring_scope (default interpretation) *)
Locate "a ^` ( n )". (* := (derivn n a) : ring_scope (default interpretation) *)
Print deriv. (* = fun (R : ringType) (p : {poly R}) => \poly_(i < (size p).-1) (p`_i.+1 *+ i.+1) *)
Print derivn. (* = fun (R : ringType) (n : nat) => [eta iter n (deriv (R:=R))] *)

Check @deriv : forall R : ringType, {poly R} -> {poly R}.

Check Poly [:: 3; 2; 1].
Check deriv (Poly [:: 3; 2; 1]).
Check @deriv R (Poly [:: 3; 2; 1]).

(**
## 多項式pを微分したときの係数は。。。。
*)
Check @coef_deriv R : forall (p : {poly R}) (i : nat), (p^`())`_i = p`_i.+1 *+ i.+1.
Check @coef_derivn R : forall (n : nat) (p : {poly R}) (i : nat), (p^`(n))`_i = p`_(n + i) *+ (n + i) ^_ n.

(**
## マルチルール
 *)
Check derivE.
Check (derivZ, deriv_mulC, derivC, derivX, derivMXaddC, derivXsubC, derivM, derivB,
        derivD, derivN, derivXn, derivM, derivMn).

(**
## ``deriv`` と ``derivn n`` は線形である。ssralg.v で定義。
 *)
Check deriv_is_linear : forall R : ringType, linear (deriv (R:=R)).
HB.about GRing.isLinear.Build.

(**
以下が成り立つようになり、補題が使えるようになる。
*)
Check (@deriv R) : {linear {poly R} -> {poly R}}.

Check linear0 (@deriv R) : 0^`() = 0.
Check linearN (@deriv R) : {morph (@deriv R) : x / - x >-> - x}.
Check linearD (@deriv R) : {morph (@deriv R) : x y / x + y >-> x + y}.
Check linearB (@deriv R) : {morph (@deriv R) : x y / x - y >-> x - y}.
Check linearMn (@deriv R) : forall n : nat,  {morph deriv (R:=R) : x / x *+ n >-> x *+ n}.
Check linearMNn (@deriv R) : forall n : nat, {morph deriv (R:=R) : x / x *- n >-> x *- n}.
Check linearP (@deriv R) : forall a,         {morph deriv (R:=R) : u v / a *: u + v >-> a *: u + v}.

Check linearN (@deriv R) : forall x, (- x)^`() = - x^`().
Check linearD (@deriv R) : forall x y, (x + y)^`() = x^`() + y^`().
Check linearB (@deriv R) : forall x y, (x - y)^`() = x^`() - y^`().
Check linearMn (@deriv R) : forall n x, (x *+ n)^`() = x^`() *+ n.
Check linearMNn (@deriv R) : forall n x, (x *- n)^`() = x^`() *- n.
Check linearP (@deriv R) : forall a x y, (a *: x + y)^`() = (a *: x^`()) + y^`().

Goal 0^`() = 0 :> {poly R}.
Proof.
  Check (@deriv R) : {linear {poly R} -> {poly R}}.
  Check linear0 (@deriv R) : deriv 0 = 0.
  
  (* Goal *) Check deriv 0 = 0.
  by rewrite (linear0 (@deriv R)).
  Undo.
  by apply: linear0.
  Undo.
  by rewrite linearE.
Qed.

(* END *)
