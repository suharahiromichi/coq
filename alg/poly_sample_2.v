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
Print polyOver. (* = fun (R : ringType) (S : {pred R}) => [qualify a p | polyOver_pred S p] *)
Check @polyOverP : forall (R : ringType) (S : addrClosed R) (p : {poly R}),
    reflect (forall i : nat, p`_i \in S) (p \is a polyOver S).

Goal 1%:P`_0  \in (@Num.int_num_subdef rat).
Proof.
  apply/polyOverP => /=.
(**
polyOverP で持ち上げる。
*)
  Check 1%:P \is a polyOver Num.int_num_subdef.
(**
定数に持ち下げる。
*)
  rewrite polyOverC /=.
  Check 1 \in  Num.int_num_subdef.
  done.
Qed.

(**
## int_num と Num.int_num_subdef ... どちらも同じ。
*)
Check (1%:P : {poly rat})`_0 \is a int_num.
Check 1%:P`_0 \is a @int_num rat.
Check 1%:P`_0 \is a int_num.

Check 1%:P`_0 \is a [qualify a x0 | Num.int_num_subdef x0].

Check @Num.int_num_subdef rat 1%:P`_0.
Check Num.int_num_subdef 1%:P`_0.

Check 1%:P`_0  \in @Num.int_num_subdef rat.
Check 1%:P`_0  \in Num.int_num_subdef.

(**
## nat_num と int_num の説明
ssrnum.v で定義された「自然数である」「整数である」。
*)
(**
1 は、nat である。
*)
Goal 1 \is a (@nat_num rat). Proof. done. Qed.

Goal (1 : rat) \is a nat_num. Proof. done. Qed.
Goal ~~ ((-1 : rat) \is a nat_num). Proof. done. Qed.

(**
-1 は、int である。
*)
Goal (1 : rat) \is a int_num. Proof. done. Qed.
Goal (-1 : rat) \is a int_num. Proof. done. Qed.
Goal ~~ (((1 / 2) : rat) \is a int_num). Proof. done. Qed.

(**
整数係数の多項式を考える。
*)
Definition f : {poly rat} := 'X^2 * (3%:P - 4 *: 'X) ^+ 2.

(**
多項式を展開できれば、```\_i`` を求めることで証明できる。
*)
Goal forall (i : nat), f`_i \is a int_num.
Proof.
  rewrite /f => i.
  have -> : 'X^2 * (3%:P - 4 *: 'X) ^+ 2 = 9 *: 'X^2 - 24 *: 'X^3 + 16 *: 'X^4 by admit.
  case: i => [| [| [| [| [| i]]]]] //=.
  - by rewrite !coefE.
  - by rewrite !coefE.
  - by rewrite !coefE.
  - by rewrite !coefE.
  - by rewrite !coefE.
  - by rewrite !coefE.
Admitted.                                   (* OK *)

(**
## ``predOverP`` で多項式に持ち上げる証明

持ち上げたあと、``rpred*`` と ``polyOver*`` の補題を使うと直接証明できる。
*)
Goal forall (i : nat), f`_i \is a int_num.
Proof.
  apply/polyOverP => /=.
  Check f \is a polyOver Num.int_num_subdef.
  rewrite rpredM //=.
  - rewrite rpredX //=.
    by rewrite polyOverX.
  - rewrite rpredX //=.
    + rewrite rpredB //=.
      * by rewrite polyOverC.
      * rewrite polyOverZ //=.
        by rewrite polyOverX.
Qed.

Check rpredD : forall (V : nmodType) (S : addrClosed V), {in S &, forall u v : V, u + v \in S}.
Check rpredB : forall (V : zmodType) (S : zmodClosed V), {in S &, forall u v : V, u - v \in S}.
Check rpredM : forall (R : semiRingType) (s : mulr2Closed R), GRing.mulr_2closed s.

Check polyOver0 : forall (R : ringType) (S0 : {pred R}), 0 \is a polyOver S0.
Check polyOverC : forall (R : ringType) (S0 : addrClosed R) (c : R), (c%:P \is a polyOver S0) = (c \in S0).
Check polyOverZ : forall (R : ringType) (S0 : semiringClosed R),
    {in S0 & polyOver S0, forall (c : R) (p : {poly R}), c *: p \is a polyOver S0}.
Check polyOverX : forall (R : ringType) (S : semiringClosed R), 'X \is a polyOver S.

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
## 多項式pを微分したときの係数 (よく使う補題)
*)
Check @coef_deriv R
  : forall (p : {poly R}) (i : nat), (p^`())`_i = p`_i.+1 *+ i.+1.

(* coef_deriv *)
Goal forall (p : {poly R}) i,  p ^`()`_i = p`_i.+1 *+ i.+1.
Proof.
  move=> p i.
  rewrite coef_poly -subn1 ltn_subRL.
  case: leqP => //.
  move/(nth_default 0) ->.
  rewrite mul0rn.
  done.
Qed.

Check @coef_derivn R
  : forall (n : nat) (p : {poly R}) (i : nat), (p^`(n))`_i = p`_(n + i) *+ (n + i) ^_ n.

(**
## ``deriv`` と ``derivn n`` は線形である。ssralg.v で定義。
 *)
Check deriv_is_linear : forall R : ringType, linear (deriv (R:=R)).

(* 証明 *)
Goal linear (@deriv R).
Proof.
  move=> k p q.
  Check (k *: p + q)^`() = k *: p^`() + q^`().
  apply/polyP => i.
  rewrite !(coef_deriv, coefD, coefZ).
  rewrite mulrnDl.
  rewrite mulrnAr.
  done.
Qed.
HB.about GRing.isLinear.Build.              (* 登録 *)

(**
以下が成り立つようになり、線形性についての補題が使えるようになる。
*)
Check (@deriv R) : {linear {poly R} -> {poly R}}.

Check linearE.                              (* マルチルール *)
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

(**
## 微分公式（マルチルール）
 *)
Check derivZ      : forall (R : ringType) (c : R) (p : {poly R}), (c *: p)^`() = c *: p^`().
Check deriv_mulC  : forall (R : ringType) (c : R) (p : {poly R}), (c%:P * p)^`() = c%:P * p^`().
Check derivC      : forall (R : ringType) (c : R), c%:P^`() = 0.
Check derivX      : forall R : ringType, 'X ^`() = 1.
Check derivMXaddC : forall (R : ringType) (p : {poly R}) (c : R), (p * 'X + c%:P)^`() = p + p^`() * 'X.
Check derivXsubC  : forall (R : ringType) (a : R), ('X - a%:P)^`() = 1.
Check derivM      : forall (R : ringType) (p q : {poly R}), (p * q)^`() = p^`() * q + p * q^`().

Check derivB      : forall R : ringType, {morph deriv (R:=R) : p q / p - q}.
Check derivD      : forall R : ringType, {morph deriv (R:=R) : p q / p + q}.
Check derivN      : forall R : ringType, {morph deriv (R:=R) : p / - p}.

Check derivB p q  : (p - q)^`() = p^`() - q^`().
Check derivD p q  : (p + q)^`() = p^`() + q^`().
Check derivN p    : (- p)^`() = - p^`().

Check derivXn     : forall (R : ringType) (n : nat), 'X^n^`() = 'X^n.-1 *+ n.
Check derivM      : forall (R : ringType) (p q : {poly R}), (p * q)^`() = p^`() * q + p * q^`().
Check derivMn     : forall (R : ringType) (n : nat) (p : {poly R}), (p *+ n)^`() = p^`() *+ n.
Check derivE.                               (* マルチルール *)

(* derivZ *)
Goal forall (c : R) (p : {poly R}), (c *: p)^`() = c *: p^`().
Proof.
  move=> c p.
  Check linearZ.
  Check linearZ (a:=c).
  Check @linearZ R {poly R} _ GRing.scale R GRing.scale c c.
  Check Linear.map_for {poly R} GRing.scale c ( *:%R c).
  rewrite (@linearZ R {poly R} _ GRing.scale R GRing.scale c c).
  simpl.
  done.
Qed.

(* derivD 線形性 *)
Goal forall (p q : {poly R}), (p + q)^`() = p^`() + q^`().
Proof.
  move=> p q.
  by apply: linearD.
Qed.

(* deriv_mulC *)
Goal forall (c : R) (p : {poly R}), (c%:P * p)^`() = c%:P * p^`().
Proof.
  move=> c p.
  rewrite !mul_polyC.
  rewrite derivZ.
  done.
Qed.

(* derivMXaddC *)
Goal forall (p : {poly R}) (c : R), (p * 'X + c%:P)^`() = p + p^`() * 'X.
Proof.
  move=> p c.
  apply/polyP=> i.
  rewrite raddfD /= derivC addr0 coefD !(coefMX, coef_deriv).
  by case: i; rewrite ?addr0.
Qed.

(* derivM *)
Goal forall (p q : {poly R}), (p * q) ^`() = p ^`() * q + p * q ^`().
Proof.
  move=> p q.
  elim/poly_ind: p => [|p b IHp].           (* poly_sample.v 参照 *)
  
  Check (0 * q)^`() = 0^`() * q + 0 * q^`().
  - by rewrite !(mul0r, add0r, derivC).

  Check IHp : (p * q)^`() = p^`() * q + p * q^`().
  Check ((p * 'X + b%:P) * q)^`() = (p * 'X + b%:P)^`() * q + (p * 'X + b%:P) * q^`().
  - rewrite mulrDl -mulrA -commr_polyX mulrA -[_ * 'X]addr0 raddfD /=.
    rewrite !derivMXaddC.
    rewrite deriv_mulC.
    rewrite IHp !mulrDl -!mulrA !commr_polyX !addrA.
    done.
Qed.

(**
## 高階微分の正規化式
 *)
Locate "a ^`N ( n )". (*  := (nderivn n a) : ring_scope (default interpretation) *)
Print nderivn.
(* = fun (R : ringType) (n : nat) (p : {poly R}) => \poly_(i < size p - n) (p`_(n + i) *+ 'C(n + i, n)) *)

Check @coef_nderivn R
  : forall (n : nat) (p : {poly R}) (i : nat), (p^`N(n))`_i = p`_(n + i) *+ 'C(n + i, n).
Check @nderivn_def R
  : forall (n : nat) (p : {poly R}), p^`(n) = p^`N(n) *+ n`!.

(**
# map poly

係数に``f``を適用する。
 *)
Notation "p ^ f" := (map_poly (GRing.Additive.sort f) p) : ring_scope. (* locally *)
Print map_poly. (* = fun (aR rR : ringType) (f : aR -> rR) (p : {poly aR}) => \poly_(i < size p) f p`_i *)

Check map_polyE
  : forall (aR rR : ringType) (f : aR -> rR) (p : {poly aR}), map_poly f p = Poly [seq f i | i <- val p].

(**
## 多項式を係数とする多項式
*)
Locate "p ^:P". (* := (map_poly polyC p) : ring_scope (default interpretation) *)

(**
# 多項式の合成 (polynomial composition)
 *)
Locate "p \Po q". (* := (comp_poly q p) : ring_scope (default interpretation) *)
Print comp_poly. (* = fun (R : ringType) (q p : {poly R}) => p^:P.[q] *)

Check @comp_polyE R : forall p q : {poly R}, p \Po q = \sum_(i < size p) (p`_i *: (q ^+ i)).

(**
多項式の合成の変形
*)
Check comp_polyX : forall (R : ringType) (p : {poly R}), 'X \Po p = p.
Check comp_polyC : forall (R : ringType) (c : R) (p : {poly R}), c%:P \Po p = c%:P.
Check comp_polyD : forall (R : ringType) (p q r : {poly R}), (p + q) \Po r = p \Po r + (q \Po r).
Check comp_polyB : forall (R : ringType) (p q r : {poly R}), (p - q) \Po r = p \Po r - (q \Po r).
Check comp_polyZ : forall (R : ringType) (c : R) (p q : {poly R}), (c *: p) \Po q = c *: (p \Po q).
Check comp_polyM : forall (R : comRingType) (p q r : {poly R}), p * q \Po r = (p \Po r) * (q \Po r).

(**
## 多項式を係数とする多項式の値
 *)
Check horner_comp : forall (R : comRingType) (p q : {poly R}) (x : R), (p \Po q).[x] = p.[q.[x]].

(**
## 多項式を係数とする多項式の微分
 *)
Check deriv_comp : forall (R : comRingType) (p q : {poly R}), (p \Po q)^`() = (p^`() \Po q) * q^`().

(**
# 外科手術

## 多項式の偶数部
*)
Print even_poly. (* = fun (R : ringType) (p : {poly R}) => \poly_(i < uphalf (size p)) p`_i.*2 *)

(**
## 多項式の奇数部
 *)
Print odd_poly. (* = fun (R : ringType) (p : {poly R}) => \poly_(i < (size p)./2) p`_i.*2.+1 *)

(* END *)
