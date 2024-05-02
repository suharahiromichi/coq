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
# コンストラクタ
*)
Print polynomial.
(**

R型の多項式は、R型のリストと、その最後の要素が``0``でないことの証明の組み合わせで定義される。
```
= Record polynomial (R : semiRingType) : Type :=
    Polynomial {
        polyseq : seq R;
        _ : is_true (last 1 polyseq != 0)
 }.
```

``last 1`` の ``1`` は、lastのディフォルト値（[::]だったときの値）であり、
``0``でなければなんでも良い数である。
ベース型であるリストの``[::]``が``1``を意味する多項式であるとは言っていない。
 *)

Axiom neqa0 : a != 0.
Lemma neq0_last_s : a != 0 -> last 1 [:: c; b; a] != 0.
Proof. done. Qed.
Check @Polynomial R [:: c; b; a] (neq0_last_s neqa0).
Check Polynomial (neq0_last_s neqa0).
Definition tstp1 := Polynomial (neq0_last_s neqa0).

(**
## {poly R}

``{poly R}`` は ``polynomial R`` と同じ意味だが、Phantom Typeを使って semiRingType型 のみ引数にとれる。
 *)
Check tstp1 : polynomial R.
Check tstp1 : {poly R}.

Check bool : semiRingType.
Check {poly bool}.

(**
次節で insubd のディフォルトとして使うために poly_nil を定義する。
*)
Print poly_nil. (* = fun R : semiRingType => Polynomial (oner_neq0 R) *)
Check poly_nil R : polynomial R.
(**
型Rを引数として、R型の``[::]``多項式を返す。この時点では、これが、0多項式であるという意味はない。
ただし、``last 1 [::]``の値である``1``が、``0``でないことに依存して作るので、
polynomial の証明部分は、``last 1`` でなければならないことが判る。
*)
Check oner_neq0 : forall s : semiRingType, 1 != 0.

(**
polyseq は単射である。

これは、両辺が``{poly R}``の等式を``seq R``の等式に変換する便利な補題である。
polyP はこれを使って証明している。
 *)
Check @poly_inj R : forall (p1 p2 : polynomial R), polyseq p1 = polyseq p2 :> seq R -> p1 = p2 :> {poly R}.
Check @poly_inj R : forall (p1 p2 : {poly R}), polyseq p1 = polyseq p2 :> seq R -> p1 = p2 :> {poly R}.

(**
## seqのサブタイプ
*)
Check [isSub for polyseq]
  : isSub.axioms_ (seq R) (fun x : seq R => last 1 x != 0) (polynomial R).
Check val : {poly R} -> seq R.
Check @insubd (seq R) (fun x : seq R => last 1 x != 0) {poly R} : {poly R} -> seq R -> {poly R}.
Check insubd : {poly R} -> seq R -> {poly R}.

Check @insubd (seq R) (fun s => last 1 s != 0) (polynomial R) (poly_nil R) [:: c; b; a].
Check insubd (poly_nil R) [:: c; b; a].
Definition tstp2 := insubd (poly_nil R) [:: c; b; a].

(**
## ```_i``

```_i`` は、単なるnth であるが、空リストの場合 0%:R を返す。これにより、
ベース型のリスト[::]から作られた多項式は、0の意味を持つことになる。
*)
Locate "s `_ i". (* := (nth GRing.zero s i) : ring_scope (default interpretation) *)
Print coefp.     (* = fun (R : semiRingType) (i : nat) (p : {poly R}) => p`_i *)

Goal (poly_nil R)`_0 = 0%:R.
Proof. done. Qed.

(**
## lead_coef 最大次数の係数をかえす関数
*)
Print lead_coef. (* = fun (R : semiRingType) (p : {poly R}) => p`_(size p).-1 *)
Compute lead_coef tstp1.                    (* a *)
Compute tstp1`_(size tstp1).-1.             (* a *)

Check lead_coefE : forall (R : semiRingType) (p : {poly R}), lead_coef p = p`_(size p).-1.

(**
## coefE - マルチルール (inEのような補題の直積) (多分「マルチツール」の駄洒落)

p`_i の簡約に便利だという。定義はずっとあとである。
*)
Check coefE.
Check (coef0, coef1, coefC, coefX, coefXn, coef_sumMXn,
        coefZ, coefMC, coefCM, coefXnM, coefMXn, coefXM, coefMX, coefMNn, coefMn,
        coefN, coefB, coefD, coef_even_poly, coef_odd_poly,
        coef_take_poly, coef_drop_poly, coef_cons, coef_Poly, coef_poly,
        coef_deriv, coef_nderivn, coef_derivn, coef_map, coef_sum,
        coef_comp_poly_Xn, coef_comp_poly).

(**
# polyC %:P 定数多項式

引数に 0 が与えられる場合を考慮すると、単なる ``[:: c]`` ではだめで、insubd で定義する必要がある。
 *)
Check insubd (poly_nil R) [:: c] : {poly R}.
Check polyC c  : {poly R}.
Definition tstp_c := polyC c.

Check polyC 0  : {poly R}.
Definition tstp_c0 := @polyC R 0.

(**
``0%:P``が``[::]``になるのは、polyC の定義で insubd の代替項が、poly_nil であること。
もともとの poly_nil 自体には``0``の意味はないことに注意するべきである。
*)
Locate "_ %:P". (* := (polyC c) : ring_scope (default interpretation) *)
Print polyC. (* = fun (R : semiRingType) (c : R) => insubd (poly_nil R) [:: c] *)

Goal (val 0%:P) == [::] :> seq R.
Proof.
  rewrite /polyC.
  rewrite val_insubd /=.
  case H : (0 == 0).
  - done.
  - Search ((_ == _) = false).
    by case/eqP in H.
Qed.

(**
``c%:P`` が nseq を使った式に書き換えられるという補題は、``(0 != 0) = 0`` や ``(42 != 0) = 1``
のコアーションを使う。つまり、``c = 0`` なら、サイズ0のリストを作る。
それ以外は、サイズ1のリストを作る。
*)
Check polyseqC : forall (R : semiRingType) (c : R), c%:P = nseq (c != 0) c :> seq R.
Goal c%:P = nseq (c != 0) c :> seq R.
Proof.
  (* true が 1、false が 0 にコアーションされることを使う。 *)
  Compute nseq (0%N != 0%N) 0%N.            (* [::] *)
  Compute nseq (1%N != 0%N) 1%N.            (* [:: 1] *)
  Compute nseq (42%N != 0%N) 42%N.          (* [:: 42] *)
  
  rewrite val_insubd /=.
  by case H : (c == 0).
Qed.  

(**
係数がすべて同じなら、多項式として同じ。
0多項式であってもこれは成り立つ。
*)
Check polyP : forall (R : semiRingType) (p q : {poly R}), nth 0 p =1 nth 0 q <-> p = q.

(**
# 多項式の作り方

## cons_poly
*)
Print cons_poly.                            (* 略 *)
Check cons_poly : forall R : semiRingType, R -> {poly R} -> {poly R}.

(* p が nil (0多項式) でないなら、cons_poly は、 p に c を cons したもの。
   p が nil (0多項式) なら、cons_poly は、 c の定数多項式。
   これは、seq R で比較する。
   ~~~~~~~~~~~~~~~~~~~~~~~~ *)
Check polyseq_cons : forall (R : semiRingType) (c : R) (p : {poly R}),
    cons_poly c p = (if ~~ nilp p then c :: p else c%:P) :> seq R.
Goal cons_poly x tstp1 = x :: tstp1 :> seq R.
Proof.
  rewrite polyseq_cons.
  done.
Qed.

Goal cons_poly x (poly_nil R) = x%:P :> seq R.
Proof.
  rewrite [LHS]polyseq_cons.
  done.
Qed.

(**
## ``Poly`` 係数のリストから作る
*)
Print Poly. (* = fun R : semiRingType => foldr (cons_poly (R:=R)) 0%:P *)
Definition tstp3 := Poly [:: c; b; a].

(**
つぎのふたつの補題の結論は同じに見えるが、両辺の型が違う。

``val (Poly s)`` と ``Poly (val p)`` のvalが消えているのである。
*)
Check PolyK : forall (R : semiRingType) (c : R) (s : seq R),
    last c s != 0 -> Poly s = s :> seq R.

Check @polyseqK : forall (R : semiRingType) (p : {poly R}),
    Poly p = p :> {poly R}.

(**
Poly s からとりだしたリストと、もとのリストsの要素は同じ。
 
s が [:: 0] の場合、 Poly s が、0多項式になるが、[::]`_i は 0 になる（左辺）。
[:: 0]`_i も 0 である（右辺）ため、係数としては同じである。
*)
Check coef_Poly : forall (R : semiRingType) (s : seq R) (i : nat), (Poly s)`_i = s`_i.

(**
## ``\poly_(i < n) E`` 係数の無限列（生成関数）と範囲から作る
*)
Locate "\poly_ ( i < n ) E".  (* := (poly n (fun i => E)) : ring_scope *)
Print poly.         (* 略 *)    (* 小文字の poly は使うことはない？ *)

Check fun (n : nat) (E : nat -> R) => poly n E.
Check fun (n : nat) (E : nat -> R) => Poly (mkseq E n).

Definition tstE (n : nat) :=
  match n with
  | 0 => c
  | 1 => b
  | _ => a
  end.
Definition tstp4 := \poly_(i < 3) (tstE i).

(**
\poly_ で定義した多項式の値（リスト）は、mkseq と同じ。seq R の eq で比較。
ただし、生成関数 E の最後の値が0でないこと。
*)
Check polyseq_poly
  : forall (R : semiRingType) (n : nat) (E : nat -> R),
    E n.-1 != 0 -> \val (\poly_(i < n) E i) = mkseq E n :> seq R.
(**
polyseq_poly は、前出の coef_Poly と同じことを言っていて、
poly全体で比較するか、係数で比較するかの違いである。
 *)

(**
\poly_ で作った多項式の係数は、生成関数 E の値に等しい。ただし、k が n 未満の場合。
左辺の場合、k が n 以上なら、自動的に0だが、右辺は場合分けで0にする。
*)
Check coef_poly  : forall (R : semiRingType) (n : nat) (E : nat -> R) (k : nat),
    (\poly_(i < n) E i)`_k = (if (k < n)%N then E k else 0).

(**
\poly_ で作った多項式の最高次数の係数は、生成関数の E(n - 1)
ただし、n は 0 ではないこと。0 なら、生成関数は無視される。
ただし、E(n - 1) は 0 でないこと。0 なら、最高次数は E(n - 2) になってしまう。
*)
Check lead_coef_poly
  : forall (R : semiRingType) (n : nat) (E : nat -> R),
    (0 < n)%N -> E n.-1 != 0 -> lead_coef (\poly_(i < n) E i) = E n.-1.

(*(
多項式pから係数をとりだす関数を生成関数とすると、\poly_でできた多項式は p に等しい。
 *)
Check coefK : forall (R : semiRingType) (p : {poly R}), \poly_(i < size p) p`_i = p :> {poly R}.

(**
# nmodType

以下の補題で Nmoduleのインスタンスにすることができる。
*)
Check [eta @add_polyA R] : forall x y z : {poly R}, add_poly x (add_poly y z) = add_poly (add_poly x y) z.
Check [eta @add_polyC R] : forall x y : {poly R}, add_poly x y = add_poly y x.
Check [eta @add_poly0 R] : forall x : {poly R}, add_poly 0%:P x = x.

Check {poly R} : nmodType.

(**
## 0多項式についての補題

nmodTypeのインスタンスにすることで、0多項式（左辺）が、多項式環の0（右辺）の意味を持つことになる。
*)
Check polyC0 : forall R : semiRingType, 0%:P = 0 :> {poly R}.

(**
## 加算についての補題

多項式の加算ができるようになる。
 *)
(**
多項式の加算の係数は、多項式の係数どうしの加算と同じである。
*)
Check coefD : forall (R : semiRingType) (p q : {poly R}) (i : nat), (p + q)`_i = p`_i + q`_i.

(**
加算結果から作った定数多項式は、定数多項式の加算結果に等しい。
 *)
Check polyCD : forall R : semiRingType, {morph polyC : a b / a + b >-> a + b}.
Check polyCD : forall (R : semiRingType) (a b : R), (a + b)%:P = a%:P + b%:P.

(**
# semiRingType

以下の補題で、SemiRingのインスタンスにすることができる。
*)
Check [eta @mul_polyA R] : forall x y z : {poly R}, mul_poly x (mul_poly y z) = mul_poly (mul_poly x y) z.
Check [eta @mul_1poly R] : forall x : {poly R}, mul_poly 1%:P x = x.
Check [eta @mul_poly1 R] : forall x : {poly R}, mul_poly x 1%:P = x.
Check [eta @mul_polyDl R] : forall x y z : {poly R}, mul_poly (x + y) z = mul_poly x z + mul_poly y z.
Check [eta @mul_polyDr R] : forall x y z : {poly R}, mul_poly x (y + z) = mul_poly x y + mul_poly x z.
Check [eta @mul_0poly R] : forall x : {poly R}, mul_poly 0%:P x = 0%:P.
Check [eta @mul_poly0 R] : forall x : {poly R}, mul_poly x 0%:P = 0%:P.
Check poly1_neq0 R : 1%:P != 0.

Check {poly R} : semiRingType.

(**
## 1多項式についての補題

semiRingTypeのインスタンスにすることで、1多項式（左辺）が、多項式環の1（右辺）の意味を持つことになる。
*)
Check polyC1 : forall R : semiRingType, 1%:P = 1 :> {poly R}.

(**
## 積算についての補題

多項式の積算ができるようになる。
 *)
Check coefM  : forall (R : semiRingType) (p q : {poly R}) (i : nat),
    (p * q)`_i = \sum_(j < i.+1) p`_j * q`_(i - j).

Check coefMr : forall (R : semiRingType) (p q : {poly R}) (i : nat),
    (p * q)`_i = \sum_(j < i.+1) p`_(i - j) * q`_j.

(**
積算結果から作った定数多項式は、定数多項式の積算結果に等しい。
 *)
Check polyCM : forall R : semiRingType, {morph polyC : a b / a * b >-> a * b}.
Check polyCM : forall (R : semiRingType) (a b : R), (a * b)%:P = a%:P * b%:P.

(**
# zmodType

以下の補題で、NmoduleのインスタンスからZmoduleのインスタンスにすることができる。
 *)
Check [eta @add_polyN R] : forall x : {poly R}, add_poly (opp_poly x) x = 0%:P.

Check {poly R} : zmodType.

(**
## 負号についての補題

zmodTypeのインスタンスにすることで、係数の負（左辺）が、多項式環の負（右辺）の意味を持つことになる。
 *)
Check coefN : forall (R : ringType) (p : {poly R}) (i : nat), (- p)`_i = - p`_i.

(**
## 減算についての補題

多項式の減算ができるようになる。
*)
Check coefB  : forall (R : ringType) (p q : {poly R}) (i : nat), (p - q)`_i = p`_i - q`_i.

Check polyCN : forall R : ringType, {morph polyC : c / - c >-> - c}.
Check polyCN : forall (R : ringType) (c : R), (- c)%:P = - c%:P.

Check polyCB : forall R : ringType, {morph polyC : a b / a - b >-> a - b}.
Check polyCB : forall (R : ringType) (a b : R), (a - b)%:P = a%:P - b%:P.

(**
# ringType

以下の補題で、Ringのインスタンスにすることができる。``coefp 0`` は定数項を取り出す関数。
*)
Check [eta coefp0_multiplicative] : forall x : ringType, multiplicative (coefp 0).
Print GRing.multiplicative.
(* = fun (R S : semiRingType) (f : R -> S) =>
   ({morph f : x y / (x * y)%R >-> (x * y)%R} * (f 1 = 1))%type *)

Check forall f x y, {morph f : x y / (x * y)%R >-> (x * y)%R} * (f 1 = 1)%type.
(* 以下の意味である。 *)
Check forall f x y, (f (x * y)%R = (f x * f y)%R)            /\ (f 1 = 1)%type.

(* （ここで、ほんとうに ringなのか、よくわからない） *)
Check {poly R} : ringType.

(**
# lmodType R と lalgType R
*)
Check {poly R} : lmodType R.
Check {poly R} : lalgType R.

(**
R と {poly R} の掛け算のscaleが使えるようになる。
*)
Locate "_ *: _". (* := (GRing.scale a m) : ring_scope (default interpretation) *)
Check @mul_polyC R : forall (a : R) (p : {poly R}), a%:P * p = a *: p.

(**
まだ習っていない ``%:A``。
*)
Locate "_ %:A". (* := (GRing.scale k (GRing.one _)) : ring_scope (default interpretation) *)
Check @alg_polyC R : forall (a : R), a%:A = a%:P :> {poly R}.

(**
# ``'X`` とその補題

x についての多項式における、1次の x のこと。
ただし、すでに多項式型なので、係数(R型)ととの足し算や掛け算はできない。
 *)
Locate "'X".  (* := (polyX _) : ring_scope (default interpretation) *)
Check polyX R : {poly R}.
Print polyX_def.            (* = fun R : ringType => Poly [:: 0; 1] *)

(* polyseqなんとかシーリス *)
Check polyseqX : forall R : ringType, 'X = [:: 0; 1] :> seq R.

(**
’X に p を掛けたときの係数
*)
Check coefXM
  : forall (R : ringType) (p : {poly R}) (i : nat), ('X * p)`_i = (if i == 0%N then 0 else p`_i.-1).

(* n次の x^n *)
Locate "'X^ n". (* := (GRing.exp (polyX _) n) : ring_scope (default interpretation) *) 

Check polyseqXn : forall (R : ringType) (n : nat), 'X^n = rcons (nseq n 0) 1 :> seq R.

(**
’X^n に p を掛けたときの係数
*)
Check coefXnM : forall (R : ringType) (n : nat) (p : {poly R}) (i : nat),
    ('X^n * p)`_i = (if (i < n)%N then 0 else p`_(i - n)).

(**
なぜか、用意されていない補題
*)
Lemma X0_1 : 'X^0 = 1 :> {poly R}.
Proof. done. Qed.

Definition tstp5 := a *: 'X^2 + b *: 'X + c *: 'X^0.
Definition tstp6 := a%:P * 'X^2 + b%:P * 'X + c%:P.

(**
## poly_ind 帰納法

- 0多項式で成り立つ。
- 多項式``p``で成り立つとして、任意の係数cで ``p + 'X * c`` で成り立つ。
ならば、任意の多項式``p``で成り立つ。
 *)
Check poly_ind
  : forall (R : ringType) (K : {poly R} -> Type),
    K 0
    -> (forall (p : {poly R}) (c : R), K p -> K (p * 'X + c%:P))
    -> forall p : {poly R}, K p.

(**
## \poly_ と \sum_ の関係

生成関数Eのとき、``E i`` が ``E i :* 'X^i`` に対応する。
*)
Check @poly_def R
  : forall (n : nat) (E : nat -> R), \poly_(i < n) (E i) = \sum_(i < n) (E i *: 'X^i).

(**
# Monic (最高次の係数が1の多項式)
*)
Print monic.   (* = fun R : ringType => [ qualify p | monic_pred p] *)
Print monic_pred. (* = fun (R : ringType) (p : {poly R}) => lead_coef p == 1 *)

(**
定義とおなじ補題
*)
Check @monicE R : forall p : {poly R}, (p \is monic) = (lead_coef p == 1).
Check @monicP R : forall p : {poly R}, reflect (lead_coef p = 1) (p \is monic).

(**
mulr で閉じている。
*)
Check @rpred1M R : forall S : mulrClosed R, mulr_closed S.
(**
この補題で以下のインスタンスにできる。
*)
Check @monic_mulr_closed R : mulr_closed monic.
HB.about GRing.isMulClosed.

(**
# Horner評価法の定義とその補題

多項式pをパラメータxで評価する。
*)
Locate "p .[ x ]". (* := (horner p x) : ring_scope (default interpretation) *)
Print horner. (* = fun (R : ringType) (p : {poly R}) => horner_rec p *)
Print horner_rec.                           (* 略 *)

Check @horner_Poly R
  : forall (s : seq R) (x : R), (Poly s).[x] = horner_rec s x.

(**
## 多項式の係数とパラメータxが可換であること、パラメータxの評価結果とパラメータxが可換であること
*)
Print comm_coef. (* = fun (R : ringType) (p : {poly R}) (x : R) => forall i : nat, p`_i * x = x * p`_i *)
Print comm_poly. (* = fun (R : ringType) (p : {poly R}) (x : R) => x * p.[x] = p.[x] * x *)
Check @comm_coef_poly R : forall (p : {poly R}) (x : R), comm_coef p x -> comm_poly p x.

(**
## Horner評価法の補題
 *)
(**
定数多項式aに多項式pを掛けたものを、パラメータxで評価したものは、
定数aに、多項式pをパラメータxで評価したものに等しい。証明には poly_ind を使う。
*)
Check @hornerCM R : forall (a : R) (p : {poly R}) (x : R), (a%:P * p).[x] = a * (p.[x]).

(**
多項式pと多項式qの積をパラメータxで評価したものは、
多項式pをパラメータxで評価したものと、多項式qをパラメータxで評価したものの積に等しい。
証明には poly_ind を使う。
 *)
Check @hornerM_comm R : forall (p q : {poly R}) (x : R),
    comm_poly q x -> (p * q).[x] = p.[x] * q.[x].

Check @horner_poly R
  : forall (n : nat) (E : nat -> R) (x : R), (\poly_(i < n) (E i)).[x] = \sum_(i < n) (E i * x ^+ i).

(**
## hornerE と hornerE_comm - マルチルール
*)
Check hornerE.
Check (hornerD, hornerN, hornerX, hornerC, horner_exp,
        Monoid.simpm, hornerCM, hornerZ, hornerM, horner_cons). (* simp := Monoid.simpm *)

Check hornerE_comm.
Check (hornerD, hornerN, hornerX, hornerC, horner_cons,
        Monoid.simpm, hornerCM, hornerZ,
        (fun p x => hornerM_comm p (comm_polyX x))).

(**
# rootの定義とその補題

多項式pを適当なxで評価して、値が0になること。
*)
Print root. (* = fun (R : ringType) (p : {poly R}) (x : R) => p.[x] == 0
 *)
(**
``x \in root p`` は ``root p x`` と同じ。ただし、マルチルール``inE``に含まれないことに注意。
*)
Check @mem_root R : forall (p : {poly R}) (x : R), (x \in root p) = (p.[x] == 0).
Check @mem_root R : forall (p : {poly R}) (x : R), root p x = (p.[x] == 0).

Check @rootE R : forall (p : {poly R}) (x : R), (root p x = (p.[x] == 0)) * ((x \in root p) = (p.[x] == 0)).
Check @rootP R : forall (p : {poly R}) (x : R), reflect (p.[x] = 0) (root p x).

(**
## 因数定理

任意の多項式``p``に対して、
``p = q * (X - a)`` なる多項式``q``が存在すること、と、
方程式``p = 0``の解が``a``であることは、同値である。
*)
Check @factor_theorem R
  : forall (p : {poly R}) (a : R), reflect (exists q : {poly R}, p = q * ('X - a%:P)) (root p a).

(**
poly.v に近いかたち
*)
Goal (forall (p : {poly R}) (a : R), reflect (exists q : {poly R}, p = q * ('X - a%:P)) (root p a)).
Proof.
  move=> p a.
  apply: (iffP eqP) => [pa0 | [q ->]]; last first.
  - rewrite hornerM_comm /comm_poly hornerXsubC subrr ?simp.
    + by rewrite mulr0.
    + by rewrite mulr0 mul0r.
  - exists (\poly_(i < size p) horner_rec (drop i.+1 p) a).
    apply/polyP=> i; rewrite mulrBr coefB coefMX coefMC !coef_poly.
    apply: canRL (addrK _) _; rewrite addrC; have [le_p_i | lt_i_p] := leqP.
    + rewrite nth_default // Monoid.simpm drop_oversize ?if_same //.
      * by rewrite mul0r.
      * exact: leq_trans (leqSpred _).
    + case: i => [|i] in lt_i_p *; last by rewrite ltnW // (drop_nth 0 lt_i_p).
      by rewrite drop1 /= -{}pa0 /horner; case: (p : seq R) lt_i_p.
Qed.

Goal (forall (p : {poly R}) (a : R), reflect (exists q : {poly R}, p = q * ('X - a%:P)) (root p a)).
Proof.
  move=> p a.
  apply: (iffP eqP) => [pa0 | [q ->]].
  - exists (\poly_(i < size p) (horner_rec (drop i.+1 p) a)).

    Check polyP : forall (R : semiRingType) (p q : {poly R}), nth 0 p =1 nth 0 q <-> p = q.
    apply/polyP => i.
    
    rewrite mulrBr.
    rewrite coefB.
    rewrite coefMX.
    rewrite coefMC.
    
    Check coef_poly : forall (R : semiRingType) (n : nat) (E : nat -> R) (k : nat),
        (\poly_(i < n) E i)`_k = (if (k < n)%N then E k else 0).
    rewrite 2!coef_poly.
    
    apply: canRL (addrK _) _.
    rewrite addrC.
    
    have := leqP.
    case=> [le_p_i | lt_i_p].

    (* le_p_i : (size p <= i)%N の場合 *)
    + rewrite nth_default //.

      Check Monoid.simpm.                   (* マルチルール *)
      rewrite Monoid.simpm.
      
      rewrite drop_oversize.
      * rewrite 2!if_same //.
        by rewrite mul0r.
      * exact: leq_trans (leqSpred _).
        
    (* lt_i_p : (i < size p)%N の場合 *)
    + case: i lt_i_p => [| i] lt_i_p.
      * rewrite drop1 /= -{}pa0 /horner.
        case: (p : seq R) lt_i_p.
        ** done.
        ** rewrite /=.
           done.
      * rewrite ltnW.
        ** rewrite //.
           rewrite (drop_nth 0 lt_i_p).
           done.
        ** done.
  - rewrite hornerM_comm.
    + rewrite hornerXsubC.
      rewrite subrr.
      rewrite mulr0.
      done.
    + rewrite /comm_poly.
      rewrite hornerXsubC.
      rewrite subrr.
      rewrite mulr0 mul0r.
      done.
Qed.


(**
## 代数学の基本定理

任意の整数係数(idomain)の多項式``p``（ただし 0 でない）の重解を除いた解の数は、``p``の次数以下である。
ただし、``p``の係数のサイズ``(size p)``は、次数(degree)+1 である。

因数定理とmonic についての補題を使用する。
 *)
Check @max_poly_roots
  : forall (R : idomainType) (p : {poly R}) (rs : seq R),
    p != 0 -> all (root p) rs -> uniq rs -> (size rs < size p)%N.

(**
poly.v に近いかたち
*)
Goal forall (R : idomainType) (p : {poly R}) (rs : seq R),
    p != 0 -> all (root p) rs -> uniq rs -> (size rs < size p)%N.
Proof.
  move=> R p rs.
  elim: rs p => [p pn0 _ _ | r rs ihrs p pn0] /=.
  - by rewrite size_poly_gt0.
  - case/andP => rpr arrs /andP [rnrs urs]; case/factor_theorem: rpr => q epq.
    have [q0 | ?] := eqVneq q 0.
    + by move: pn0; rewrite epq q0 mul0r eqxx.
    + have -> : size p = (size q).+1 by rewrite epq size_Mmonic ?monicXsubC // size_XsubC addnC.
      suff /eq_in_all h : {in rs, root q =1 root p} by apply: ihrs => //; rewrite h.
      move=> x xrs; rewrite epq rootM root_XsubC orbC; case: (eqVneq x r) => // exr.
      by move: rnrs; rewrite -exr xrs.
Qed.

(**
直観的な証明：
解のリストrsについての帰納法で考える。

- rs が nil の場合は、``size [::] < size p`` で明らか。
- rs が (r :: rs') の場合は、

  ``all (root p) (r :: rs') -> uniq (r :: rs') -> (size (r :: rs') < size p)``

  から、次のゴールを得る。ただし、``uniq (r :: rs') == r \notin rs' && uniq rs'`` を使う。

  ``all (root p) rs'        -> uniq rs'        -> (size rs').+1 < size p)``

  また、因数定理から、``p = q * ('X - r%:P)`` である。

  - ``q = 0`` なら、``p = q * ('X - r%:P)`` から ``p = 0`` になるから前提矛盾である。
  - ``q != 0`` として、
        ``p = q * ('X - r%:P)`` から、``H1 : size p = (size q).+1``
        ``r \notin rs'``        から、``H2 : all (root q) rs' = all (root p) rs'``
    帰納法の仮定から ``IHrs : all (root p) rs' -> uniq rs' -> (size rs' < size p)``
    
    H1, H2, IHrs から、上記のゴールが証明できる。
*)
Goal forall (R : idomainType) (p : {poly R}) (rs : seq R),
    p != 0 -> all (root p) rs -> uniq rs -> (size rs < size p)%N.
Proof.
  move=> R p rs.
  elim: rs p => [p pn0 _ _ | r rs' IHrs p pn0].

  (* 0 でない多項式のサイズは 0 より大きい。 *)
  Check size_poly_gt0 : forall (R : semiRingType) (p : {poly R}), (0 < size p)%N = (p != 0).
  - by rewrite size_poly_gt0.
    
    Check all (root p) (r :: rs') -> uniq (r :: rs') -> (size (r :: rs') < size p)%N.
  - rewrite /=.
    (* ``r :: rs`` が分解され、r \notin rs になる。 *)
    Check all (root p) (r :: rs') -> uniq (r :: rs') -> (size (r :: rs') < size p)%N.

    case/andP => rpr arrs' /andP [rnrs' urs'].
    
    (* rpr に因数定理を適用して、epq に変換する。 *)
    Check factor_theorem
      : forall (R : ringType) (p : {poly R}) (a : R),
        reflect (exists q : {poly R}, p = q * ('X - a%:P)) (root p a).
    case/factor_theorem: rpr => q epq.
    (* 「p の解が r である」を「pが(X - r) と q の積である」に言い換える。 *)
    
    Check eqVneq q 0 : eq_xor_neq q 0 (0 == q) (q == 0).
    have [q0 | qn0] := eqVneq q 0. (* q = 0 と q != 0 に条件分けする。  *)
    (* q = 0 の場合*)
    + move: pn0.
      by rewrite epq q0 mul0r eqxx.         (* epq で書き換える。 *)
      
    (* q != 0 の場合 *)
      (* H1 *)
      (* p と (p の因数である) q の次数が一つ違いであることを証明する。 *)
      (* monic についての補題を使用する。 *)
      Check size_Mmonic                     (* monic の掛け算 *)
        : forall (R : ringType) (p q : {poly R}),
          p != 0 -> q \is monic -> size (p * q) = (size p + size q).-1.
      Check monicXsubC : forall (R : ringType) (c : R), 'X - c%:P \is monic.
    + have H1 : size p = (size q).+1
        by rewrite epq size_Mmonic ?monicXsubC // size_XsubC addnC.

      (* H2 *)
      (* q の全解がrs'であることと、pの全解がrs'であることは同値である。 *)
      (* この rs' は、r についての帰納法におけるseqの残りの部分である。 *)
      (* uniq (r :: rs') から、rs' に r は含まれないことに注意！！ *)
      have H2 : {in rs', root q =1 root p}.
      {
        move=> x xrs'.
        Check root q x = root p x.
        rewrite epq rootM root_XsubC orbC.    (* epq で書き換える。 *)
        
        case: (eqVneq x r) => exr.            (* x = r と x != r に条件分けする。 *)
        (* x = r の場合 *)
        * move: rnrs'.
          by rewrite -exr xrs'.
        (* x != r の場合 *)
        * done.
      }.
      move/eq_in_all in H2.
      (* H2 : all (root q) rs' = all (root p) rs' ... H2をわかりやすく書き換えたもの。 *)
      (* H1 : size p = (size q).+1 *)

      rewrite H1.
      apply: IHrs => //=.
      rewrite H2.
      done.
Qed.

(**
# 補足説明
*)

(**
## 自明である
*)
Goal (poly_nil R)`_0 = 0.
Proof.
  done.
Qed.

Goal forall i, (poly_nil R)`_i = 0.
Proof.
  by elim.
Qed.

(**
## モノイドのマルチルール (see. bigop.v)
*)
Check Monoid.simpm.
Check (Monoid.mulm1, Monoid.mulm0, Monoid.mul1m, Monoid.mul0m, Monoid.mulmA).

(**
# 多項式の定義の間の相互変換
 *)
Check neqa0 : a != 0.
Check neq0_last_s : a != 0 -> last 1 [:: c; b; a] != 0.
Print tstE.                                 (* 略 *)

Print tstp1.                  (* = Polynomial (neq0_last_s neqa0) *)
Print tstp2.                  (* = insubd (poly_nil R) [:: c; b; a] *)
Print tstp3.                  (* = Poly [:: c; b; a] *)
Print tstp4.                  (* = \poly_(i < 3) tstE i *)
Print tstp5.                  (* = a *: 'X^2 + b *: 'X + c%:P *)
Print tstp6.                  (* = a%:P * 'X^2 + b%:P * 'X + c%:P *)

(**
## polyP を使う

polyP は poly_inj で証明できる。
*)
Check polyP : forall (R : semiRingType) (p q : {poly R}), nth 0 p =1 nth 0 q <-> p = q :> {poly R}.
Check [eta @poly_inj R] : forall p q : {poly R}, p = q :> seq R -> p = q :> {poly R}.

Goal tstp3 = tstp4 :> {poly R}.
Proof.
  rewrite /tstp3 /tstp4.
  Check Poly [:: c; b; a] = \poly_(i < 3) tstE i :> {poly R}.
  apply/polyP => i.                         (* 係数毎 *)
  rewrite coefE.                            (* マルチルール *)
  rewrite polyseq_poly //=.
  by rewrite /= neqa0.
Qed.

Goal tstp1 = tstp2 :> {poly R}.
Proof.
  rewrite /tstp1 /tstp2.
  Check Polynomial (neq0_last_s neqa0) = insubd (poly_nil R) [:: c; b; a] :> {poly R}.
  apply/polyP => i.                         (* 係数毎 *)
  rewrite /= val_insubd.
  case: ifP => //=.
  by rewrite neqa0.
Qed.

Goal tstp1 = tstp3 :> {poly R}.
Proof.
  rewrite /tstp1 /tstp3.
  Check Polynomial (neq0_last_s neqa0) = Poly [:: c; b; a] :> {poly R}.
  apply/polyP => i.                         (* 係数毎 *)
  by rewrite coefE.                         (* マルチルール *)
Qed.

Goal tstp3 = tstp6 :> {poly R}.
Proof.
  rewrite /tstp3 /tstp6.
  Check Poly [:: c; b; a] = a%:P * 'X^2 + b%:P * 'X + c%:P :> {poly R}.
  apply/polyP => i.                         (* 係数毎 *)
  rewrite /=.
  rewrite !cons_poly_def.
  rewrite mul0r add0r expr2.
  rewrite mulrDl mulrA.
  done.
Qed.

(**
## mulr (``*``)  と scale ``*:`` の間の相互変換を使う
 *)
Goal tstp5 = tstp6 :> {poly R}.
Proof.
  rewrite /tstp5 /tstp6.
  Check a *: 'X^2 + b *: 'X + c *: 'X^0 = a%:P * 'X^2 + b%:P * 'X + c%:P :> {poly R}.
  
  Check mul_polyC : forall (R : ringType) (a : R) (p : {poly R}), a%:P * p = a *: p.
  rewrite -3!mul_polyC.
  
  Check X0_1 : 'X^0 = 1.
  rewrite X0_1 mulr1.
  done.
Qed.

(**
*** 以下は参考である。 ****

## 多項式の定義の間の相互変換 (eq_irrelevance を使う)

``_ = _ :> seq R`` と `` _ = _ :> {poly R}`` の相互変換を使う
 *)

(* 多項式として等しいならseqとして等しい。*)
Lemma poly_seq (p q : {poly R}) : p = q :> {poly R} -> p = q :> seq R.
Proof.
  move=> H.
  (* Goal の両辺には、コアーションで val がついているから、rewrite で済む。 *)
  (* Goal *) Check val p = val q :> seq R.
  by rewrite H.
Qed.

(* seqとして等しいなら、多項式として等しい。 *)
(* poly_inj があれば seq_poly はいらない。同じ意味であるため *)
(* polyP は poly_inj で証明されている。 *)
Lemma seq_poly (p q : {poly R}) : p = q :> seq R -> p = q :> {poly R}.
Proof.
  case: p; case: q.
  move=> p Hp q Hq /= H.

(**
``p = q`` から ``Hp = Hq`` であることを示したいが、
*)
  subst.
(**
同じ命題 ``last 1 p != 0`` の証明だからといって、一般に、それが等しいとは言えない。
*)
  Check eq_irrelevance : forall (T : eqType) (x y : T) (e1 e2 : x = y), e1 = e2.
(**
しかし、これは boolean の命題なので、等しいと言える。
*)
  rewrite (eq_irrelevance Hp Hq).
  done.  
Qed.  

Goal tstp3 = tstp4 :> {poly R}.
Proof.
  rewrite /tstp3 /tstp4.
  (* Goal *) Check Poly [:: c; b; a] = \poly_(i < 3) (tstE i) :> {poly R}.
  
  Check @PolyK R a [:: c; b; a] : last a [:: c; b; a] != 0 -> Poly [:: c; b; a] = [:: c; b; a] :> seq R.
  Check @polyseq_poly R 3 tstE : tstE 3.-1 != 0 -> \poly_(i < 3) tstE i = mkseq [eta tstE] 3 :> seq R.
(**
どちらも ``_ = _ :> seq R`` の補題なので、使えない。
 *)
  Fail rewrite (@PolyK R a [:: c; b; a]).  
  Fail rewrite (@polyseq_poly R 3 tstE).

  apply: seq_poly.
  (* Goal *) Check Poly [:: c; b; a] = \poly_(i < 3) (tstE i) :> seq R.
(**
ゴールの両辺を ``_ = _ :> seq R`` に変換できたので、使える。
*)
  rewrite (@PolyK R a [:: c; b; a]).  
  rewrite (@polyseq_poly R 3 tstE).
  
  - done.
  - by rewrite /= neqa0.
  - by rewrite /= neqa0.
Qed.

Goal tstp1 = tstp2 :> {poly R}.
Proof.
  rewrite /tstp1 /tstp2.
  rewrite /=.                               (* なにも起きない。 *)
  apply: seq_poly.
  rewrite /= val_insubd.
  case: ifP => //=.
  by rewrite neqa0.                         (* 前提矛盾 *)
Qed.

Goal tstp1 = tstp3 :> {poly R}.
Proof.
  rewrite /tstp1 /tstp3.
  apply: seq_poly.
  rewrite /=.
  rewrite (@PolyK R a [:: c; b; a]) //=.
  by rewrite neqa0.
Qed.

Goal tstp3 = tstp6 :> {poly R}.
  rewrite /tstp3 /tstp6.
  apply: seq_poly.
  rewrite /=.
  rewrite !cons_poly_def.
  rewrite mul0r add0r expr2.
  rewrite mulrDl mulrA.
  done.
Qed.  

(* END *)
