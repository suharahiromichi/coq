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
# コンストラクタ
## seqのサブタイプと、0多項式
*)

(**
## ```_i`` の定義と補題
*)

(**
# 定数多項式とその補題
 *)


(**
# 多項式の作り方
## cons_poly の定義と補題
*)

(**
## ``Poly`` 係数のリストから作る
*)

(**
## ``\poly_(i < n) E`` 係数の無限列（生成関数）と範囲から作る
*)

(**
# nmodType
*)

(**
## 0多項式についての補題
*)

(**
## 加算についての補題
*)


(**
# semiRingType
*)

(**
## 1多項式についての補題
 *)

(**
## 積算についての補題
 *)


(**
# zmodType
*)

(**
## 引算についての補題
*)

(**
# ringType
*)

(**
# lmodType
*)

(**
## Linier についての補題
*)

(**
# ``'X`` とその補題

## poly_ind 帰納法
 *)

(**
# Monic (最高次の係数が1の多項式)
*)

(**
# Horner評価法の定義とその補題
*)

(**
# rootの定義とその補題
*)

(**
## 因数定理
*)


(**
コンストラクタにおいて、最大次数の係数が 0 でないことを
 *)
Check fun s => last 1 s != 0.
(**
でチェックしている。この``1``は``0``でなければなんでも良い数である。
ベース型であるリストの``[::]``が``1``を意味するとは言っていない。
 *)

(**
- ``0%:P``が``[::]``になるのは、polyC の定義で insubd の代替項が、poly_nil であること。
もともとの poly_nil 自体には``0``の意味はないことに注意するべきである。
*)
Print polyC. (* = fun (R : semiRingType) (c : R) => insubd (poly_nil R) [:: c] *)

(**
- ``[::]`_i``が0になるのは、```_i``の定義で、nth の代替項が、0%R であること。
 *)
Locate "s `_ i". (* Notation "s `_ i" := (nth GRing.zero s i) : ring_scope (default interpretation) *)






Section TypeClasses.

  Section Polynomial.
    Variable R : semiRingType.

    Check {poly R} : choiceType.
  End Polynomial.

  Section SemiPolynomialTheory.
    Variable R : semiRingType.
    Implicit Types (a b c x y z : R) (p q r d : {poly R}).

    Check {poly R} : nmodType.
    Check {poly R} : semiRingType.

  End SemiPolynomialTheory.

  Section PolynomialTheory.
    Variable R : ringType.
    Implicit Types (a b c x y z : R) (p q r d : {poly R}).

    Check {poly R} : zmodType.
    
  End PolynomialTheory.
  
  Section PolynomialComRing.
    Variable R : comRingType.
    Implicit Types p q : {poly R}.

    Check {poly R} : comRingType.
    
  End PolynomialComRing.

  Section PolynomialIdomain.
    (* Integral domain structure on poly *)
    Variable R : idomainType.
    Implicit Types (a b x y : R) (p q r m : {poly R}).

    Check {poly R} : idomainType.
    
  End PolynomialIdomain.

End TypeClasses.

Check coef0.

Variable R : ringType.

Print nseq.
Print ncons.

Compute ncons 1%N true [::].

Print nseq.

Compute (fun c => nseq (c != 0)%N c) 0.     (* [::] *)
Compute (fun c => nseq (c != 0)%N c) 1.     (* [:: 1] *)
Compute (fun c => nseq (c != 0)%N c) 2.     (* [:: 2] *)

Compute nseq true 0.


Goal (poly_nil R)`_0 = 0.
Proof.
  rewrite /poly_nil.
  rewrite /oner_neq0.
  rewrite /GRing.oner_neq0.

Goal (0 : {poly R})`_0 = 0.
Proof.
  simpl.
  rewrite /polyseq.


Lemma coef0 i : (0 : {poly R})`_i = 0.
Proof.
  Check (0 : {poly R})`_i = 0 :> R.
  Set Printing All.
  





Section Polynomial.

Variable R : semiRingType.
Variable a b c d : R.

(**
-------------------------------
# 多項式のコンストラクタ

Defines a polynomial as a sequence with <> 0 last element

コンストラクタを直接使って多項式を作ることは、勧められない。
 *)
Definition neq0_last s := last 1 s != 0 :> R.
Check oner_neq0 : forall s : semiRingType, 1 != 0.

(* 0 の多項式を作る。 *)
Check @Polynomial R [::] (oner_neq0 R) : polynomial R.
Print poly_nil.
Check @poly_nil R.

(* a X^2 + b X + c の多項式を作る。 *)
Definition tsts : seq R := [:: c; b; a].
Axiom neqa0 : a != 0 :> R.

Lemma neq0_last_s : neq0_last tsts.
Proof.
  by rewrite /neq0_last /tsts /= neqa0.
Qed.

Check @Polynomial R tsts neq0_last_s.
Check Polynomial neq0_last_s.

Definition tstp1 := Polynomial neq0_last_s.
Check tstp1 : polynomial R.
Check tstp1 : {poly R}. (* もう polynomial R の短縮形と思ってよい？ *)

(* 係数を取り出す。 *)
Compute tstp1`_2.                           (* a *)
Compute tstp1`_1.                           (* b *)
Compute tstp1`_0.                           (* c *)

(* poly から seq を取り出す関数 *)
Print polyseq.
Check [eta polyseq] : {poly R} -> seq R.

(**
HB.instance Definition _ := [isSub for polyseq].
HB.instance Definition _ := [Choice of polynomial by <:].
*)

End Polynomial.

(* We need to break off the section here to let the Bind Scope directives     *)
(* take effect.                                                               *)

Section SemiPolynomialTheory.

Variable R : semiRingType.
Variable (a b c x y z : R) (p q r d : {poly R}).

(* polyseq は単射である。 *)
Check @poly_inj R : forall p1 p2, polyseq p1 = polyseq p2 :> seq R -> p1 = p2 :> {poly R}.


(**
-------------------------------
# リストのサブタイプとしての多項式
*)
(* サブタイプの値からベースタイプの値を取り出す。 *)
(* サブタイプの値を作る。 *)
Check @insubd (seq R) neq0_last (polynomial R) (poly_nil R) tsts.
Check insubd (poly_nil R) tsts.
Definition tstp2 := insubd (poly_nil R) tsts.
Check tstp2 : {poly R}.

(* 最高次数の係数を取り出す。 *)
Compute lead_coef tstp1.                    (* a *)
Compute tstp1`_(size tstp1).-1.             (* a *)
Check lead_coefE : forall (R : semiRingType) (p : {poly R}), lead_coef p = p`_(size p).-1.

(* 定数多項式を作る *)
Check insubd (poly_nil R) [:: c] : {poly R}.
Check polyC c  : {poly R}.
Definition tstp_c := polyC c.

(* 引数に 0 が与えられる場合を考慮すると、[:: c] ではだめで、insubd で定義する必要がある。 *)
Check polyC 0  : {poly R}.
Definition tstp_c0 := @polyC R 0.

(**
----------------------------------
# 定数多項式についての補題
 *)
Compute nseq (42%N != 0) 42%N.              (* [:: 42] *)
Compute nseq  (0%N != 0) 0%N.               (* [::] *)

Lemma l_neq_false (x : R) : (x != x) = false.
Proof.
  by apply/eqP.
Qed.

Lemma l_eq_true (x : R) : (x == x).
Proof.
  by apply/eqP.
Qed.

(* 定数多項式からseqを取り出したものは、cが非零ならシングルトン、cが零なら空リスト *)
Check polyseqC c : c%:P = nseq (c != 0) c :> seq R.
(* これは、cが非0でも、0でも成り立つ。ただし、場合分けが要る。 *)
Goal c != 0 -> c%:P = [:: c] :> seq R.
Proof.
  rewrite polyseqC.
  move=> ->.
  done.
Qed.

Lemma zeroP_nil : 0%:P = [::] :> seq R.
Proof.
  rewrite polyseqC l_neq_false.
  done.
Qed.


(* 定数多項式のサイズは、cが非零なら1、cが零なら0 *)
Check size_polyC : forall (R : semiRingType) (c : R), size c%:P = (c != 0).
(* これは、cが非0でも、0でも成り立つ。ただし、場合分けが要る。 *)
Goal c != 0 -> size c%:P = 1.
Proof.
  rewrite size_polyC.
  move=> ->.
  done.
Qed.

Goal @size R 0%:P = 0.
Proof.
  rewrite size_polyC l_neq_false.
  done.
Qed.

(* 定数多項式の0次の係数が定数、1次の係数は0である。 *)
Check coefC : forall (R : semiRingType) (c : R) (i : nat), c%:P`_i = (if i == 0 then c else 0).
(* これは、cが非0でも、0でも成り立つ。ただし、場合分けも不要。 *)
Goal c%:P`_0 = c.
Proof.
  rewrite coefC /=.
  done.
Qed.

Goal c%:P`_1 = 0.
Proof.
  rewrite coefC /=.
  done.
Qed.

(* 定数多項式を作る関数と0次の係数を求める関数は、キャンセルの関係である。 *)
Check polyCK : cancel polyC (coefp 0).
Check [eta polyCK] c : coefp 0 c%:P = c.

(* 定数多項式をつくる関数 polyC は単射である。 *)
Check [eta polyC_inj] : forall x1 x2 : R, x1%:P = x2%:P :> {poly R} -> x1 = x2 :> R.

(* 定数多項式の最高次数の係数は、定数である。 *)
Check lead_coefC c : lead_coef c%:P = c.
(* 定数多項式を作る関数と最高次数の係数を求める関数は、キャンセルの関係である。 *)
Goal cancel polyC (@lead_coef R).
Proof.
  move=> c.
  by rewrite lead_coefC.
Qed.

(* 係数がすべて同じなら、多項式は同じ *)
Check polyP : forall (R : semiRingType) (p q : {poly R}), nth 0 p =1 nth 0 q <-> p = q :> {poly R}.
Goal tstp1 = tstp2 :> {poly R}.
Proof.
  apply/polyP.
  rewrite /tstp1 /tstp2 /= => i.
  rewrite insubdK //=.
  rewrite unfold_in.
  by apply: neq0_last_s.
Qed.  
(* リストとして比較するなら、この補題はいらない。 *)
Goal tstp1 = tstp2 :> seq R.
Proof.
  rewrite /tstp1 /tstp2.
  rewrite insubdK //=.
  rewrite unfold_in.
  by apply: neq0_last_s.
Qed.

(* サイズが1、0次の多項式、または0の多項式なら、0次の項を取り出して作った定数多項式は、同じ。 *)
Check size1_polyC : forall (R : semiRingType) (p : {poly R}), (size p <= 1)%N -> p = (p`_0)%:P :> {poly R}.
Goal c != 0 -> c%:P = (c%:P`_0)%:P :> {poly R}.
Proof.
  move=> H.
  apply: size1_polyC => //.
  by rewrite size_polyC H.
Qed.

Goal 0%:P = (0%:P`_0)%:P :> {poly R}.
Proof.
  apply: size1_polyC.
  by rewrite size_polyC l_neq_false.
Qed.

(**
-------------------------------
# extension (cons) で多項式を作る。
 *)
(* 係数となる定数と多項式から、あらたな多項式をつくる。 *)
Check cons_poly : forall R : semiRingType, R -> {poly R} -> {poly R}.

(* p が nil (0多項式) でないなら、cons_poly は、 p に c を cons したもの。
   p が nil (0多項式) なら、cons_poly は、 c の定数多項式。
   これは、seq R で比較する。
   ~~~~~~~~~~~~~~~~~~~~~~~~ *)
Check polyseq_cons : forall (R : semiRingType) (c : R) (p : {poly R}),
    cons_poly c p = (if ~~ nilp p then c :: p else c%:P) :> seq R.
Goal cons_poly d tstp1 = d :: tstp1 :> seq R.
Proof.
  rewrite polyseq_cons.
  done.
Qed.

Goal cons_poly d (poly_nil R) = d%:P :> seq R.
Proof.
  rewrite [LHS]polyseq_cons.
  done.
Qed.

(* p が nil (0多項式) なら、cons_poly のサイズは c が 0 かどうかで決まる。
   p が nil (0多項式) でないなら、cons_poly はサイズを 1 増やす。
 *)
Check size_cons_poly : forall (R : semiRingType) (c : R) (p : {poly R}),
    size (cons_poly c p) = (if nilp p && (c == 0) then 0 else (size p).+1).
Goal size (cons_poly d tstp1) = 4.
Proof.
  rewrite size_cons_poly /=.
  done.
Qed.

Goal d != 0 -> size (cons_poly d (poly_nil R)) = 1.
Proof.
  rewrite size_cons_poly /=.
  by case: ifP.
Qed.

Goal size (cons_poly 0 (poly_nil R)) = 0.
Proof.
  rewrite size_cons_poly /=.
  rewrite l_eq_true.
  done.
Qed.  

(* cons_poly した多項式の係数は、もとの係数のインデックスに-1したもの。 *)
Check coef_cons : forall (R : semiRingType) (c : R) (p : {poly R}) (i : nat),
    (cons_poly c p)`_i = (if i == 0 then c else p`_i.-1).

Goal (cons_poly d tstp1)`_1 = tstp1`_0.
Proof.
  rewrite coef_cons /=.
  done.
Qed.

Goal (cons_poly d tstp1)`_0 = d.
Proof.
  rewrite coef_cons /=.
  done.
Qed.
(* nil 多項式でも成り立つ。 *)
Goal (cons_poly d (poly_nil R))`_1 = (poly_nil R)`_0.
Proof.
  rewrite coef_cons /=.
  done.
Qed.

(**
-------------------------------
# 係数リストから多項式を作る。
*)
(* 受け取ったリストを順番に cons_poly していく。サブタイプの関係は使わない。 *)
Print Poly.
(**
fun R : semiRingType => foldr (cons_poly (R:=R)) 0%:P
     : forall R : semiRingType, seq R -> {poly R}
 *)
Definition tstp3 := Poly [:: c; b; a].

(* 最後の要素が0でないなら、Polyの結果はもとのリストとおなじ。 *)
Check PolyK : forall (R : semiRingType) (c : R) (s : seq R),
    last c s != 0 -> Poly s = s :> seq R.
Goal Poly [:: c; b; a] = [:: c; b; a] :> seq R.
Proof.
  Check @PolyK R a.
  rewrite (@PolyK R a). (* last c の c を与えないといけないが、大丈夫か？ *)
  - done.
  - rewrite neqa0.
  done.
Qed.

Goal size (Poly tsts) = 3.
Proof.
  Check size (val (Poly tsts)) = 3. (* size を取る前に、ベースタイプのリストが取り出されている。 *)
  rewrite (@PolyK R a).
  - Check size tsts = 3.                    (* リストの長さになる。 *)
    done.
  - by rewrite neqa0.
Qed.

(* 任意の多項式からベースタイプのリストを取り出し、それに Poly を適用すると、もとの多項式に戻る。 *)
Check @polyseqK : forall (R : semiRingType) (p : {poly R}), Poly p = p.
Check @polyseqK : forall (R : semiRingType) (p : {poly R}), Poly (val p) = p :> {poly R}.

Goal Poly tstp2 = tstp2 :> {poly R}.
Proof.
  rewrite polyseqK.
  Check tstp2 = tstp2 :> {poly R}.
  done.
Qed.

(* Poly s から取り出したリストのサイズは、sのサイズ以下である。 *)
Check size_Poly : forall (R : semiRingType) (s : seq R), (size (Poly s) <= size s)%N.
Check size_Poly : forall (R : semiRingType) (s : seq R), (size (\val (Poly s)) <= size s)%N.
(* 通常は等しいが、0多項式ならサイズは0である。*)
Goal size (\val (Poly [:: 0 : R; 0 : R])) = @size R [::] :> nat.
Proof.
  rewrite /= !polyseq_cons.
  case: ifP => /=.
  - by rewrite !zeroP_nil.                   (* 前提矛盾 *)
  - by rewrite !zeroP_nil.
Qed.

(* Poly s からとりだしたリストと、もとのリストsの要素は同じ。 *)
(* s が [:: 0] の場合、 Poly s が、0多項式になるが、[::]`_i は 0 になる（左辺）。
   [:: 0]`_i も 0 である（右辺）ため、係数としては同じである。 *)
Check coef_Poly : forall (R : semiRingType) (s : seq R) (i : nat), (Poly s)`_i = s`_i.

(**
# 無限の係数シーケンスと境界から多項式を作る
 *)
Locate "\poly_ ( i < n ) E".  (* (poly n (fun i => E)) : ring_scope *)
Check fun (n : nat) (E : nat -> R) => poly n E.    (* 小文字の poly は使うことはない。 *)
Check fun (n : nat) (E : nat -> R) => Poly (mkseq E n).

(* \poly_ で定義した多項式の値（リスト）は、mkseq と同じ。ただし、生成関数 E の最後の値が0でないこと。
   ほぼ、定義の両辺を seq R にしたもの。 *)
Check polyseq_poly
  : forall (R : semiRingType) (n : nat) (E : nat -> R),
    E n.-1 != 0 -> \val (\poly_(i < n) E i) = mkseq E n :> seq R.

Definition tstE (n : nat) :=
  match n with
  | 0 => c
  | 1 => b
  | _ => a
  end.

(* \poly_ で作った多項式の（ベースタイプのリスト）のサイズは、\poly_ の n 以下である。 *)
Check size_poly
  : forall (R : semiRingType) (n : nat) (E : nat -> R), (size (\poly_(i < n) E i) <= n)%N.

(* \poly_ で作った多項式の（ベースタイプのリスト）のサイズは、\poly_ の n に等しい。
   ただし、生成関数 E の最後の値が0でないとき。 *)
Check size_poly_eq : forall (R : semiRingType) (n : nat) (E : nat -> R),
    E n.-1 != 0 -> size (\poly_(i < n) E i) = n.

Goal size (\poly_(i < 3) tstE i) = 3.
Proof.
  rewrite size_poly_eq //=.
  rewrite neqa0.
  done.
Qed.

(* \poly_ で作った多項式の係数は、生成関数 E の値に等しい。ただし、k が n 未満の場合。
 左辺の場合、k が n 以上なら、自動的に0だが、右辺は場合分けで0にする。 *)
Check coef_poly
  : forall (R : semiRingType) (n : nat) (E : nat -> R) (k : nat),
    (\poly_(i < n) E i)`_k = (if (k < n)%N then E k else 0).

(* \poly_ で作った多項式の最高次数の係数は、生成関数の E(n - 1) *)
(* ただし、n は 0 ではないこと。0 なら、生成関数は無視される。 *)
(* ただし、E(n - 1) は 0 でないこと。0 なら、最高次数は E(n - 2) になってしまう。 *)
Check lead_coef_poly
  : forall (R : semiRingType) (n : nat) (E : nat -> R),
    (0 < n)%N -> E n.-1 != 0 -> lead_coef (\poly_(i < n) E i) = E n.-1.

(* 多項式pから係数をとりだす関数を生成関数とすると、\poly_でできた多項式は p に等しい。 *)
Check coefK : forall (R : semiRingType) (p : {poly R}), \poly_(i < size p) p`_i = p :> {poly R}.

(* これは証明したい。XXXX *)
Goal \poly_(i < 0)(tstE i) = poly_nil R.
Proof.
Admitted.

(**
 # アーベルモノイドとしての多項式
 *)
Check @add_poly R : {poly R} -> {poly R} -> {poly R}.

(* 多項式の加算の係数は、多項式の係数の加算 *)
Check coef_add_poly : forall (R : semiRingType) (p q : {poly R}) (i : nat),
    (add_poly p q)`_i = p`_i + q`_i.
(* 左辺は多項式の加算、右辺は環の加算 *)

(* 多項式の加算の結合則、可換、0加算 *)
Check add_polyA : forall R p q r, add_poly p (add_poly q r) = add_poly (add_poly p q) r.
Check add_polyC : forall R p q, add_poly p q = add_poly q p.
Check add_poly0 : forall R p, add_poly 0%:P p = p.

(**
以下を定義すると、多項式は nmodTypeになるので、``+`` が使えるようになる。

HB.instance Definition _ := GRing.isNmodule.Build (polynomial R)
  add_polyA add_polyC add_poly0.
HB.instance Definition _ := GRing.Nmodule.on {poly R}.
*)
Check {poly R} : nmodType.
Check forall (R : semiRingType) (p q : {poly R}), p + q = add_poly p q :> {poly R}.

(**
# 0多項式

0 は GRing.zero、
 *)
Check {poly R} : nmodType.

(* 0多項式 ``0%:P`` は、環の0元である。 *)
Check polyC0 : forall R : semiRingType, 0%:P = 0 :> {poly R}.

Check polyseq0 : forall R : semiRingType, \val (0 : {poly R}) = [::] :> seq R.

Check size_poly0 : forall R : semiRingType, size (0 : {poly R}) = 0%N.

Check coef0  : forall (R : semiRingType) (i : nat), (0 : {poly R})`_i = 0 :> R.

Check lead_coef0 : forall R : semiRingType, lead_coef 0 = 0 :> R.

(* 略 *)

(**
# Size, leading coef, morphism properties of coef
 *)

Check coefD
  : forall (R : semiRingType) (p q : {poly R}) (i : nat), (p + q)`_i = p`_i + q`_i.


(**
# Polynomial semiring structure.
 *)
Print mul_poly_def.

(**
HB.instance Definition _ := GRing.Nmodule_isSemiRing.Build (polynomial R)
  mul_polyA mul_1poly mul_poly1 mul_polyDl mul_polyDr mul_0poly mul_poly0
  poly1_neq0.
HB.instance Definition _ := GRing.SemiRing.on {poly R}.
*)

End SemiPolynomialTheory.

Section PolynomialTheory.

Variable R : ringType.
(* Zmodule structure for polynomial *)

(**
HB.instance Definition _ := GRing.Nmodule_isZmodule.Build (polynomial R)
  add_polyN.
HB.instance Definition _ := GRing.Zmodule.on {poly R}.
 *)

Check {poly R} : zmodType.


(**
# Size, leading coef, morphism properties of coef
*)



(*
# Polynomial ring structure.
 *)

(**
HB.instance Definition _ := GRing.isMultiplicative.Build R {poly R} (@polyC R)
  polyC_multiplicative.
 *)

Check {poly R} : ringType.

(*
# Algebra structure of polynomials.
 *)

(**
HB.instance Definition _ := GRing.Zmodule_isLmodule.Build R (polynomial R)
  scale_polyA scale_1poly scale_polyDr scale_polyDl.
HB.instance Definition _ := GRing.Lmodule_isLalgebra.Build R (polynomial R)
  scale_polyAl.
HB.instance Definition _ := GRing.Lalgebra.on {poly R}.
 *)


(**
HB.instance Definition _ i := GRing.isScalable.Build R {poly R} R *%R (coefp i)
  (fun a => (coefZ a) ^~ i).
HB.instance Definition _ := GRing.Linear.on (coefp 0).
*)

(* The indeterminate, at last! *)

(* Expansion of a polynomial as an indexed sum *)

(* Some facts about regular elements. *)

(* Horner evaluation of polynomials *)

Print horner_rec.
(**
fun R : ringType =>
fix horner_rec (s : seq R) (x : R) {struct s} : R :=
  match s with
  | [::] => 0
  | a :: s' => horner_rec s' x * x + a
  end
 *)

Print root.
(**
fun (R : ringType) (p : {poly R}) (x : R) => p.[x] == 0
     : forall R : ringType, {poly R} -> pred R
 *)

Check factor_theorem
  : forall (R : ringType) (p : {poly R}) (a : R),
    reflect (exists q : {poly R}, p = q * ('X - a%:P)) (root p a).

(**
HB.instance Definition _ := GRing.ComRing_hasMulInverse.Build (polynomial R)
  poly_mulVp poly_intro_unit poly_inv_out.
HB.instance Definition _ := GRing.ComUnitRing.on {poly R}.

HB.instance Definition _ := GRing.ComUnitRing_isIntegral.Build (polynomial R)
  poly_idomainAxiom.
HB.instance Definition _ := GRing.IntegralDomain.on {poly R}.
*)

Check {poly R} : idomainType.

Check max_poly_roots
  : forall (R : idomainType) (p : {poly R}) (rs : seq R),
    p != 0 -> all (root p) rs -> uniq rs -> (size rs < size p)%N.


