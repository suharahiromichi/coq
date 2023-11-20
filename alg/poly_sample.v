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

Variable R : semiRingType.
Variable a b c d : R.

(**
-------------------------------
# 多項式のコンストラクタ

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
(* polyseq は単射である。 *)
Check @poly_inj R : forall p1 p2, polyseq p1 = polyseq p2 :> seq R -> p1 = p2 :> {poly R}.

(**
-------------------------------
# リストのサブタイプとしての多項式
*)
(* サブタイプの値からベースタイプの値を取り出す。 *)
Check val tstp1 : seq R.                    (* polyseq とおなじ。 *)

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



















Definition p1 := Poly [:: c; b; a].
Check p1 : {poly R}.

Definition p2 := \poly_(i < 3) f i.
Check p2 : {poly R}.

Check polyC c : {poly R}.
Check c%:P : {poly R}.
Check 'X : {poly R}.
Definition p3 := a%:P * 'X^2 + b%:P * 'X + c%:P * 'X^0.
Check p3 : {poly R}.

Goal forall i, p2`_i = f i.
Proof.
Admitted.

Goal forall i, coefp i p2 = f i.
Proof.
Admitted.





Goal 'X^1 = Poly [:: 0; 1] :> {poly R}.
Proof.
  rewrite unlock.
  rewrite /polyX_def.
  done.
Qed.

Goal 'X = [:: 0; 1] :> seq R.
Proof.
  by rewrite polyseqX.
Qed.

Goal 'X^2 = [:: 0; 0; 1] :> seq R.
Proof.
  by rewrite polyseqXn.
Qed.

Goal 'X^3 = [:: 0; 0; 0; 1] :> seq R.
Proof.
  by rewrite polyseqXn.
Qed.

Goal size ('X : {poly R}) = 2%N.
Proof.
  by rewrite size_polyX.
Qed.

Goal 1%:P = 1 :> {poly R}.
Proof.
  by rewrite polyC1.
Qed.

Check 'X          : {poly R} : lmodType R.
Check x *: 'X     : {poly R} : lmodType R.

Check lead_coef ('X : {poly R}).
Compute lead_coef ('X : {poly R}) = x.

Implicit Types (a b c x y z : R) (p q r d : {poly R}).

Local Notation "c %:P" := (polyC c).

Local Notation "\poly_ ( i < n ) E" := (poly n (fun i : nat => E)).

Open Scope unity_root_scope.

Theorem factor_theorem p a : reflect (exists q, p = q * ('X - a%:P)) (root p a).
Proof.
apply: (iffP eqP) => [pa0 | [q ->]]; last first.
rewrite hornerM_comm /comm_poly hornerXsubC subrr ?simp.

exists (\poly_(i < size p) horner_rec (drop i.+1 p) a).
apply/polyP=> i; rewrite mulrBr coefB coefMX coefMC !coef_poly.
apply: canRL (addrK _) _; rewrite addrC; have [le_p_i | lt_i_p] := leqP.
  rewrite nth_default // !simp drop_oversize ?if_same //.
  exact: leq_trans (leqSpred _).
case: i => [|i] in lt_i_p *; last by rewrite ltnW // (drop_nth 0 lt_i_p).
by rewrite drop1 /= -{}pa0 /horner; case: (p : seq R) lt_i_p.
Qed.


