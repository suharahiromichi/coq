(**
Coq/SSReflect/MathComp による定理証明

第4章 MathComp ライブラリの基本ファイル

4.5 fintype.v --- 有限型のライブラリ

======

2018_12_10 @suharahiromichi
 *)

From mathcomp Require Import all_ssreflect.
From mathcomp Require Import perm.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(**
# はじめに

本節はテキストを参照しながら、MathComp のソースコードに沿って説明していきます。
ソースコードが手元にあるならば、それも参照してください。
opamでインストールしている場合は、ソースは、たとえば以下にあります。

~/.opam/4.07.1/lib/coq/user-contrib/mathcomp/ssreflect/fintype.v
*)

(**
# finType とは

要素の列挙(enum)のリストと、enumの要素に重複がないことを公理とする。
具体的なインスタンスを生成するときに、この公理は証明済みの命題に置き換える。
*)

(**
公理の内容は、以下である。ballがこれを満たすことは、あとで調べる。
*)
Print Finite.axiom.
(**
conunt_mem を展開すると、つぎのようになる。
*)
Check fun (T : eqType) (e : seq T) =>
        forall x : T, count [pred y | x == y] e = 1.
(**
とりあえあず ``[pred y | x == y]`` は ``fun y => x == y`` と思ってよい。
 *)

(**
## ball_finType
 *)

(**
### ball_eqType, ball_choiceType, ball_countType を定義する。

ball と bool が1対1対応であることを証明して、それを使って、
型クラスeqType のインスタンスの ball_eqType型を定義する。
型クラスchoiceType のインスタンスの ball_choiceType型を定義する。
型クラスcountType のインスタンスの ball_countType型を定義する。

eqType の公理を直接証明するのは、以下を参照のこと。
https://github.com/suharahiromichi/coq/blob/master/csm/csm_4_2_eqtype.v

Coutable の公理 (unpick と pick) はともかく、Choice の公理を証明するのは大変。
*)

(**
predArgType を明示したほうがよい。
 *)
Inductive ball : predArgType :=
| red                          (* 紅玉 *)
| white.                       (* 白玉 *)

Definition ball2bool (b : ball) : bool :=
  match b with
  | red => true
  | white => false
  end.

Definition bool2ball (b : bool) : ball :=
  match b with
  | true => red
  | false => white
  end.

Lemma inj_b2b : injective ball2bool.
Proof. by case; case. Qed.

Lemma can_b2b : cancel ball2bool bool2ball.
Proof. by case. Qed.

Definition ball_eqMixin := InjEqMixin inj_b2b.
Canonical ball_eqType := EqType ball ball_eqMixin.
Definition ball_choiceMixin := CanChoiceMixin can_b2b.
Canonical ball_choiceType := ChoiceType ball ball_choiceMixin.
Definition ball_countMixin := CanCountMixin can_b2b.
Canonical ball_countType := CountType ball ball_countMixin.

(**
### ball の本来の定義を使ってfinTypeを定義する。
 *)
Definition ball_enum := [:: red; white].

(**
ball_eqType で導入した「==」が、Finite.axiom を満たすことを確かめます。
*)
Compute count [pred y | red == y] ball_enum.   (* 1 *)
Compute count [pred y | white == y] ball_enum. (* 1 *)

(**
定理として証明します。
*)
Lemma ball_uniq : forall x, count_mem x ball_enum = 1.
Proof. by case. Qed.

Definition ball_finMixin' := @FinMixin ball_countType ball_enum ball_uniq.
Canonical ball_finType' := FinType ball ball_finMixin'.

(**
### ball2bool の単射性をつかってfinTypeを定義する。
 *)
Definition ball_finMixin := CanFinMixin can_b2b.
Canonical ball_finType := FinType ball ball_finMixin.

(**
出来上がったもの：
*)
Check red : ball : predArgType.
(**
ball の定義のときに predArgType を明示しない場合：
ball : predArgType は成り立つ。 predArgType = Type なので。
しかし、finType の定義のなかで、濃度の定義がされない。card は mem_pred T -> nat であるため。
*)
Check red : ball_finType : finType.
Check red : Finite.sort ball_finType : predArgType.

(**
ここでは、ball型 と bool型 との要素の対応で定義したが、
Ordinal型との要素の対応で定義もできる。MCBの7.5節参照。

[MCB] Mathematical Components (MathComp Book)
https://math-comp.github.io

https://github.com/suharahiromichi/coq/blob/master/math-comp-book/suhara.ch7-windrose.v
*)

(**
### MathComp の三点セット（？）

以上で、==, \in, #|_| の「三点セット」が成り立つよういなる。
*)
Check red == red.
Check red != white.
Check red \in ball.          (* 最初に predArgType を明示すること。 *)
Check #| ball | == 2.        (* predArgType に対する finType なら濃度が定義される。 *)

(**
# その他の finType のインスタンス型
*)

Check bool_finType       : finType.         (* bool型 *)
Check ordinal_finType 5  : finType.         (* 濃度5の順序数 *)

Check tuple_finType 3 (ordinal_finType 5)
  : finType.                (* 濃度5の順序数を要素とする寸法3のリスト *)

Check finfun_finType (ordinal_finType 5) (ordinal_finType 6)
  : finType. (* 濃度5の順序数を引数、濃度6の順序数を値とする関数である。 *)
(* finfun は、一般に値は任意の型でよいので、finfun が finType とは限らない。 *)

Check set_finType (ordinal_finType 5) : finType. (* 濃度5の順序数を要素とする集合 *)
(* finset は、finType型を引数、bool型を値とする関数 finfun である。 *)

Check perm_finType (ordinal_finType 5) : finType. (* 濃度5の順序数の順列 *)

(**
# 順序数 (ordinal n)

``0``〜``n-1`` の範囲の自然数である。
*)

Goal [forall x in 'I_5, x < 5].
Proof.
  apply/forallP.
    (* forall x, (x \in 'I_5) ==> (x < 5) *)
    by case=> m i.
Qed.  

(**
## ordinal 型の値を作る関数

"n is inferred from the context" とは、この場合、``: 'I_5`` のところ。
 *)
Definition s0 : 'I_5 := ord0.
Definition s1 : 'I_5 := inord 1.
Definition s2 : 'I_5 := inord 2.
Definition s3 : 'I_5 := inord 3.
Definition s4 : 'I_5 := ord_max.

Definition p0 (x : 'I_5) := (x == s0).      (* 'I_5 -> bool *)
Definition p4 (x : 'I_5) := x <= s4.        (* 'I_5 -> bool *)

(**
出来上がったもの：
*)
Check s1 : 'I_5 : predArgType.            (* ordinal は predArgType *)
(**
``'I_5`` (``ordinal 5``) は、Finite.sort 関数についての
``ordinal_finType 5`` のカノニカル解なので、
Coq は ``Finite.sort (ordinal_finType 5)`` が ``'I_5`` であることを推論できる
（テキスト 3.15.2 参照）。
*)
Check s1 : ordinal_finType 5 : finType.
Check s1 : Finite.sort (ordinal_finType 5) : predArgType.
Compute Finite.sort (ordinal_finType 5).    (* 'I_5 *)

Compute val s1.                             (* ***** *)

(**
## 順序数の定義に基づいた定義

s1 == s1' であることの証明をすること。。。
*)
Definition s1' : 'I_5.
Proof. by apply: (@Ordinal 5 1). Defined.   (* Defined で終わる。 *)
Compute val s1'.                            (* 1 *)

Lemma le15 : 1 <= 5. Proof. done. Qed.
Definition s1'' := @Ordinal 5 1 le15.
Compute val s1''.                           (* 1 *)



(**
## 型を変換する関数
*)
Lemma le_5_6 : 5 <= 6. Proof. done. Qed.
Check @widen_ord 5 6 le_5_6 s1 : 'I_6.

Definition s1''' : 'I_6.
Proof.
  apply: (@widen_ord 5 6).
  - done.
  - apply: s1.
Defined.

(**
順序数の型（範囲）をひとつだけ増やす関数。
 *)
Definition widen_ord_1 {n : nat} (s : 'I_n) : 'I_n.+1.
Proof.
  apply: widen_ord.
  - by apply: leqnSn.
  - by apply: s.
Defined.

Check widen_ord_1 (widen_ord_1 s1) : 'I_7.


(**
## val または  nat_of_ord で自然数の値を取り出す。後者はコアーション。
*)
Check val : 'I_5 -> nat.
Check @nat_of_ord 5  : 'I_5 -> nat.

Compute val s0.                             (* = 0 *)
Compute nat_of_ord s0.                      (* = 0 *)

Compute val s4.                             (* = 4 *)
Compute nat_of_ord s4.                      (* = 4 *)

Compute s0 < 4.                     (* 不等式はコアーションが効く。 *)

(**
## 補題 val と nat_of_ord が単射である。
*)

Check @val_inj : forall (T : Type) (P : pred T) (sT : subType P), injective val.
Check ord_inj : forall n : nat, injective (nat_of_ord (n:=n)).

(**
## Ordinal についての補題：
*)

Check ltn_ord : forall (n : nat) (i : 'I_n), i < n.
Check leq_ord : forall (n' : nat) (i : 'I_n'.+1), i <= n'.

Check card_ord : forall n : nat, #|'I_n| = n.

Check widen_ord_proof : forall (n m : nat) (i : 'I_n), n <= m -> i < m.
Check cast_ord_proof : forall (n m : nat) (i : 'I_n), n = m -> i < m.


(**
# 濃度 Cardinal
*)

Goal #| 'I_5  | = 5.
Proof.
    by rewrite cardE size_enum_ord.
Qed.

Check cardE : forall (T : finType) (A : predPredType T), #|A| = size (enum A).
Check eq_card : forall (T : finType) (A B : predPredType T), A =i B -> #|A| = #|B|.
Check eq_card_trans : forall (T : finType) (A B : predPredType T) (n : nat),
    #|A| = n -> B =i A -> #|B| = n.
Check card0 : forall T : finType, #|pred0| = 0.
Check card1 : forall (T : finType) (x : T), #|pred1 x| = 1.
Check eq_card0 : forall (T : finType) (A : predPredType T), A =i pred0 -> #|A| = 0.
Check eq_card1
  : forall (T : finType) (x : T) (A : predPredType T), A =i pred1 x -> #|A| = 1.
Check cardUI : forall (T : finType) (A B : predPredType T),
    #|[predU A & B]| + #|[predI A & B]| = #|A| + #|B|.
Check cardID : forall (T : finType) (B A : predPredType T),
    #|[predI A & B]| + #|[predD A & B]| = #|A|.
Check cardC : forall (T : finType) (A : predPredType T), #|A| + #|[predC A]| = #|T|.      Check cardU1 : forall (T : finType) (x : T) (A : predPredType T),
    #|[predU1 x & A]| = (x \notin A) + #|A|.

(**
濃度が存在することの証明：

https://github.com/suharahiromichi/coq/blob/master/pearl/ssr_ex_card.v
 *)

(**
# forall と exists (boolean quantifiers)

## 定義

bool型を返す量化子（∀と∃）であり、``T : finType`` のとき、
bool型を返す述語 ``P : T -> bool`` において、
T型の要素を量化の範囲として、その「すべて」、「ある」要素に対して
``P x`` が true を返すとき、
[forall x in T, P x]、[exists x in T, P x] は true を返す。
``in T`` は省略できる。
*)

(**
## 用意されている同値の補題
*)
Check @forallP
  : forall (T : finType) (P : pred T), reflect (forall x : T, P x) [forall x, P x].
Check @existsP
  : forall (T : finType) (P : pred T), reflect (exists x : T, P x) [exists x, P x].

Goal [forall x, p4 x].              (* すべての 'I_5 の要素は、4以下である。 *)
Proof.
  apply/forallP.
  rewrite /p4 /s4.
  (* forall x : ordinal_finType 5, x <= p4 *)
  case=> m /=.
  (* m < 5 -> m <= 4 *)
  done.
Qed.

Goal [exists x, p0 x].             (* ある 'I_5 の要素は、0である。 *)
Proof.
  apply/existsP.
  rewrite /p0.
  (* exists x : ordinal_finType 5, x == p0  *)
  exists s0.
  (* p0 == p0 *)
  done.
Qed.

(**
# \subset と \proper

## 定義

``T : finType`` のとき、
bool型を返す述語 ``P : T -> bool`` において、
それがtrueを返す、Tの要素についての包含関係（部分集合と真部分集合）を考えることができる。
 *)

Check p0 \subset p4.
(**
``p0 \subset p4`` は、濃度が0であることで定義されている。すなわち、
*)
Check (fun x : 'I_5 => ~~ (p0 x) && (p4 x)) : pred 'I_5.
(**
p0 x が false かつ p4 x が true という論理式を考え、
 *)
Check card (mem (predD (fun x => p0 x) (fun x => p4 x))) == 0.
(**
それを満たす x の個数が 0個である、と定義されている。

次の補題は、\subset の定義を展開しただけのものである。
*)
Check subsetE
  : forall (T : finType) (A B : predPredType T),
    (A \subset B) = pred0b [predD A & B].

(**
\proper は \subset から定義されている。
*)
Check p0 \proper p4.
Check (p0 \subset p4) && ~~(p4 \subset p0).


(**
## Prop型の命題 ``{subset p0 <= p4} == (x \in p0 -> x \in p4)``
*)
Lemma p0_p4' : {subset p0 <= p4}.
Proof.
  rewrite /p0 /p4 => x.
  rewrite /in_mem /=.
    by move/eqP => ->.
Qed.

(**
補題が用意されている。
*)
Check @subsetP
  : forall (T : finType) (A B : predPredType T),
    reflect {subset A <= B} (A \subset B).
Check @properP
  : forall (T : finType) (A B : predPredType T),
    reflect (A \subset B /\ (exists2 x : T, x \in B & x \notin A)) (A \proper B).

Lemma p0_p4 : p0 \subset p4.
Proof.
  by apply/subsetP/p0_p4'.
Qed.

Lemma p0_p4'' : p0 \proper p4.
Proof.
  apply/properP.
  split.
  - by apply: p0_p4.
  - by exists s4.
Qed.

(**
## bool型の命題 ``[forall x, (x \in p0) ==> (x \in p4)]``
*)
Section Test.
  Variable T : finType.
  
(**
命題型とbool型の同値関係を証明しておく。

(forall x, x \in q1 -> x \in q2) <-> [forall x, (x \in q1) ==> (x \in q2)]
*)
  Lemma mySubsetP' (q1 q2 : pred T) :
    {subset q1 <= q2} <-> [forall x, (x \in q1) ==> (x \in q2)].
  Proof.
    split=> H.
    - apply/forallP => x.
        by apply/implyP/H.
      - move=> x.
      apply/implyP.
      move: x.
        by apply/forallP.
  Qed.
  
  Lemma mySubsetP (q1 q2 : pred T) :
    q1 \subset q2 <-> (forall x, x \in q1 -> x \in q2).
  Proof.
    split.
    - move/subsetP.
      move/mySubsetP' => H.
        by apply/mySubsetP'.
    - move/mySubsetP' => H.
      apply/subsetP.
        by apply/mySubsetP'.
  Qed.
  
  Lemma mySubsetE (q1 q2 : pred T) :
    q1 \subset q2 = [forall x, (x \in q1) ==> (x \in q2)].
  Proof.
    apply/idP/idP.
    - move=> H.
      apply/forallP => x.
      apply/implyP.
        by apply/mySubsetP : x.
    - move=> H.
      apply/mySubsetP => x.
      move/forallP in H.
        by move: (H x) => {H} /implyP H /=.
  Qed.
End Test.

Goal [forall x, (x \in p0) ==> (x \in p4)].
Proof.
  rewrite -mySubsetE.
    by apply: p0_p4.
Qed.

(* END *)
