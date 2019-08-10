(**
MathComp で文字列を使う - プログラムの証明への利用 -
======
2019/08/10


- 概要

プログラムの証明をするとき、自然数のほかに文字列を使いたくなります。
Coq/SSReflect/MathComp [1.] には文字列型の定義がないので、
Starndard Coqの文字列の定義 [2.] を使うことになります。

ここでは、それをそのまま使うのではなく、
決定性のある等式の使える型として文字列型を定義してみます。

同様に、2分木のデータ構造も定義して、LispのS式のようなデータを扱えるようにしてみます。
それを「定理証明手習い」[4.]のLispプログラムの証明に適用してみます。

全体を通して、決定性のある等式のサポートのあるMathCompは、
if-then-elesでの分岐のあるプログラムの証明にも便利であることを示します。
*)

(**
- この文書のソースコードは以下にあります。


https://github.com/suharahiromichi/coq/blob/master/pearl/ssr_string_3.v

 *)

(**
- バージョン


OCaml 4.07.1, Coq 8.9.0, MathComp 1.9.0
 *)

(**
----------------
# MathComp で自然数型を使う
 *)
From mathcomp Require Import all_ssreflect.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(**
 例。
 *)

Goal forall (n : nat), n = 42 -> if (n == 42) then true else false.
Proof.
  move=> n H.              (* H : n = 42 *)
  case: ifP.               (* if節 の成立と非成立で、場合分けする。 *)
  (* Goal : (n == 42) = true -> true *)
  - done.                      (* true なので自明 *)
  (* Goal : (n == 42) = false -> false *)
  - move/eqP.                     (* n <> 42 に「リフレクト」する。 *)
  (* Goal : n <> 42 -> false *)
    done.                         (* 前提どうしが矛盾する。 *)
Qed.


(**
----------------
# MathComp で自然数型を使う（続き）
 *)

(**
- Prop型の等式（「=」、Leibnizの等式）に加えて、
bool値を返す等式（「==」、bool値の等式）が使える。
 *)
Check @eq    : forall T : Type,   T -> T -> Prop. (* Leibnizの等式 「=」 *)
Check @eq_op : forall T : eqType, T -> T -> bool. (* bool値の等式 「==」 *)

(**
- bool値の等式は、その値がtrueかfalseどどちらかに決まる。
つまり決定性のあるので、
成り立つ場合(true)と、成り立たない場合(false) で場合分けできる。

ifP や eqP など MathComp で定義された補題（``ssrbool.v`` [1.])
を使う他、``case H : (n == 42).`` のようにbool値の式を直接書くこともできる。
 *)

(**
- 「==」が成り立たなければ、「!=」が成り立つといえる。
``x != y`` は、``~~ x == y`` ただし、「~~」はbool値の否定。
*)

(**
- bool値の等式（等式に限らないが）は、命題の文脈に埋め込むことができる。
*)

Check 42 == 42 : bool.
Check (42 == 42) = true : Prop.
Check 42 == 42 : Prop.     (* is_true が省略されている。コアーション。
 *)


(**
- 決定性の等式の型クラス(eqType)のインスタンス型(nat_eqType)が定義されている。
 *)

Check 42 : nat.
Check 42 : Equality.sort nat_eqType.
Check 42 : nat_eqType.       (* sort が省略されている。コアーション *)
(* 42 は nat_eqType 型ではない、ことに注意 *)

(**
- nat型からnat_eqType型への対応づけがある。
*)

Fail Check @eq_op nat 42 42. (* eq_opの第1引数はeqType型の型であるべき *)
Check @eq_op nat_eqType 42 42.
Check eq_op 42 42.
Check 42 == 42.
(* 42 は nat_eqType型ではないが、eqType型である型であるところに書くと、
nat_eqType型であると対応づけされる。カノニカル・プロジェクション *)

(**
- リスト型(seq)、直積型、オプション型と組み合わせとも、上記と同様になる。
*)

Check [:: 4; 2] == [:: 4; 2] : bool.
Check [:: 4; 2] == [:: 4; 2] : Prop.

Check [:: 4; 2] : seq nat.
Check [:: 4; 2] : seq_eqType nat_eqType. (* sort が省略されている。 *)

(**
---------------
# Coq の String型

Starndard Coqのライブラリ ``String.v`` [2.] を使う。
 *)

Require Import String.
Open Scope string_scope.

Check "abc" : string.

(**
- Ascii は bool をコンストラクタで組み立てたもの。
- String は Ascii をコンストラクタで組み立てたもの。
 *)

Import Ascii.
(* Set Printing All. *)

Check "A"%char. (* Ascii true false false false false false true false *) (* 41H *)
Check "ABC"%string. (* String "A" (String "B" (String "C" EmptyString)) *)


(**
---------------
# MathComp で文字列型を使う
 *)

Definition string_eqMixin := @EqMixin string String.eqb String.eqb_spec.
Canonical string_eqType := EqType string string_eqMixin.

Check "ABC" == "ABC" : bool.
Check "ABC" == "ABC" : Prop.

Check "ABC" : string.
Check "ABC" : string_eqType.

Check [:: "ABC"; "DEF"] == [:: "ABC"; "DEF"] : bool.
Check [:: "ABC"; "DEF"] == [:: "ABC"; "DEF"] : Prop.

Check [:: "ABC"; "DEF"] : seq string.
Check [:: "ABC"; "DEF"] : seq_eqType string_eqType.

(**
- 文字列型は、決定性のある等式が使える。「==」が使えるようになった。

- 文字列型を要素とするリストや直積型などでも、決定性のある等式が使える、ようになった。
*)


(**
------------------
# 二分木型の定義

「Star型は、アトム、または、Star型のふたつ要素を連結(Cons)したもの」
と再帰的に定義できます。これがinductiveなデータ型です。
*)

Inductive star T : Type :=
| S_ATOM of T
| S_CONS of star T & star T.

(**
Coqはinductiveなデータ型に対して、inductionできるようになります。
そのために、star_ind という公理が自動的に定義されます。
これは、TLPの第7賞で説明されている "star induction" と同じものです。

Coqによる証明でも、この公理を直接使用することはなく、
star型のデータに対して、
inductionタクティクまたはelimタクティクを使用すると、
この公理が適用されます。
 *)

(**
Star型についても、booleanの等号を定義して、論理式の等号にリフレク
ションできるようにします。
*)

Fixpoint eqStar {T : eqType} (x y : star T) : bool :=
  match (x, y) with
  | (S_ATOM a, S_ATOM b) => a == b          (* eqType *)
  | (S_CONS x1 y1, S_CONS x2 y2) => eqStar x1 x2 && eqStar y1 y2
  | _ => false
  end.

Lemma eqCons {T : eqType} (x y x' y' : star T) :
  (x = x' /\ y = y') -> @S_CONS T x y = @S_CONS T x' y'.
Proof.
  case=> Hx Hy.
    by rewrite Hx Hy.
Qed.

Lemma star_eqP : forall (T : eqType) (x y : star T), reflect (x = y) (eqStar x y).
Proof.
  move=> T x y.
  apply: (iffP idP).
  - elim: x y.
    + move=> x'.
      elim=> y.
      * by move/eqP => <-.                  (* ATOM と ATOM *)
      * done.                               (* ATOM と CONS *)
    + move=> x Hx y Hy.
      elim.
      * done.                               (* CONS と ATOM *)
      * move=> x' IHx y' IHy.               (* CONS と CONS *)
        move/andP.
        case=> Hxx' Hyy'.
        apply: eqCons.
        split.
        ** by apply: (Hx x').
        ** by apply: (Hy y').
  -  move=> <-.
     elim: x.
     * by move=> a /=.
     * move=> x Hx y' Hy /=.
         by apply/andP; split.
Qed.

Definition star_eqMixin (T : eqType) := @EqMixin (star T) (@eqStar T) (@star_eqP T).
Canonical star_eqType (T : eqType) := EqType (star T) (star_eqMixin T).

(**
# S式と S式の埋め込み

以降では、string型を要素（アトム）にもつS式だけを考えるので、その型を定義します。
*)

Definition star_exp := star string.

(**
S式を論理式(Prop)に埋め込めるようにします。このとき、Lispの真偽の定義から、

「真」 iff 「'NILでないS式」

としなければいけません。
実際には、S式からbooleanの等式 (x != 'NIL) へのコアーションを定義します。
これは、一旦boolを経由することで、論理式(Prop)の否定も扱えるようにするためです。

なお、コアーションを実現するためには、``star string`` では駄目で、
star_sring型が必須となるようです。
*)

Coercion is_not_nil (x : star_exp) : bool := x != (@S_ATOM string "NIL").

(**
さらに、S式の文脈でシンボルを直接書けるようにします。
次のコアーションで、S式のなかで、S_ATOM "ABC" の S_ATOM を省けるようになります。

これは、Lispの評価規則として正しくないかもしれませんが、
eval-quote式のLispの評価規則を実装することはTLPの範囲外と考え、
ここでは、書きやすさを優先することにします。
*)

Coercion s_quote (s : string) : star_exp := (@S_ATOM string s).


(**
# 「定理証明手習い」第7章

## CTX? と SUB の定義
*)

Fixpoint ctxp (x : star_exp) : star_exp :=
  match x with
  | S_CONS x1 x2 => if (ctxp x1) then (s_quote "T") else (ctxp x2)
  | _ => if x == (s_quote "?") then "T" else "F"
  end.

Fixpoint sub (x y : star_exp) : star_exp :=
  match y with
  | S_CONS y1 y2 => S_CONS (sub x y1) (sub x y2)
  | _ => if y == (s_quote "?") then x else y
  end.

(**
# 「定理証明手習い」第7章

## CTX?/SUB 定理の証明
*)

Lemma l_ctxp_cons (s1 s2 : star_exp) :
  (ctxp s1) || (ctxp s2) = (ctxp (S_CONS s1 s2)).
Proof.
  rewrite /=.
    by case: ifP.
Qed.

(* 不使用 *)
Lemma l_sub_cons (x s1 s2 : star_exp) :
  (sub x (S_CONS s1 s2)) = (S_CONS (sub x s1) (sub x s2)).
Proof.
  done.
Qed.

Lemma ctxp_sub (x y : star_exp) :
  (ctxp x) -> (ctxp y) -> (ctxp (sub x y)).
Proof.
  elim: y.
  - move=> t Hx Ht /=.
      by case: ifP.
  - move=> s1 IHs1 s2 IHs2 H /=.
    rewrite -l_ctxp_cons.
    move/orP.
    case.
    + move=> Hs1.
      case: ifP.
      * done.
      * move: (IHs1 H Hs1) => {IHs1} {Hs1} Hs1.
        move/negbT/negP.                    (* Hs1と矛盾する。 *)
        done.
    + move=> Hs2.
      move: (IHs2 H Hs2) => {IHs2} {Hs2} Hs2.
      case: ifP.
      * done.
      * move/negbT/negP.                    (* Hs2と矛盾する。 *)
        done.
Qed.


(**
----------------
# まとめ

1. 文字型を、決定性の等式の型クラス(eqType)のインスタンス型(string_eqType)として定義した。


2. 二分木型を、決定性の等式の型クラスのインスタンス型(star_eqType)として定義した。


3. Lispの S式のデータ構造を扱えるようにして、
「定理証明手習い」のLispプログラムの証明をしてみた。ctxp_sub


4. 決定性の等式の型クラスは、if-then-else による場合分けの多い、
プログラムの証明にも便利である。


5. MathComp でプログラムの証明しよう。

*)


(**
---------------
# 文献

[1.] Mathematical Components 公式

https://math-comp.github.io/


[2.] Library Coq.Strings.String

https://coq.inria.fr/library/Coq.Strings.String.html


[3.] Mathematical Components Book

https://math-comp.github.io/mcb/



[4.] 萩原学 アフェルト・レナルド 「Coq/SSReflect/MathCompによる定理証明」 森北出版



[5.] Daniel P. Friedman, Carl Eastlund, "The Little Prover", MIT Press, 2015.

https://mitpress.mit.edu/books/little-prover

中野圭介監訳、「定理証明手習い」、ラムダノート、2017。

https://www.lambdanote.com/collections/littleprover



[6.] リフレクションのしくみをつくる

https://qiita.com/suharahiromichi/items/9cd109386278b4a22a63



[5.] TBD

TBD



 *)

(**
---------------
# 補足説明
*)


(**
----------------
# 定理証明手習い（まとめ）

以上のようにすると、TLPで「公理」として与えられた命題の大半をを証明することができます。
残りの部分は、[3.]を参照してください。

S式（二分木のリスト）をもち、特定のATOMINCな要素(NIL)以外を真とするような、
Lispの意味を形式化したといえます。

TLPの前半では線形なリストを扱っていますが、それは、空リスト([])以外を真とする
ものですから、まったく異なったものになると思います。試みてください！

前述のとおり、評価規則についてはCoqに依存しています。
Eval-Quoteの評価規則を厳密に実装するには、なんらかのバーチャルマシンを定義する
ことになるのだろうとおもいます。これも試みてください！！
 *)





(**
----------------
# MathComp で自然数型を使う（続き）
 *)

Goal forall (n : nat), (n == 42) || (n != 42).
Proof.
  move=> n.
  case: (n == 42).
  - done.                                   (* n == 42 の場合 *)
  - done.                                   (* n != 42 の場合 *)
Qed.

Goal forall (l : seq nat), (l == [:: 42]) || (l != [:: 42]).
Proof.
  move=> l.
  case: (l == [:: 42]).
  - done.                                   (* l == [:: 42] の場合 *)
  - done.                                   (* l != [:: 42] の場合 *)
Qed.

(**
- 自然数型は、決定性のある等式が使える。

- 自然数型を要素とするリストや直積型などでも、決定性のある等式が使える
（リストや直積型に、その準備がされているため）。
*)

(**
---------------
# MathComp で自然数型を使う（続き）
 *)

Check 1      : nat                   : Type.
Check 1      : nat_eqType            : eqType.
Check 1      : Equality.sort nat_eqType.
(* 「==」 *)
Check 1 == 1                : bool.
Check @eq_op nat_eqType 1 1 : bool.
Fail Check @eq_op nat 1 1.

Check [:: 1] : seq nat               : Type.
Check [:: 1] : seq_eqType nat_eqType : eqType.
Check [:: 1] : Equality.sort (seq_eqType nat_eqType).
(* 「==」 *)
Check [:: 1] == [:: 1]                             : bool.
Check @eq_op (seq_eqType nat_eqType) [:: 1] [:: 1] : bool.
Fail Check @eq_op (seq nat) [:: 1] [:: 1].

(**
- nat_eqType は、eqType (決定性のある等式のある型）のインスタンスである。

- 1 は、nat型 であると同時に、nat_eqType型である（と見える）。コアーション。

- 「==」の引数の 1 は、nat_eqType であると対応づけできる。カノニカル・プロジェクション
*)



(**
---------------
# Coq の String型 (続き)

決定性のある等式は、Starndard Coqでも定義されている。ただし、

- 型毎に関数が違う（Notation で、「=?」と定義されてはいる）。
 *)

Goal forall (s1 s2 : string), (String.eqb s1 s2) || (~~ String.eqb s1 s2).
Proof.
  move=> s1 s2.
  case: (String.eqb s1 s2).
  - done.
  - done.
Qed.

(**
- string のリストか可能だが、それに対して「==」が使えない。
*)

Check [:: "ABC"] : seq string.
Fail Check [:: "ABC"] : seq_eqType string.
Fail Check [:: "ABC"] == [:: "ABC"].

(**
---------------
# MathComp で文字列型を使う（続き）
 *)

Check "ABC"      : string                   : Type.
Check "ABC"      : string_eqType            : eqType.
Check "ABC"      : Equality.sort string_eqType.
(* 「==」 *)
Check "ABC" == "ABC"                   : bool.
Check @eq_op string_eqType "ABC" "ABC" : bool.
Fail Check @eq_op string "ABC" "ABC".


Check [:: "ABC"] : seq string               : Type.
Check [:: "ABC"] : seq_eqType string_eqType : eqType.
Check [:: "ABC"] : Equality.sort (seq_eqType string_eqType).
(* 「==」 *)
Check [:: "ABC"] == [:: "ABC"]                                : bool.
Check @eq_op (seq_eqType string_eqType) [:: "ABC"] [:: "ABC"] : bool.
Fail Check @eq_op (seq string) [:: "ABC"] [:: "ABC"].

(**
- string_eqType は、eqType (決定性のある等式のある型）のインスタンスである、ようになった。

- "ABC" は、string型 であると同時に、string_eqType型である（と見える）、ようにになった。

- 「==」の引数の "ABC" は、string_eqType であると対応づけできる、ようになった。
*)

(**
---------------
# 補足説明 (その1)

Mixin について：
 *)

Check @EqMixin
  : forall (T : Type)                       (* (1) *)
           (op : T -> T -> bool),           (* (2) *)
    (forall x y, reflect (x = y) (op x y))  (* (3) *)
    -> Equality.mixin_of T.

Check @EqMixin nat                          (* (1) *)
      eqn                                   (* (2) *)
      (@eqnP)                               (* (3) *)
  : Equality.mixin_of nat.

Check @EqMixin (seq nat)
      eqseq
      (@eqseqP nat_eqType)
  : Equality.mixin_of (seq nat).

Check @EqMixin string                       (* (1) *)
      String.eqb                            (* (2) *)
      String.eqb_spec                       (* (3) *)
  : Equality.mixin_of string.

Check @EqMixin (seq string)
      eqseq
      (@eqseqP string_eqType)
  : Equality.mixin_of (seq string).

(**
(1) ベースとなる型、ここでは string

(2) 決定性のある、bool型を返す等式。

(3) (2)が、「=」と同値であることの証明を与える。ただし、bool型のtrueなら証明可能とみなす。

String型については、(1)(2)(3)とも、String.v で定義されてりるので、それを使う。

より詳しい説明は、[4.][5.][6.]。
  *)

(**
---------------
# 補足説明 (その2)

String.v での定義について：
*)

(**
(2) bool値を返す等式の定義
 *)

Print String.eqb.
(**
```

Fixpoint eqb s1 s2 : bool :=
 match s1, s2 with
 | EmptyString, EmptyString => true
 | String c1 s1', String c2 s2' =>
     if (Ascii.eqb c1 c2) then (eqb s1' s2') else false
 | _,_ => false
 end.

```

*)

(**
(3) の証明、リフレクティブ補題 ([5.])
*)

Check String.eqb_spec
  : forall s1 s2 : string, reflect (s1 = s2) (String.eqb s1 s2).





(* END *)
