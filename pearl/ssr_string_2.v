(**
MathComp で文字列を使う (スライド版)
======
2019/08/04


- 概要

Coq でプログラムの証明をするとき[3.]など、文字列型を使いたくなります。
MathComp [1.] には文字列の定義がないので、
Starndard Coqの文字列の定義 [2.] を使うことになります。
しかし、Import しただけでは、MathComp の機能を使えません。
文字列型をMathCompの型として使う方法を説明します。わずか1行の定義です。

- この文書のソースコードは以下にあります。


https://github.com/suharahiromichi/coq/blob/master/pearl/ssr_string_2.v

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

Goal forall (n : nat), (n == 42) || (n != 42).
Proof.
  move=> n.
  case H : (n == 42). (* n が 42 か、そうでないか、で場合分けする。 *)
  - done.             (* n が 42 の場合 *)
  - done.             (* n が 42 でない場合 *)
Qed.

(**
- bool値を返す等式（「==」）が使える。
 *)
Check @eq_op : forall T : eqType, T -> T -> bool. (* 「==」 *)

(**
- bool値を返す等式は、決定性のあるので、
成り立つ場合(true)と、成り立たない場合(false) で場合分けできる。case または destruct。

- 「==」が成り立たなければ、「!=」が成り立つといえる。「!=」は「==」のbool値の否定。
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
# MathComp で文字列型を使う
 *)

Canonical string_eqType := EqType string (EqMixin String.eqb_spec).

Goal forall (l : string), (l == "ABC") || (l != "ABC").
Proof.
  move=> l.
  case: (l == "ABC").
  - done.                                   (* l == "ABC" の場合 *)
  - done.                                   (* l != "ABC" の場合 *)
Qed.

Goal forall (l : seq string), (l == [:: "ABC"]) || (l != [:: "ABC"]).
Proof.
  move=> l.
  case: (l == [:: "ABC"]).
  - done.                                   (* l == [:: "ABC"] の場合 *)
  - done.                                   (* l != [:: "ABC"] の場合 *)
Qed.


(**
- 文字列型は、決定性のある等式が使える。「==」が使えるようになった。

- 文字列型を要素とするリストや直積型などでも、決定性のある等式が使える、ようになった。
*)


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


(**
------------------
# 定理証明手習い（STAR型)

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
      * by move/eqP => <-.                  (* ATOM どうし *)
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

(*
Definition star_eqMixin (T : eqType) := @EqMixin star (@eqStar T) (star_eqP T).
 *)
Definition star_eqMixin (T : eqType) := EqMixin (star_eqP T).
Canonical star_eqType (T : eqType) := EqType (star T) (star_eqMixin T).

(**
# 定理証明手習い（埋め込み）

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
------------------
# 定理証明手習い（組み込み関数）
*)

Definition Cons (x y : star_exp) : star_exp :=
  @S_CONS string x y.

Definition Car (x : star_exp) : star_exp :=
  match x with
  | S_ATOM _ => "NIL"
  | S_CONS x _ => x
  end.

Definition Cdr (x : star_exp) : star_exp :=
  match x with
  | S_ATOM _ => "NIL"
  | S_CONS _ y => y
  end.

Definition Atom (x : star_exp) : star_exp :=
  match x with
  | S_ATOM _ => "T"
  | S_CONS _ _ => "NIL"
  end.

Definition If (q a e : star_exp) : star_exp :=
  if q == s_quote "NIL" then e else a.

Definition Equal (x y : star_exp) : star_exp :=
  if x == y then "T" else "NIL".

(**
------------------
# 定理証明手習い（「公理」の証明）

ここまでに用意した道具を使って、証明をおこないます。
証明スクリプトは説明のためのものであり、もっとも短いなど最適化されたものではありません。
*)

Theorem equal_same (x : star_exp) :
  (Equal x x).
Proof.
  rewrite /Equal.
  Check eq_refl x : (x == x) = true.
  rewrite eq_refl.                      (* eq_refl は eqType の補題 *)
  done.

  Restart.
  Show.
  rewrite /Equal.
  case H : (x == x).
  - done.
  - move/eqP in H.                          (* 前提の矛盾 *)
    done.
Qed.

Theorem atom_cons (x y : star_exp) :
  (Equal (Atom (Cons x y)) "NIL").
Proof.
  rewrite /Equal /=.
  done.
Qed.

Theorem car_cons (x y : star_exp) :
  (Equal (Car (Cons x y)) x).
Proof.
  rewrite /Equal /=.
  rewrite eq_refl.                      (* eq_refl は eqType の補題 *)
  done.
Qed.

Theorem equal_swap (x y : star_exp) :
  (Equal (Equal x y) (Equal y x)).
Proof.
  rewrite {3}/Equal {2}/Equal.
  Check eq_sym x y : (x == y) = (y == x). (* eq_sym は eqType の補題 *)
  rewrite eq_sym.
  case: (y == x).                        (* まとめて場合分けする。 *)
  - done.
  - done.
Qed.

Theorem equal_if (x y : star_exp) :
  (If (Equal x y) (Equal x y) "T").
Proof.
    by rewrite /If; case: eqP; move/eqP.
Qed.

Theorem if_true (x y : star_exp) :
  (Equal (If "T" x y) x).
Proof.
    by rewrite /Equal; case: eqP.
Qed.

Theorem if_false (x y : star_exp) :
  (Equal (If "NIL" x y) y).
Proof.
    by rewrite /Equal; case: eqP.
Qed.

Theorem if_same (x y : star_exp) :
  (Equal (If x y y) y).
Proof.
  rewrite /If.
  case H : (x == s_quote "NIL").
  - by rewrite equal_same.               (* rewrite /Equal eq_refl. *)
  - by rewrite equal_same.               (* rewrite /Equal eq_refl. *)
Qed.

Theorem if_nest_A (x y z : star_exp) :
  (If x (Equal (If x y z) y) "T").
Proof.
  rewrite /If.
  case Hx : (x == s_quote "NIL").
  - done.
  - rewrite /Equal.
    case Hy : (y == y).
    + done.
    + move/eqP in Hy.                       (* 前提の矛盾 *)
      done.
Qed.

Lemma l_cons_car_cdr (x : star_exp) :
  (Atom x) = "NIL" -> (Cons (Car x) (Cdr x)) = x.
Proof.
  move=> Hn.
  case Hc: x; rewrite /Cons => //.
    by rewrite Hc in Hn.                    (* 前提の矛盾 *)
Qed.

Theorem cons_car_cdr (x : star_exp) :
  (If (Atom x) "T" (Equal (Cons (Car x) (Cdr x)) x)).
Proof.
  rewrite /If.
  case Hq : (Atom x == s_quote "NIL").
  - rewrite l_cons_car_cdr.
    + by rewrite equal_same.             (* rewrite /Equal eq_refl. *)
    + by move/eqP in Hq.
  - done.
Qed.


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
# まとめ

1. 文字列型を例に、MathComp の型定義について説明した。

2. 「定理証明手習い」のLispの Star型を定義して、これから「公理」を証明してみた。

3. eqType のインスタンスとして型を定義すると、決定性のあるbooleanの等号が使えるので、
いろいろ捗る。実は49個あるクラス（algebric Structure)の最初のひとつ。

4. MathComp でデータ型を定義して、証明しよう。

5. MathComp でプログラムの証明しよう。

*)


(**
---------------
# 文献

[1.] Mathematical Components 公式

https://math-comp.github.io/


[2.] Library Coq.Strings.String

https://coq.inria.fr/library/Coq.Strings.String.html


[3.] 「The Little Prover」のCoqでの実現---「定理証明手習い」の「公理」をCoqで証明してみた

https://qiita.com/suharahiromichi/items/723896ebfbc332f9d3dd


[4.] リフレクションのしくみをつくる

https://qiita.com/suharahiromichi/items/9cd109386278b4a22a63


[5.] 萩原学 アフェルト・レナルド 「Coq/SSReflect/MathCompによる定理証明」 森北出版


[6.] Mathematical Components Book

https://math-comp.github.io/mcb/

 *)

(**
---------------
# 補足説明
*)

Theorem equal_swap' (x y : star_exp) :
  (Equal (Equal x y) (Equal y x)).
Proof.
  rewrite {1}/Equal.
  case H : (Equal x y == Equal y x).
  - done.
  - rewrite /Equal [y == x]eq_sym in H.
      by move/negbT/eqP in H.
Qed.

(* END *)
