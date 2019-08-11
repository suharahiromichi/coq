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
    done.                                 (* 前提どうしが矛盾する。 *)
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

ifP や eqP など MathComp で定義された補題（``ssrbool.v`` [3.])
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

Mixin に、standard Coq で定義された、文字列型 ([2.]) のbool型の比較の関数と、
それが、Leibnizの等式と同値である証明を与える ([4.] p.131)。
 *)

Definition string_eqMixin := @EqMixin string String.eqb String.eqb_spec.
Canonical string_eqType := EqType string string_eqMixin.

Goal forall (s : string), s = "ABC" -> if (s == "ABC") then true else false.
Proof.
  move=> s H.              (* H : s = "ABC" *)
  case: ifP.               (* if節 の成立と非成立で、場合分けする。 *)
  (* Goal : (s == "ABC") = true -> true *)
  - done.                   (* true なので自明 *)
  (* Goal : (s == "ABC") = false -> false *)
  - move/eqP.                  (* s <> "ABC" に「リフレクト」する。 *)
  (* Goal : s <> "ABC" -> false *)
    done.                                 (* 前提どうしが矛盾する。 *)
Qed.

(**
- 文字列型に対して、Prop型の等式（「=」、Leibnizの等式）に加えて、
bool値を返す等式（「==」、bool値の等式）が使える。

- bool値の等式は、その値がtrueかfalseどどちらかに決まる。決定性がある。

ifP や eqP など MathComp で定義された補題（``ssrbool.v`` [3.])
を使う他、``case H : (s == "ABC").`` のようにbool値の式を直接書くこともできる。

- リスト型(seq)、直積型、オプション型と組み合わせとも、上記と同様になる。
*)

(**
---------------
# MathComp で文字列型を使う （続き）
 *)

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
----------------
# S式とS式の埋め込み

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
----------------
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
----------------
# 「定理証明手習い」第7章

## CTX?/SUB 定理の証明
*)

Lemma l_ctxp_cons (s1 s2 : star_exp) :
  (ctxp s1) || (ctxp s2) = (ctxp (S_CONS s1 s2)).
Proof.
  rewrite /=.
    by case: ifP.
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

[4https://qiita.com/suharahiromichi/items/9cd109386278b4a22a63



[5.] TBD

TBD



 *)

(**
---------------
# 補足説明
*)


(**
---------------
# 証明の詳細 （ifP 補題について）

ifP は ``ssrbool.v`` で定義されている。そのソースコードと、[3.]にも説明がある。
 *)

Goal forall (n : nat), n = 42 -> if (n == 42) then true else false.
Proof.
  move=> n Hn.
(**
``Hn : n = 42`` …… n は 42 である、これは全体の前提である。
 *)  

(**
ifP の引数を明示的に書くと。。。   
*)  
  move: (@ifP bool (n == 42) true false) => Hif.
  Check Hif : if_spec (n == 42) true false ((n == 42) = false) (n == 42)
                      (if n == 42 then true else false).

(**
場合分けする。
 *)
  case: Hif => Hcond.

(**
``Hcond : (n == 42) = true`` の場合。
 *)
  - Check @IfSpecTrue bool (n == 42) true false ((n == 42) = true)
    : n == 42 -> if_spec (n == 42) true false ((n == 42) = true) true true.
(**
``Goal : true`` …… これは、成立する。
*)
    done.

(**
``Hcond : (n == 42) = false`` の場合。
 *)
  - Check @IfSpecTrue bool (n == 42) true false ((n == 42) = false)
    : n == 42 -> if_spec (n == 42) true false ((n == 42) = false) true true.
(**
``Goal : false`` …… これは、成立しないけれども、
*)
(**
``Hcond : (n == 42) = false`` …… bool値 = false を…

``Hcond : n <> 42`` …… Prop型にリフレクトする。

リフレクションの際にビューヒントから補完される補題は elimTF である。
 *)
    move/eqP in Hcond.
    Undo 1.
    Check elimTF :
      forall (P : Prop) (b c : bool), reflect P b -> b = c -> if c then P else ~ P.
    Check elimTF eqP : (n == 42) = false -> if false then n = 42 else n <> 42.
    Check elimTF eqP : (n == 42) = false -> n <> 42.
    Check elimNTF eqP : ~~ (n == 42) = false -> n = 42. (* 参考 *)
    apply (elimTF eqP) in Hcond.
    rewrite /= in Hcond.

(**
[4.] では、リフレクションを
bool型とProp型 (bool型の等式 ``n == 42`` と Leibnizの等式 ``n = 42``)
の相互の変換として説明しているが、
boolの等式については ``(n == 42) = false`` 
の場合に ``n <> 42`` のような否定との間でリフレクションが可能である。
*)

(**
``Hcond : n <> 42`` は ``not (n = 42)`` なので、

``Hn : n = 42`` …… とから、 Hn と Hcond が矛盾するので証明終わり。
*)
    done.
Qed.


(**
--------------
# eqMixin のまとめ
*)

(**

| eqType   | sort  | op | axiom | Module (3) | 

|:----------------|:--------|:---------------|:---------------|:---------------|

| bool_eqType     | bool    | eqb (1)        | eqbP           |                |

| nat_eqType      | nat     | eqn (2)        | eqnP           |                |

| ascii_eqType    | ascii   | eqb (*)        | eqb_spec (*)   | Ascii   |

| string_eqType   | string  | eqb (*)        | eqb_spec (*)   | String  |

| seq_eqType eT   | seq T   | eqseqP         | eqseq          |                |

| prod_eqType eT  | prod T  | pair_eq        | pair_eqP       |                |

| option_eqType eT | option T | opt_eq        | opt_eqP        |                |

| star_eqType eT   | star T   | eqCons        | star_eqP       | 本資料で定義    |



(1) Standard Coq では、beq

(2) Standard Coq では、beq_nat

(3) 空欄は、Moduleの外からも参照可能であるため、省いた。

(*) Standard Coq で定義

 *)


(**
----------------
# 「定理証明手習い」の証明について - なにを証明しているのか - 

## 対象にしているLispの性質（意味）

- S式、すなわち、二分木の構造に基づく。
節をCONS、葉をATOMICと呼ぶ。

- 特定のATOMINCなシンボルであるNILを偽とする。
それ以外のATOMICな要素は真とする。ATOMICでない要素も真とする。

注記：LispではNILは空リストを示すわけではない。
LispのCONSは直積に近いもの。
もっとも深い位置にあるCONSの右側(CDR)は、かならずしもNILでなくてよい
また、その要素がNILでないなら（CDRを取った果てがNILでないなら）、偽を表すわけではない。

なお、上記は、ATOMICな要素に対してCARやCDRをとったときに、
便宜的にNILを返すことについてのべているのではない。

（注記終わり）


「定理証明手習い」の前半では線形なリストを扱っているが、
これは、空リストをNILとして偽とするものである。
この場合の性質（意味）は、ここでの内容と別なものになると思います（試みてください）。


## 対象にしているないLispの性質（意味）

- 評価規則についてはCoqに依存する。simpl タクティクを使うため。

- CARやCDRなどの組込関数を実装せず、match を使う。
Coq の Fixpoint と simpl タクティクをつかうため。

Fixpoint で well-formed で定義するためには match が必要である。
また、simpl タクティクは、コンストラクタされた値をmatchで分解する
（ιイオタ簡約）をおこなうが、CARやCDRを定義して使うとこれが機能しない。
すなわち、Coqを使う必要性がなくなってしまう。

 *)


(* END *)
