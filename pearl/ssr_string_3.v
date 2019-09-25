(**
MathComp で文字列を使う - 「定理証明手習い」の証明をしてみた
======

@suharahiromichi

2019/08/10

2019/09/18
 *)

(**
- 概要

プログラムの証明をするとき、自然数のほかに文字列を使いたくなります。
Coq/SSReflect/MathComp [1.] には文字列型の定義がないので、
Starndard Coqの文字列の定義 [2.] を使うことになります。

ここでは、それをそのまま使うのではなく、
決定性のある同値関係の使える型として文字列型を定義してみます。

同様に、2分木型のデータ構造も定義して、
LispのS式のようなデータを扱えるようにしてみます。
それを「定理証明手習い」（以下 TLP [5.]) のLispプログラムの証明に適用してみます。

全体を通して、決定性のある同値関係のサポートのあるMathCompは、
if-then-elesでの分岐のあるプログラムの証明にも便利であることを示します。


注意：この記事では、Lispのシンボルを文字列で表します（例："T", "NIL", "?"）。
近代Lispで使われる、Lispのデータ構造としての文字列（分解や連結）については扱いません。
*)

(**
- この文書のソースコードは以下にあります。


https://github.com/suharahiromichi/coq/blob/master/pearl/ssr_string_3.v

 *)

(**
- バージョン


OCaml 4.07.1, Coq 8.9.0, MathComp 1.9.0
 *)
From mathcomp Require Import all_ssreflect.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(**
----------------
# 型クラス ``eqType`` について
 *)

(**
MathComp の実体は、深く継承された型クラスといってもよいのですが、
その根にあるのは ``eqType`` という決定性のある同値関係が使える型のクラスです。

毎度お馴染みの自然数型や今回述べる文字列型を台(carrier)にして、``eqType`` の
型インスタンスを生成することで、
自然数や文字列に対して、決定性のある同値関係 (``==``) が使えるようになります。
自然数については、標準で意識せずに使っているかもしれません。
ふたつの自然数が等しいかどうかを判定できる、ということです。

以下、決定性のある同値関係の式を「bool値の等式」と呼ぶ場合があります。
 *)

Compute 42 == 42.                           (* true *)
Compute 42 == 0.                            (* false *)

(**
これに対して、``=`` (Leibnizの等式)は、ふたつの値が等しいことを「証明できる」ということです。
*)

Compute 42 = 42.                            (* 42 = 42 *)
Goal 42 = 42. Proof. reflexivity. Qed.

(**
自然数型 ``nat`` を台とする ``eqType`` のインスタンスは ``nat_eqType`` です。
これは MathComp の命名規則によるようです。
 *)

Check     eqType :   Type.
Check nat_eqType : eqType.

(**
自然数型 ``nat`` が型であるように、``nat_eqType`` も型とみなせます。
「eqType型の型」です。
実際には、コアーション([4.] p.94)によって sort が省略されていることに注意してください。
*)

Check               nat        : Type.
Check Equality.sort nat_eqType : Type.
Check               nat_eqType : Type.      (* コアーション *)

(**
定数 ``42`` の型が ``nat`` であるのと同様に、``nat_eqType`` 型でもあるとみなせます。
しかし、``42`` は複数の型を持つわけではなく、
コアーションによって sort が省略されていることに注意してください。
結果として、``42`` は、「eqType型の型」のところに書くことができます。
 *)

Check 42 :               nat.
Check 42 : Equality.sort nat_eqType.
Check 42 :               nat_eqType.        (* コアーション *)

(**
``nat``型から ``nat_eqType``型への対応づけがあります。
*)

Fail Check @eq_op nat        42 42. (* eq_opの第1引数はeqType型の型であるべき *)
Check      @eq_op nat_eqType 42 42.
Check       eq_op            42 42. (* nat_eqType を探し出している。 *)
Check                        42 == 42.      (* 同上 *)

(**
``42`` を「eqType型の型」の場所に書くためには、
それが ``nat_eqType`` であることが判る必要があります。
クラスからインスタンスを探し出すことになるので、逆引きになり、
Canonical コマンド ([4.] p.120) で宣言することで可能になります。
この逆引き推論をすることをカノニカル・プロジェクションといいます。
宣言の方法は後述します。
*)

(**
----------------
# MathComp で自然数型を使う

## 自然数の証明の例
 *)

(**
最初に、決定性のある同値関係の使える型として自然数の証明の例を示します。
決定性のある同値関係 ``n == 42`` の真偽で分岐するif-then-else式について、
条件の成立・非成立で場合分けして、成立な自明で、非成立なら矛盾を導きます。
証明の詳細は、末尾の補足説明に記載します。
 *)

Goal forall (n : nat), n = 42 -> if n == 42 then true else false.
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

## 自然数の性質
 *)

(**
（決定性のある同値関係の使える型としての）自然数には、次の性質があります。
 *)

(**
- Prop型の等式（「=」、Leibnizの等式）に加えて、
bool値を返す等式（「==」、bool値の等式）が使える。
 *)
Check @eq    : forall T  : Type,   T  -> T  -> Prop. (* Leibnizの等式 「=」 *)
Check @eq_op : forall eT : eqType, eT -> eT -> bool. (* bool値の等式 「==」 *)

(**
- bool値の等式は、その値がtrueかfalseどどちらかに決まる。
つまり決定性があるので、
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
Check 42 == 42 : Prop.     (* is_true が省略されている。コアーション。 *)


(**
- リスト型(seq)、直積型、オプション型と組み合わせとも、上記と同様になる。
*)

Check [:: 4; 2] == [:: 4; 2] : bool.
Check [:: 4; 2] == [:: 4; 2] : Prop.

Check [:: 4; 2] : seq nat.
Check [:: 4; 2] : seq_eqType nat_eqType. (* sort が省略されている。 *)

(**
---------------
# Coq の文字列型
 *)

(**
次に、Coqの標準ライブラリにある文字列型 (``String.v`` [2.]) をみてみましょう。
 *)

Require Import String.
Open Scope string_scope.

Check "ABC" : string.

(**
文字列型 (string型) は ascii型 から、ascii型 は bool型 から構成されます。
``Set Ptinting All`` を設定すると、それが判ります。
 *)

Import Ascii.
(* Set Printing All. *)

Check "A"%char. (* Ascii true false false false false false true false *) (* 41H *)
Check "ABC"%string. (* String "A" (String "B" (String "C" EmptyString)) *)


(**
---------------
# MathComp で文字列型を使う

## 決定性のある同値関係の使える型としての定義
 *)

(**
Coqの標準ライブラリにある文字列型をMathCompの自然数型のような、
決定性のある同値関係の使える型として定義します。

最初に述べたように、型クラス ``eqType`` のインスタンスとして、
文字列型を台とする型を生成します。
そのためには、ふたつの文字列が同じか判定するbool値の関数と、
それがLeibnizの等式と同値であるという証明を与える必要があります ([4.] p.131)。
 *)

Definition string_eqMixin := @EqMixin string String.eqb String.eqb_spec.
Canonical string_eqType := EqType string string_eqMixin.

(**
- String.eqb ......... 文字列型のbool型の判定の関数
- String.eqb_spec .... Leibnizの等式と同値であるという証明

どちらも ``String.v`` で定義されているものが使えます。
2行めの Canonical は Define の代わりで、カノニカル・プロジェクションを有効にします。
 *)

(**
---------------
# MathComp で文字列型を使う（続き）

## 文字列の証明の例
 *)

(**
文字列の証明の例を示します。
文字列が決定性のある同値関係の使える型になっているので、自然数の証明と同じになっています。
*)

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
（決定性のある同値関係の使える型としての）文字列には、次の性質があります。
 *)

(**
- 文字列型に対して、Prop型の等式（「=」、Leibnizの等式）に加えて、
bool値を返す等式（「==」、bool値の等式）が使える。

- bool値の等式は、その値がtrueかfalseどどちらかに決まる。決定性がある。

ifP や eqP など MathComp で定義された補題（``ssrbool.v`` [3.])
を使う他、``case H : (s == "ABC").`` のようにbool値の式を直接書くこともできる。

- リスト型(seq)、直積型、オプション型と組み合わせとも、上記と同様になる（次頁）。
*)

(**
---------------
# MathComp で文字列型を使う （続き）

## 文字列の性質
 *)

(**
ここまでをまとめると、次のようになります。

- 文字列型は、決定性のある同値関係(``==``)が使えるようになった。
- 文字列型を要素とするリストや直積型などでも、決定性のある同値関係が使える、ようになった。
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
------------------
# Star型（S式) の定義
 *)

(**
2分木型をここでは TLP ([5.]) の「Star Induction」から、Star型と命名します。
Star型は、「ATOM、または、Star型のふたつ要素を連結(CONS)したもの」と再帰的に定義できます。
その要素のことを一般的なLispのようにS式と呼ぶことにします。

任意の型を ATOM にできるように、``T : Type`` を引数とします。
*)

Inductive star (T : Type) : Type :=
| S_ATOM of T
| S_CONS of star T & star T.

(**
Star型はInductiveなデータ型です、(TLP [5.]と同様に)
Coqはinductiveなデータ型に対して、inductionできるようになります。
 *)

(**
文字列型と同様に、``Star T`` 型についても、型クラス ``eqType`` のインスタンスとして、
``Star T``型を台とする型を生成します。

最初に、``star T``型のふたつの値(S式)が同じか判定するbool値の関数 ``eqStar`` を定義します。

CONSを分解してATOMに至ったら、
ATOMどうしを決定性のある同値関係を使って、等しいかどうか判定します。
ここで、引数 ``eT`` の型が (``Type``でなく) ``eqType`` であることに注意してください。
なので、ATOMの値 a と b は、「eqType型の型」になります。
*)

Fixpoint eqStar {eT : eqType} (x y : star eT) : bool :=
  match (x, y) with
  | (S_ATOM a, S_ATOM b) => a == b          (* eqType *)
  | (S_CONS x1 y1, S_CONS x2 y2) => eqStar x1 x2 && eqStar y1 y2
  | _ => false
  end.

(**
次いで、Leinizの等式と ``eqStar`` によるbool値の等式とが同値であることを証明します。
*)
Lemma eqCons {eT : eqType} (x y x' y' : star eT) :
  (x = x' /\ y = y') -> @S_CONS eT x y = @S_CONS eT x' y'.
Proof.
  case=> Hx Hy.
    by rewrite Hx Hy.
Qed.

Lemma star_eqP : forall (eT : eqType) (x y : star eT), reflect (x = y) (eqStar x y).
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
         by apply/andP/conj.
Qed.

(**
最後に、型クラス ``eqType`` のインスタンスとして、``Star T``型を台とする型を生成します。
これで、文字列型と同様に、``Star T``型を決定性のある同値関係の使える型として定義できました。
*)
Definition star_eqMixin (eT : eqType) := @EqMixin (star eT) (@eqStar eT) (@star_eqP eT).
Canonical star_eqType (eT : eqType) := EqType (star eT) (star_eqMixin eT).

(**
このとき、``Star eT`` の ``eT`` は ``eqType`` でなければなりません。
そうであるならば、``star_eqType eT`` は ``eqType`` になります。
 *)

Check star_eqType    nat_eqType : eqType.   (* 自然数を要素とする S式 *)
Check star_eqType string_eqType : eqType.   (* 文字列を要素とする S式 *)


(**
----------------
# Star型（S式）の埋め込み

以降では、string型を要素（ATOM）にもつS式だけを考えるので、その型を定義します。
*)

Definition star_exp := star string.

(**
S式を論理式(Prop)に埋め込めるようにします。このとき、Lispの真偽の定義から、

「真」 iff 「"NIL" でないS式」

としなければいけません。
実際には、S式からbooleanの等式 (x != "NIL") へのコアーションを定義します。
これは、一旦boolを経由することで、論理式(Prop)の否定も扱えるようにするためです。

なお、コアーションを実現するためには、``star string`` では駄目で、
star_sring型が必須となるようです。
*)

Coercion is_not_nil (x : star_exp) : bool := x != (S_ATOM "NIL").

(**
さらに、S式の文脈でシンボルを直接書けるようにします。
次のコアーションで、S式のなかで、S_ATOM "ABC" の S_ATOM を省けるようになります。

これは、Lispの評価規則として正しくないかもしれませんが、
eval-quote式のLispの評価規則を実装することは TLP ([5.]) の範囲外と考え、
ここでは、書きやすさを優先することにします。
*)

Coercion s_quote (s : string) : star_exp := (S_ATOM s).

(**
なお、if-then-else のなかで、コアーションはうまく機能しない箇所がありました。
そこでは、s_quote を補っています。
*)

(**
----------------
# 「定理証明手習い」 TLP 第7章

## CTX? と SUB の定義
 *)

(**
TLP ([5.]) の関数をCoqで定義してみます。ここではシンボルを文字列で表します。

- (CTX? x) .... S式 x にシンボル "?" が含まれていたら "T" を返す。
*)

Fixpoint ctxp (x : star_exp) : star_exp :=
  match x with
  | S_CONS x1 x2 => if (ctxp x1) then (s_quote "T") else (ctxp x2)
  | _ => if x == (s_quote "?") then "T" else "F"
  end.

(**
- (SUN x y) ... S式 x に含まれるシンボル "?" を S式 y で置き換える。
*)

Fixpoint sub (x y : star_exp) : star_exp :=
  match y with
  | S_CONS y1 y2 => S_CONS (sub x y1) (sub x y2)
  | _ => if y == (s_quote "?") then x else y
  end.

(**
----------------
# 「定理証明手習い」TLP 第7章

## CTX?/SUB 定理の証明
*)

(**
- 定理 (CTX?/SUB s1 s2) ... S式 s1 と s2 の両方にシンボル "?" が含まれているなら、
s1 に含まれるシンボル "?" を s2 に置き換えても "?" が含まれる。


TLP にしたがって、定理についても真偽を "T" と "NIL" で表します。
定理が真であるとは、命題の値が常に"T"である（または、非"NIL"である)ことと同値です。
 *)

(**
補題を使います。

- S式 s1 と s2 のどちらかにシンボル "?" が含まれていたら、
両者をCONSした結果にも "?" が含まれる。

補題も定理も、if式の条件の成立・非成立で場合分けして、証明を進めています。
*)

Lemma l_ctxp_cons (s1 s2 : star_exp) : (ctxp s1) || (ctxp s2) = (ctxp (S_CONS s1 s2)).
Proof.
  rewrite /=.
    by case: ifP.
Qed.

Theorem ctxp_sub (x y : star_exp) : (ctxp x) -> (ctxp y) -> (ctxp (sub x y)).
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
 *)

(**
---------------
# 補足説明

## 証明の詳細 （``case: ifP`` と ``move/eqP`` について)
*)

(**
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
                      (if (n == 42) then true else false).
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
# 補足説明

## 他の方法との比較
*)

(**
- sumbool を使う - 場合分けが多い。
*)

Require Import Arith.
Goal forall (n : nat), n = 42 -> if eq_nat_dec n 42 then true else false.
Proof.
  move=> n H.
  case: ifP.
  (* Goal : Nat.eq_dec n 42 -> true *)
  - done.
  - case: (Nat.eq_dec n 42) => /=.
    (* Goal : n = 42 -> true = false -> false *)
    + done.
    (* Goal : n <> 42 -> false = false -> false *)
    + done.
Qed.

(**
- 自然数の同値判定の関数だけ使う - 同様に証明できる。
  型毎に判定の関数を覚えておく必要がある。Notation で逃げられるが。
*)

Goal forall (n : nat), n = 42 -> if eqn n 42 then true else false.
Proof.
  move=> n H.
  case: ifP.
  (* Goal : eqn n 42 -> true *)
  - done.
  (* Goal : eqn n 42 = false -> false *)
  - move/eqnP.
  (* Goal : n <> 42 -> false *)
    done.
Qed.


(**
--------------
# 補足説明

## eqMixin のまとめ
*)

(**

| eqType   | sort  | op | axiom | Module (3) | 

|:----------------|:--------|:---------------|:---------------|:---------------|

| unit_eqType     | unit    | fun _ _ => true  | unit_eqP     |                |

| bool_eqType     | bool    | eqb (1)        | eqbP           |                |

| nat_eqType      | nat     | eqn (2)        | eqnP           |                |

| ascii_eqType    | ascii   | eqb (+)        | eqb_spec (+)   | Ascii   |

| string_eqType   | string  | eqb (+)        | eqb_spec (+)   | String  |

| seq_eqType eT   | seq T   | eqseqP         | eqseq          |                |

| prod_eqType eT  | prod T  | pair_eq        | pair_eqP       |                |

| option_eqType eT | option T | opt_eq        | opt_eqP        |                |

| star_eqType eT   | star T   | eqCons        | star_eqP       | 本資料で定義    |



(1) Standard Coq では、beq

(2) Standard Coq では、beq_nat

(3) 空欄は、Moduleの外からも参照可能であるため、省いた。

(+) Standard Coq で定義

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

(**
----------------
# Collective述語になれるようにする。
 *)

(**
\in (∈) の 左側の文字(ascii)、右側に文字列(string) が書けるようにする。
*)

Section Collective.

  Fail Compute "C"%char \in "ABCD".         (* collective述語 *)
  Fail Compute "ABCD" "C"%char.             (* applicative述語 *)
  
  Fixpoint in_string (s : string) (c : ascii) : bool :=
    match s with
    | EmptyString => false
    | String c' s' => (Ascii.eqb c c') || in_string s' c
    end.
  Coercion pred_of_string (s : string) : pred_class := in_string s.
  
  Compute in_string "ABCD" "C"%char.   (* true *)
  
  Canonical string_predType := @mkPredType ascii string pred_of_string.
  Canonical mem_string_predType := mkPredType pred_of_string.
  Check string_predType : predType ascii.

End Collective.
Check string_predType : predType ascii.

Compute "C"%char \in "ABCD".                (* true *)
Compute "E"%char \in "ABCD".                (* false *)
Fail Compute "ABCD" "C"%char.               (* applicative述語 *)

(* END *)
