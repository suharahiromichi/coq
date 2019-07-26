(**
リストのリフレクション補題
======
2019/07/25

この文書のソースコードは以下にあります。


https://github.com/suharahiromichi/coq/blob/master/pearl/ssr_list_1.v

 *)

(**
# 説明

Mathcomp の seq は、seq.v の中で、

``Notation seq := list``


という具合に、list のNotation (構文糖）として定義されていて、
Standard Coq の list と同じものであることが判ります。

（注記）

括弧による表記については、``[::]`` など、MathcompのNotationで上書きされるので、
かなり変わったものになりますが、支障にはなりません。
ここでは、型としてはseqを、括弧の表記はMathcompの表記を使いますが、
データ型として「リスト」と呼ぶことにします。

（注記終わり）

Mathcomp の中から、Standard Coq で定義されたリストの命題を使用することができます。
当然、おなじ意味（同値）な命題もあります。

実際には、Standard Coqでは Prop型の命題（述語）として、
Mathcompではbool型を返す関数として定義されているわけですが、
それらの間で同値性を示すリフレクション補題を証明することで、
相互の変換ができ（リフレクションですね）、証明が捗ることがあるかもしれません。
*)

(**
# コード例 その1
*)

Require Import List.
From mathcomp Require Import all_ssreflect.

Section List_1_1.

(**
最初の例は、Standard Coq の Lists/List.v で定義されている Forall と Exists です。
述語Pが、リストの要素のすべてで成り立つ、あるいは、ある要素で成り立つ、
ことを示す命題です。（∀と∃の意味の、forallとexists とは別な意味です。）
 *)

  Check Forall : forall A : Type, (A -> Prop) -> seq A -> Prop.
  Check Exists : forall A : Type, (A -> Prop) -> seq A -> Prop.

(**
これらに対して、Mathcomp では、
ssreflect/seq.v で all と has という関数が定義されています。

@は、implicitな引数を表示するために使っています。
この場合、型Tの指定は、引数として省略できます。
*)

  Check @all : forall A : Type, (A -> bool) -> seq A -> bool.
  Check @has : forall A : Type, (A -> bool) -> seq A -> bool.  

(**
ここでは、型しか示しませんが、実際の定義はそれぞれのソースコードを参照してください。

Standard Coq の Forall と Exists は、
(A->Prop)型の述語と、A型のリストをとり、全体としてProp型を返します。

Mathcop の allと has は、(A->bool)型の関数と、A型のリストをとり、
全体としてbool型を返します。
*)

(**
Forall と all の間のリフレクション補題を次に示します。
*)
  Lemma ForallP {A : Type} (P : A -> Prop) (p : A -> bool) :
    (forall (a : A), reflect (P a) (p a)) ->
    forall (s : seq A), reflect (Forall P s) (all p s).
  Proof.
    move=> H s.
    apply/(iffP idP).
    - elim: s => [Hp | a s IHs /= /andP].
      + by apply: Forall_nil.
      + case.
        move/H => Hpa Hps.
        apply: Forall_cons.
        * done.
        * by apply: IHs.
    - elim: s => /= [| a s IHs].
      + done.
      + move=> HP.
        apply/andP.
        inversion HP; subst.
        split.
        * by apply/H.
        * by apply IHs.
  Qed.

(**
``reflect (Forall P s) (all p s)``
が、Forall と all が同値であることを示す
リフレクション補題で、これだけで同値であることを示します。

しかし、(A->Prop)型の述語P と、(A->bool)型の関数p とがリフレクション関係である
ことを条件としなければなりません。なので、前提に
``reflect (P a) (p a)``
が必要となります。

リフレクション補題をしめす reflect の定義は、
ssreflect/ssrbool.v にある定義か、
文献 [1.] を参照してください。
*)
  
(**
Exists についても同様です。
*)
  Lemma ExistsP {A : Type} (P : A -> Prop) (p : A -> bool) :
    (forall (a : A), reflect (P a) (p a)) ->
    forall (s : seq A), reflect (Exists P s) (has p s).
  Proof.
    move=> H s.
    apply/(iffP idP).
    - elim: s => [Hp | a s IHs /= /orP].
      + done.
      + case=> [Hpa | Hpa].
        * apply: Exists_cons_hd.
            by apply/H.
        * apply: Exists_cons_tl.
            by apply: IHs.
    - elim: s => /= [| a s IHs] HP.
      + by inversion HP.
      + apply/orP.
        inversion HP; subst.
        * left.
            by apply/H.
        * right.
            by apply: IHs.
  Qed.

End List_1_1.

(**
# 実行例 その1

最初に、ここで証明したリフレクション補題を使う例です。
*)

Goal Forall (fun n => n == 1) [:: 1; 1; 1; 1].
Proof.
  apply/ForallP.
(**
``apply/ForallP`` がゴールに対してリフレクション補題を使うことを示します。
詳細は、文献 [2.] の 3.7節を参照してください。

すると、ForallP の前提部分の証明を求められます。
``a == 1`` と同値な命題は ``a = 1`` ですから、補題 eqP
*)

Check eqP : reflect (_ = _) (_ == _).

(**
を使って証明することができます。
*)
  - move=> a.
      by apply: eqP.

(**
残った

``all (fun a => (a == 1) == true) [:: 1; 1; 1; 1]``


については、「計算」で真偽を決定することができるので、
done で証明を終了することができます。
*)
  - done.
Qed.
    
(**
リフレクション補題を使わない場合は、
Forall のコンストラクタである、Forall_cons と Forall_nil を適用して
ゴールの要素を個々に証明することになります。
*)

Check Forall_cons :
  forall A  (P : A -> Prop) x l, P x -> Forall P l -> Forall P (x :: l).
Check Forall_nil :
  forall A  (P : A -> Prop), Forall P [::].

Goal Forall (fun n => n == 1) [:: 1; 1; 1; 1].
Proof.
  apply: Forall_cons.
  - done.
  - apply: Forall_cons.
    + done.
    + apply: Forall_cons.
      * done.
      * apply: Forall_cons.
        ** done.
        ** apply: Forall_nil.
Qed.

(**
タクティカルの利用して、短く書くことは可能ですが、
本質的な操作は変わらないことに注意してください。
*)

Goal Forall (fun n => n == 1) [:: 1; 1; 1; 1].
Proof.
  do ! apply: Forall_cons => //=.
Qed.

(**
# コード例 その2
*)

Section List_1_2.

(**
次の例は、指定の値と同じ値がリストの中に存在することを示す In です。
Starndard Coq の場合は、値とリストをとる述語 In、
Mathcomp の場合は、\in という中置記法の演算子を使います。
*)  

  Lemma In_inb {A : eqType} (x : A) (s : seq A) : In x s <-> x \in s.
  Proof.
    elim: s.
    - done.
    - move=> a s IHs.
      split=> /=; rewrite inE.
      + case=> H.
        * by apply/orP/or_introl/eqP.
        * by apply/orP/or_intror/IHs.
      + move/orP; case.
        * move/eqP => ->.
            by left.
        * move=> H.
          move/IHs in H.
            by right.
  Qed.
  
  Lemma InP {A : eqType} (x : A) (s : seq A) : reflect (In x s) (x \in s).
  Proof.
    apply: (iffP idP) => H.
    - by apply/In_inb.
    - by apply/In_inb.
  Qed.

End List_1_2.

(**
# 実行例 その2
*)

Goal In 3 [:: 1; 2; 3; 4].
Proof.
  apply/InP.
(**
ここで証明したリフレクション補題 InP を使うと、
Goal として: ``3 \in [:: 1; 2; 3; 4]`` が得られます。
これについても、「計算」で真偽を決定することができるので、
done で終了します。
*)
  
  done.
Qed.

(**
# 参考文献

[1.] リフレクションのしくみをつくる

https://qiita.com/suharahiromichi/items/9cd109386278b4a22a63


[2.] 萩原学 アフェルト・レナルド 「Coq/SSReflect/MathCompによる定理証明」 森北出版

(* END *)
