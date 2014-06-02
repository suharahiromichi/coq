Require Import ssreflect.

(**
# 第7回 ソースファイルの分割とコンパイル/SectionとModule (2014/05/18)

http://qnighy.github.io/coqex2014/ex7.html
*)

(**
## 課題31 (種別:A / 締め切り : 2014/05/25)

Sectionを使って、非空なリストを表すposlistを定義する。この定義を埋めよ。
*)

(* Section の練習 *)

Section Poslist.
  (* このセクションの中では、Aが共通の変数として使える。 *)
  Variable A : Type.
  (* 非空なリスト *)
  Inductive poslist : Type :=
  | base of A
  | cons of A & poslist.

  Section Fold.
    (* 二項演算 *)
    Variable g : A -> A -> A.

   (* gによって畳み込む。
    * 次のどちらかを定義すること。どちらでもよい。
    * 左畳み込み : リスト [a; b; c] に対して (a * b) * c を計算する。
    * 右畳み込み : リスト [a; b; c] に対して a * (b * c) を計算する。
    *)
    Definition fold : poslist -> A :=   (* 右畳み込み *)
      fun l =>
        (fix fold' (l' : poslist) : A :=
           match l' with
             | base a => a
             | cons a l'' => g a (fold' l'')
           end) l.
  End Fold.

  Check poslist.                            (* : Type *)
  Check base.                               (* : A -> poslist A *)
  Check cons.                               (* : A -> poslist A -> poslist A *)
  Check fold.         (* : (A -> A -> A) -> poslist A -> A  *)
End Poslist.
(* Poslistから抜けたことにより、poslistは変数Aについて量化された形になる。 *)

Check poslist.                              (* : Type -> Type *)
Check base.                                 (* : forall A : Type, A -> poslist A *)
Check cons.                                 (* : forall A : Type, A -> poslist A -> poslist A *)
Check fold.           (* : forall A : Type, (A -> A -> A) -> poslist A -> A  *)

(* このリストに関するmap関数 *)
Section PoslistMap.
  Variable A B : Type.
  Variable f : A -> B.

  Definition map : poslist A -> poslist B :=
      fun l =>
        (fix map' (l' : poslist A) : poslist B :=
           match l' with
             | base a => base B (f a)
             | cons a l'' => cons B (f a) (map' l'')
           end) l.

  Check map.                                (* : poslist A -> poslist B *)
End PoslistMap.

Check map.        (* : forall A B : Type, (A -> B) -> poslist A -> poslist B *)

(**
ヒント

同じ変数や仮定を使いまわすときは、この例のようにSectionで囲うと便利です。

Sectionから抜けると、変数として仮定されていたものがforallの形でSection内の定義に自動的に付
加されます。

Section内の変数はVariable, Variablesで宣言します。仮定は、Hypothesis, Hypothesesで宣言しま
す。(これらの効果は同じです。意味に応じて使い分けてください。)

Variableの亜種として、Contextというものもあります。Section内では、DefinitionとLetは異なる効
果を持ちます。気になる人は確認してみてください。

*)
