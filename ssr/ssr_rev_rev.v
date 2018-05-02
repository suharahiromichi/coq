(**
Coq/SSReflect/MathComp による証明の例

[2018_05_19 ProofCafe @OSC名古屋]

線形リストを反転(reverse)する関数について：

[1] 二種類の定義が同じであるこを証明する。

[2] 2回反転するともとに戻ることを証明する。
*)
From mathcomp Require Import all_ssreflect.
From mathcomp Require Import ssralg.
Require Import ZArith.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Set Print All.

Section Rev.
  (** 任意のT型のデータについて証明する。 *)
  (** Sectionの外から適当な型を与えたり、データから型を推論できる。  *)
  Variable T : Type.
  
  (** * 二種類のreverseの定義 *)
  
  (** ** rcons を使った定義 *)
  (** リストの末尾に要素を置く関数を使う。 *)
  Definition rcons l (a : T) := l ++ [:: a].
  
  Fixpoint rev1 (l : seq T) : seq T :=
    match l with
    | nil    => nil
    | h :: t => rcons (rev1 t) h
    end.
  
  (** ** 末尾再帰を使った定義 *)
  Fixpoint catrev (l m : seq T) : seq T :=
    match l with
    | [::] => m
    | x :: l => catrev l (x :: m)
    end.
  
  Definition rev2 (l : seq T) : seq T := catrev l [::].
  
  (** ** 二種類の定義が同じであることの証明 *)
  Lemma l_rev2_cat_r (l m n : seq T) :
    catrev l (m ++ n) = catrev l m ++ n.   (* 第2引数がappendのとき *)
  Proof.
    elim: l m => [| x l IHl m] /=.
    + done.
    + rewrite -[x :: m ++ n]cat_cons.
      rewrite (IHl (x :: m)).
      done.
  Qed.
  
  Theorem rev1_rev2 (l : seq T) : rev1 l = rev2 l.
  Proof.
    rewrite /rev2.
    elim: l => [| a l IHl] /=.
    - done.
    - rewrite IHl /rcons.
      rewrite -l_rev2_cat_r.
      done.
  Qed.
  
  (** * 2回反転すると同じ(対合)であることを証明 *)
  (** ** rev1 が対合であることを証明 *)
  Lemma rcons_rev1 (x : T) (l : seq T) : rev1 (rcons l x) = x :: (rev1 l).
  Proof.
    elim: l => [| x' l IHl] /=.
    - done.
    - rewrite IHl.
      done.
  Qed.
  
  Theorem rev1_involutive (l : seq T) : rev1 (rev1 l) = l.
  Proof.
    elim: l => [| n l IHl] /=.
    - done.
    - rewrite rcons_rev1.
      rewrite IHl.
      done.
  Qed.
  
  (** ** rev2 が対合であることを証明。rev1を経由する例。 *)
  Theorem rev2_rev2 (l : seq T) : rev2 (rev2 l) = l.
  Proof.
    rewrite -!rev1_rev2.
    apply rev1_involutive.
  Qed.
  
  (** ** rev2 が対合であることを証明。直接証明する例。 *)
  Theorem l_rev2_cat_l (l m n : seq T) :
    catrev (l ++ m) n = catrev m [::] ++ catrev l n. (* 第1引数がappendのとき *)
  Proof.
    elim: l n => [n | a l IHl n] /=.
    - rewrite -l_rev2_cat_r.
      done.
    - rewrite IHl.
      done.
  Qed.
  
  Lemma rev2_rev2' (l : seq T) : rev2 (rev2 l) = l.
  Proof.
    rewrite /rev2.
    elim: l => [| a l IHl] /=.
    - done.
    - rewrite (l_rev2_cat_r l [::] [:: a]).
    - rewrite (l_rev2_cat_l (catrev l [::]) [::a] [::]).
      rewrite IHl.
      done.
  Qed.
End Rev.

(** * 参考文献 *)
(**
[1] "Mathematical Components"

本家。[https://math-comp.github.io/math-comp/]
*)

(**
[2] 萩原学、アフェルト・レナルド 「Coq/SSReflect/MathComp」 森北出版

SSReflect本。おすすめ。数学の定理の証明がテーマである。
出版社のページ：[http://www.morikita.co.jp/books/book/3287]
*)

(**
[3] Ilya Sergey, "Programs and Proofs"

PnP。プログラムの証明をテーマにしている。
[http://ilyasergey.net/pnp/]
 *)

(**
[4] Assia Mahboubi, Enrico Tassi, "Mathematical Components"

MCB。MathCompライブラリのしくみの説明が詳しい。
[https://math-comp.github.io/mcb/]
*)

(**
[5] Georges Gonthier, Assia Mahboubi, Enrico Tassi,
"A Small Scale Reflection Extension for the Coq system"

GMT。SSReflect拡張部分のリファレンスマニュアル。
[https://hal.inria.fr/inria-00258384v17/document]
 *)

(* END *)
