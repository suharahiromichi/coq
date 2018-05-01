(**
Coq/SSReflect/MathComp による証明の例

線形リストを反転(reverse)する関数についての証明

2018_05_19 OSC名古屋 ProofCafe 
*)
From mathcomp Require Import all_ssreflect.
From mathcomp Require Import ssralg.
Require Import ZArith.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Set Print All.

Section Rev.
  Variable T : Type.                        (* 任意のT型のデータについて、 *)

  (** # 二種類のreverseの定義 *)
  
  (** ## rcons を使った定義 *)
  Definition rcons l (a : T) := l ++ [:: a]. (* リストの末尾に要素を置く関数 *)
  
  Fixpoint rev1 (l : seq T) : seq T :=      (* rconsを使った、よくある定義 *)
    match l with
    | nil    => nil
    | h :: t => rcons (rev1 t) h
    end.
  
  (** ## 末尾再帰を使った定義 *)
  Fixpoint catrev (l m : seq T) : seq T :=
    match l with
    | [::] => m
    | x :: l => catrev l (x :: m)
    end.
  
  Definition rev2 (l : seq T) : seq T := catrev l [::].
  
  (** # 補題（予備定理）を証明する。  *)
  
  (** ## rev1 に関する補題を証明する。  *)
  Lemma rcons_rev1 (x : T) (l : seq T) : rev1 (rcons l x) = x :: (rev1 l).
  Proof.
    elim: l => [| x' l IHl] /=.
    - done.
    - rewrite IHl.
      done.
  Qed.
  
  (** ## rev2 に関する補題を証明する。  *)
  Lemma l_rev2_cat_r (l m n : seq T) :
    catrev l (m ++ n) = catrev l m ++ n.   (* 第2引数がappendのとき *)
  Proof.
    elim: l m => [| x l IHl m] /=.
    + done.
    + rewrite -[x :: m ++ n]cat_cons.
      rewrite (IHl (x :: m)).
      done.
  Qed.
  
  Lemma l_rev2_cat_l (l m n : seq T) :
    catrev (l ++ m) n = catrev m [::] ++ catrev l n. (* 第1引数がappendのとき *)
  Proof.
    elim: l n => [n | a l IHl n] /=.
    - rewrite -l_rev2_cat_r.
      done.
    - rewrite IHl.
      done.
  Qed.
  
  (** ## ふたつの定義が同じであることの証明 *)
  Theorem rev1_rev2 (l : seq T) : rev1 l = rev2 l.
  Proof.
    rewrite /rev2.
    elim: l => [| a l IHl] /=.
    - done.
    - rewrite IHl /rcons.
      rewrite -l_rev2_cat_r.
      done.
  Qed.
  
  (** # 対合(involutive)であることを証明する。 *)
  
  (** ## rev1 が対合であることを証明する。 *)
  Theorem rev1_involutive (l : seq T) : rev1 (rev1 l) = l.
  Proof.
    elim: l => [| n l IHl] /=.
    - done.
    - rewrite rcons_rev1.
      rewrite IHl.
      done.
  Qed.
  
  (** ## rev2 が対合であることを証明する。rev1を経由する。 *)
  Lemma rev2_rev2 (l : seq T) : rev2 (rev2 l) = l.
  Proof.
    rewrite -!rev1_rev2.
    apply rev1_involutive.
  Qed.
  
  (** ## rev2 が対合であることを証明する。直接証明する。 *)
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

(*
# Coq/SSReflect/MathComp の参考文献

- 本家

https://math-comp.github.io/math-comp/


- 萩原学、アフェルト・レナルド 「Coq/SSReflect/MathComp」 森北出版 2018

（SSReflect本。最近出版された。おすすめ。数学の定理の証明がテーマである。）


- Georges Gonthier, Assia Mahboubi, Enrico Tassi,

"A Small Scale Reflection Extension for the Coq system"

https://hal.inria.fr/inria-00258384v17/document

(GMT。SSReflect拡張部分のリファレンスマニュアル)


- Ilya Sergey,

"Programs and Proofs"

http://ilyasergey.net/pnp/

（PnP。プログラムの証明をテーマにしている。）


- Assia Mahboubi, Enrico Tassi,

"Mathematical Components"

https://math-comp.github.io/mcb/

（MCB。MathCompライブラリのしくみの説明が詳しい。）

 *)

(* END *)
