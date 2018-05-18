(**
Coq/SSReflect/MathComp による証明の例

2018_05_19 OSC名古屋2018 [ProofCafe www.proofcafe.org]

線形リストを反転(reverse)するプログラムについて：

[(1)] 二種類のプログラムが同じ結果になることを証明する。

[(2)] 2回実行するともとに戻ることを証明する。
*)
From mathcomp Require Import all_ssreflect.

Set Implicit Arguments.
Unset Strict Implicit.

Section Rev.
  (* 任意のT型のデータについて証明する。 *)
  (* Sectionの外から適当な型を与えたり、データから型を推論できる。  *)
  Variable T : Type.
  
  (** * 二種類のリスト反転のプログラムの定義 *)
  (** ** rcons を使ったプログラム *)
  (* リストの末尾に要素を置く関数を使う。 *)
  Definition rcons l (a : T) := l ++ [:: a].
  Fixpoint rev1 (l : seq T) : seq T :=
    match l with
    | nil    => nil
    | h :: t => rcons (rev1 t) h
    end.
  
  (** ** 末尾再帰を使ったプログラム *)
  Fixpoint revsub (l m : seq T) : seq T :=
    match l with
    | [::] => m
    | x :: l => revsub l (x :: m)
    end.
  Definition rev2 (l : seq T) : seq T := revsub l [::].
  
  (** ** 二種類のプログラムが同じであることの証明 *)
  (* revsubの第2引数がappendのときの補題 *)
  Lemma l_rev2_cat_r (l m n : seq T) :
    revsub l (m ++ n) = revsub l m ++ n.
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
  
  (** * 2回実行するともとに戻ることを証明 *)
  (** ** rev1 について証明 *)
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
  
  (** ** rev2 について証明。rev1を経由する例 *)
  (** すでにある定理を再利用する。 *)
  Theorem rev2_involutive (l : seq T) : rev2 (rev2 l) = l.
  Proof.
    rewrite -!rev1_rev2.
    apply: rev1_involutive.
  Qed.
  
  (** ** rev2 について証明。直接証明する例 *)
  (* revsubの第1引数がappendのときの補題 *)
  Lemma l_rev2_cat_l (l m n : seq T) :
    revsub (l ++ m) n = revsub m [::] ++ revsub l n.
  Proof.
    elim: l n => [n | a l IHl n] /=.
    - rewrite -l_rev2_cat_r.
      done.
    - rewrite IHl.
      done.
  Qed.
  
  Theorem rev2_involutive' (l : seq T) : rev2 (rev2 l) = l.
  Proof.
    rewrite /rev2.
    elim: l => [| a l IHl] /=.
    - done.
    - rewrite (l_rev2_cat_r l [::] [:: a]).
      rewrite (l_rev2_cat_l (revsub l [::]) [::a] [::]).
      rewrite IHl.
      done.
  Qed.
End Rev.

(** * 参考文献 *)
(**
[1.] "Mathematical Components"
[https://math-comp.github.io/math-comp/]

一次配布元。
*)

(**
[2.] 萩原学、アフェルト・レナルド 「Coq/SSReflect/MathComp」 森北出版
[http://www.morikita.co.jp/books/book/3287]

SSReflect本。おすすめ。数学の定理の証明がテーマである。
*)

(**
[3.] Ilya Sergey, "Programs and Proofs"
[http://ilyasergey.net/pnp/]

PnP。プログラムの証明をテーマにしている。
 *)

(**
[4.] Assia Mahboubi, Enrico Tassi, "Mathematical Components"
[https://math-comp.github.io/mcb/]

MCB。MathCompライブラリのしくみの説明が詳しい。
*)

(**
[5.] Georges Gonthier, Assia Mahboubi, Enrico Tassi,
"A Small Scale Reflection Extension for the Coq system"
[https://hal.inria.fr/inria-00258384v17/document]

GMT。SSReflect拡張部分のリファレンスマニュアル。
 *)
(**
[------------]

@suharahiromichi [https://sites.google.com/site/suharahiromichi]
*)

(* END *)
