(**
Coq/SSReflect/MathComp による証明の例

2018_07_13 OSC名古屋2018 [ProofCafe proofcafe.connpass.com]
2020_06_27 ProofCafe #100

線形リストを反転(reverse)するプログラムについて：

(1) 二種類のプログラムが同じ結果になることを証明する。

(2) 2回実行するともとに戻ることを証明する。
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
  Definition rcons' l (a : T) := l ++ [:: a].
  
  Fixpoint reverse (l : seq T) : seq T :=
    match l with
    | nil    => nil
    | h :: t => rcons' (reverse t) h
    end.
  
  (** ** 末尾再帰を使ったプログラム *)
  Fixpoint catrev (l1 l2 : seq T) : seq T :=
    match l1 with
    | [::] => l2
    | x :: l1 => catrev l1 (x :: l2)
    end.
  Definition rev (l : seq T) : seq T := catrev l [::].
  
  (** (1) 二種類のプログラムが同じであることの証明 *)
  (* catrevの第2引数がappendのときの補題 *)
  Lemma l_rev_cat_r (l l1 l2 : seq T) :
    catrev l (l1 ++ l2) = catrev l l1 ++ l2.
  Proof.
    elim: l l1 => [| x l IHl l1] /=.
    - done.
    - rewrite -[x :: l1 ++ l2]cat_cons.
      rewrite (IHl (x :: l1)).
      done.
  Qed.
  
  Theorem reverse_rev (l : seq T) : reverse l = rev l.
  Proof.
    rewrite /rev.
    elim: l => [| a l IHl] /=.
    - done.
    - rewrite IHl /rcons'.
      rewrite -l_rev_cat_r.
      done.
  Qed.
  
  (** (2) 2回実行するともとに戻ることを証明 *)
  (** ** reverse について証明 *)
  Lemma rcons_reverse (x : T) (l : seq T) : reverse (rcons' l x) = x :: (reverse l).
  Proof.
    elim: l => [| x' l IHl] /=.
    - done.
    - rewrite IHl.
      done.
  Qed.
  
  Theorem reverse_involutive (l : seq T) : reverse (reverse l) = l.
  Proof.
    elim: l => [| n l IHl] /=.
    - done.
    - rewrite rcons_reverse.
      rewrite IHl.
      done.
  Qed.
  
  (** ** rev について証明。reverseを経由する例 *)
  (* すでにある定理を再利用する。 *)
  Theorem rev_involutive (l : seq T) : rev (rev l) = l.
  Proof.
    rewrite -!reverse_rev.
    apply: reverse_involutive.
  Qed.
  
  (** ** rev について証明。直接証明する例 *)
  (* catrevの第1引数がappendのときの補題 *)
  Lemma l_rev_cat_l (l l1 l2 : seq T) :
    catrev (l ++ l1) l2 = catrev l1 [::] ++ catrev l l2.
  Proof.
    elim: l l2 => [n | a l IHl l2] /=.
    - rewrite -l_rev_cat_r.
      done.
    - rewrite IHl.
      done.
  Qed.
  
  Theorem rev_involutive' (l : seq T) : rev (rev l) = l.
  Proof.
    rewrite /rev.
    elim: l => [| a l IHl] /=.
    - done.
    - rewrite (l_rev_cat_r l [::] [:: a]).
      rewrite (l_rev_cat_l (catrev l [::]) [:: a] [::]).
      rewrite IHl.
      done.
  Qed.
End Rev.

(** * 参考文献 *)
(**
[1.] "Mathematical Components"
[https://math-comp.github.io]

本家・一次配布元。日本語情報へのリンクもある。
*)

(**
[2.] 萩原学 アフェルト・レナルド 「Coq/SSReflect/MathCompによる定理証明」 森北出版
[http://www.morikita.co.jp/books/book/3287]
*)

(** * ProofCafe - 名古屋Coq勉強会 について *)
(**
Mathcomp/Coq などの定理証明器（定理証明支援システム）の使い方と、
プログラムや数学の問題の証明のしかたを勉強する会です。
あらかじめ指定したテキストをもとに、実際に証明をしながら進めていきます。

第4土曜日の午後、名古屋市内、または、オンラインで開催します。
参加費は無料です。できるだけPCを持参してください。

[https://proofcafe.connpass.com] 開催案内
*)

(**
[------------]

@suharahiromichi [https://sites.google.com/site/suharahiromichi]
*)

(* END *)
