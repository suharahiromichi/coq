(**
Coq/SSReflect/MathComp による証明の例

2018_07_13 OSC名古屋2018 [ProofCafe proofcafe.connpass.com]
2020_06_27 ProofCafe #100

線形リストを反転(reverse)するプログラムについて：

(1) 二種類のプログラムが同じ結果になることを証明する。

(2) 2回実行するともとに戻ることを証明する(involutive)。

(3) 単射であることを証明する(injective)。
*)
From mathcomp Require Import all_ssreflect.

Set Implicit Arguments.
Unset Strict Implicit.

Section Rev.
  (* 任意のT型のデータについて証明する。 *)
  (* Sectionの外から適当な型を与えたり、データから型を推論できる。  *)
  Variable T : Type.
  
  (** * 二種類のリスト反転のプログラムの定義 *)
  (** rcons を使ったプログラム *)
  (* リストの末尾に要素を置く関数を使う。 *)
  Definition rcons' s (a : T) := s ++ [:: a].
  
  Fixpoint reverse (s : seq T) : seq T :=
    match s with
    | nil    => nil
    | h :: t => rcons' (reverse t) h
    end.
  
  (** 末尾再帰を使ったプログラム *)
  Fixpoint catrev (s1 s2 : seq T) : seq T :=
    match s1 with
    | [::] => s2
    | x :: s1 => catrev s1 (x :: s2)
    end.
  Definition rev (s : seq T) : seq T := catrev s [::].
  
  (** (1) 二種類のプログラムが同じであることの証明 *)
  (* 良く使う補題 *)
  Lemma cat_cons (x : T) (s1 s2 : seq T) :
    (x :: s1) ++ s2 = x :: (s1 ++ s2).
  Proof. done. Qed.
  
  (* catrevの第2引数がappendのときの補題 *)
  Lemma l_rev_cat_r (s s1 s2 : seq T) :
    catrev s (s1 ++ s2) = catrev s s1 ++ s2.
  Proof.
    elim: s s1 => [| x s IHs s1] /=.
    - done.
    - rewrite -[x :: s1 ++ s2]cat_cons.
      rewrite (IHs (x :: s1)).
      done.
  Qed.
  
  Theorem reverse_rev (s : seq T) : reverse s = rev s.
  Proof.
    rewrite /rev.
    elim: s => [| a l IHs] /=.
    - done.
    - admit.                                (* 答え参照 *)
  Admitted.
  
  (** (2) 2回実行するともとに戻ることを証明 *)
  (** reverse について証明 *)
  Lemma rcons_reverse (x : T) (s : seq T) :
    reverse (rcons' s x) = x :: (reverse s).
  Proof.
    elim: s => [| x' s IHs] /=.
    - done.
    - admit.                                (* 答え参照 *)
  Admitted.
  
  Theorem reverse_involutive (s : seq T) : reverse (reverse s) = s.
  Proof.
    elim: s => [| n s IHs] /=.
    - done.
    - admit.                                (* 答え参照 *)
  Admitted.
  
  (** (3) reverse が単射であることを証明 *)
  (** reverse について証明 *)
  Theorem reverse_injective s1 s2 : reverse s1 = reverse s2 -> s1 = s2.
  Proof.
    move=> H.
    admit.                                  (* 答え参照 *)
  Admitted.
  
  (** * 説明 *)
  (** (あ) リストの反転 reverse のような、誰でも書いてみる・良く使うコードにも、
      involutive や injective といった数学的な構造を持っています。
      ++ と reverse の分配法則というのもあります（証明してください！）。
  
      (い) reverse_injective は Software Fundations の 4 stars の問題です。
      それも比較的簡単に証明できてしまいました。
   *)
  
  (** * おまけ *)
  (** (2') 2回実行するともとに戻ることを証明 *)
  (** rev について証明。reverseを経由する例 *)
  (* すでにある定理を再利用する。 *)
  Theorem rev_involutive (s : seq T) : rev (rev s) = s.
  Proof.
    rewrite -!reverse_rev.
    apply: reverse_involutive.
  Qed.
  
  (** (2'') 2回実行するともとに戻ることを証明 *)
  (** rev について証明。直接証明する例 *)
  (* catrevの第1引数がappendのときの補題 *)
  Lemma l_rev_cat_l (s s1 s2 : seq T) :
    catrev (s ++ s1) s2 = catrev s1 [::] ++ catrev s s2.
  Proof.
    elim: s s2 => [n | a s IHs s2] /=.
    - rewrite -l_rev_cat_r.
      done.
    - rewrite IHs.
      done.
  Qed.
  
  Theorem rev_involutive' (s : seq T) : rev (rev s) = s.
  Proof.
    rewrite /rev.
    elim: s => [| a s IHs] /=.
    - done.
    - rewrite (l_rev_cat_r s [::] [:: a]).
      rewrite (l_rev_cat_l (catrev s [::]) [:: a] [::]).
      rewrite IHs.
      done.
  Qed.
  
  (** (3') reverse が単射であることを証明 *)
  (** rev について証明 *)
  Theorem rev_injective s1 s2 : rev s1 = rev s2 -> s1 = s2.
  Proof.
    move=> H.
    rewrite -[s1]rev_involutive.
    rewrite H.
    rewrite [LHS]rev_involutive.
    done.
  Qed.


  (** * 答え *)
  Theorem a_reverse_rev (s : seq T) : reverse s = rev s.
  Proof.
    rewrite /rev.
    elim: s => [| a l IHs] /=.
    - done.
    - rewrite IHs /rcons'.
      rewrite -l_rev_cat_r.
      done.
  Qed.
  
  Lemma a_rcons_reverse (x : T) (s : seq T) :
    reverse (rcons' s x) = x :: (reverse s).
  Proof.
    elim: s => [| x' s IHs] /=.
    - done.
    - rewrite IHs.
      done.
  Qed.
  
  Theorem a_reverse_involutive (s : seq T) : reverse (reverse s) = s.
  Proof.
    elim: s => [| n s IHs] /=.
    - done.
    - rewrite rcons_reverse.
      rewrite IHs.
      done.
  Qed.
  
  Theorem a_reverse_injective s1 s2 : reverse s1 = reverse s2 -> s1 = s2.
  Proof.
    move=> H.
    rewrite -[s1]reverse_involutive.
    rewrite H.
    rewrite [LHS]reverse_involutive.
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

(**
[3.] Benjamin C. Pierce "Software Fundations - Logical Fundataion"
[https://softwarefoundations.cis.upenn.edu/lf-current/Lists.html]
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
