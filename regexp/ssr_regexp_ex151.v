Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq fintype.
Require Import div prime.
Require Import regexp pumping.

(**
https://www.ps.uni-saarland.de/~doczkal/regular/
の Coq development からリンクされる、
ConstructiveRegularLanguages.tgz
を展開して、make する。
*)
(**
以下は、その同じ場所で実行する。
*)

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

(**
Tukuba Coq Users' Grup 「Coqによる定理証明」
坂口さん著「反復定理で遊ぼう」 1.5.1 から。
*)
Variable char : finType.

Lemma nseq_eq_cat (x : char) n xs ys :
  nseq n x = xs ++ ys -> nseq (size xs) x = xs /\ nseq (size ys) x = ys.
Proof.
  elim: n xs ys => //=.
  - by do 2 case=> //=.
  - move=> n IH [] //=.
    + by case=> //= y ys [] H H0; subst y ys; rewrite size_nseq.
    + by move=> a xs ys [] H; subst a; case/IH => {2}<- {2}<-. (* 2番め出現でrewriteする。 *)
Qed.

Definition lang (a b : char) : word char -> Prop := (* 1.5.1 例: {a^n b^n | n : nat}  の言語 *)
  fun (s : word char) => exists (n : nat), s = nseq n a ++ nseq n b.

(* 一部を冗長に書き直している。 *)
Lemma anbn_non_regular (a b : char) :
  a != b -> ~ regular (lang a b).
Proof.
  move/negbTE => H.
  apply pumping => k.
  exists [::].
  exists (nseq k a).
  exists (nseq k b).
  rewrite size_nseq leqnn /=.
  split; last split.
  - by [].
  - exists k. by [].
  - move=> u v w H0.
    move: H0 (H0).
    do 2 case/nseq_eq_cat => <-.
    move=> <-.
    move: {u v w} (size u) (size v) (size w) => u v w.
    rewrite !cat_nseq_eq addnA.
    move/(f_equal size); rewrite !size_nseq => -> {k}; case: v => // v _.
    exists 0; case=> /= x H0.
    move: (f_equal (count (fun c => c == a)) H0).
    move: (f_equal (count (fun c => c == b)) H0).
    rewrite !count_cat !non_regular.count_nseq !eqxx eq_sym.
    rewrite H !mul1n !mul0n.
    nat_norm=> <- /eqP; rewrite addnCA -addSn -{1}(add0n (u + w)) eqn_add2r.
    by [].
Qed.

(* END *)
