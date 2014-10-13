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
坂口さん著「反復定理で遊ぼう」 1.5.2 から。
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

(** 1.5.2 例: {x | |x|a = |x|b }、語xにおける、文字aとbの出現回数が同じ。 *)
Definition lang (a b : char) : word char -> Prop :=
  fun (s : word char) => count (fun c => c == a) s = count (fun c => c == b) s.

(** lang が正規言語でないことを証明する *) (* 一部を冗長に書き直している。 *)
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
  - rewrite /lang.                          (* Goal : lang a b (nseq k a ++ nseq k b) *)
    rewrite !count_cat !non_regular.count_nseq.
    rewrite !eqxx.                          (* a == a と b == b の書き換え。 *)
    rewrite (eq_sym b a) H.                 (* a == b と b == a の書き換え。 *)
    by [].
  - move=> u v w H0.
    move: H0 (H0).                          (* 前提をふたつにコピーする。 *)
    case/nseq_eq_cat => <-.
    case/nseq_eq_cat => <-.
    move=> <-.
    move: {u v w} (size u) (size v) (size w) => u v w.
    rewrite !cat_nseq_eq addnA.
    move/(f_equal size); rewrite !size_nseq => -> {k}; case: v => // v _.
    exists 0; move=> /=.
    (* Goal : lang a b (nseq u a ++ nseq w a ++ nseq (u + v.+1 + w) b) -> False *)
    rewrite /lang.
    rewrite !count_cat !non_regular.count_nseq.
    rewrite !eqxx.
    rewrite (eq_sym b a) H => /=.
    nat_norm => /eqP.                       (* 以降、数式の計算をする。 *)
    rewrite !mul1n -addnS -addSn.
    rewrite eqn_add2l -{1}[w]add0n.         (* 両辺のuを消す。 *)
    rewrite eqn_add2r.                      (* 両辺のwを消す。 *)
    by [].
Qed.

(* END *)
