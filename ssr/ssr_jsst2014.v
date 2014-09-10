(**
日本ソフトウェア科学会
チュートリアル(1) 定理証明支援系Coq入門

講師：アフェルト レナルド 先生
https://staff.aist.go.jp/reynald.affeldt/ssrcoq/coq-jssst2014.pdf
 *)

(**
首記の講演から興味のもとに抜粋し、例題を追加したものです。
内容の責任は  @suharahiromichi にあります。
 *)
Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq.

(***********************************
COQの基本  predicative_example.v
*)
(* see. ssr_jsst2014_predicative_example.v *)

(***********************************
SSREFLECT : elimタクティク

ユーザが帰納法の補題を選べる (書き方: elim/myT_ind) (NB: 必要な時:
mutual inductive types, nested types)
*)
(*
elim/P === move=> tmp; elim: (P tmp); move=> {tmp}
つまり、n でなく (P n) 帰納法をおこなう。
*)

(***********************************
SSREFLECT : 等式の生成 tactics_example.v
*)
Goal forall s1 s2 : seq nat, rev (s1 ++ s2) = rev s2 ++ rev s1.
Proof.
  move=> s1.
  move: (size s1) => n.
  Undo 1.
  move H : (size s1) => n.                  (* H : size s1 = n が前提に入る。 *)
  move: n s1 H.
  elim.
  - case => //.
    rewrite /=.
    move=> _ s2.
      by rewrite cats0.
  - move=> n IH.
    case=> // h t.
    case=> tn.
    move=> s2.
    rewrite /=.
    rewrite rev_cons.
    rewrite IH //.
    rewrite rcons_cat.
      by rewrite rev_cons.
Qed.

(***********************************
SSREFLECT : move/H の意味 view_example.v
*)
Goal forall (P Q : Prop), (P -> Q) -> P -> Q.
Proof.
  move=> P Q PQ.
  move/PQ.
  Undo 1.
  move=> tmp.
  move: (PQ tmp).
  move=> {tmp}.
  done.
Qed.

Goal forall (P Q : Prop), (P <-> Q) -> P -> Q.
Proof.
  move=> P Q PQ.
  move/PQ.
  Undo 1.
  move/(iffLR PQ).
  (* ビューヒントによって、補題(例：iffLR)が適用される。 *)
  done.
Qed.

(***********************************
SSREFLECT : apply/H の意味 view_example.v
*)
Goal forall (P Q : Prop), (P <-> Q) -> P -> Q.
Proof.
  move=> P Q PQ Hp.
  apply PQ.
  Undo.
  apply/PQ.
  Undo.
  apply/(iffLR PQ).
  (* ビューヒントによって、補題(例：iffLR)が適用される。 *)
  Undo.
  apply PQ, Hp.                             (* 続けてapplyする。 *)
  Undo.
  apply/PQ/Hp.
(* x == y に対する、 apply/idP/idP とは別の意味。. *)
Qed.

(***********************************
SSREFLECT : ssrboolのboolP ssrbool_example.v
*)
Lemma boolP_example : forall n : nat, n * n - 1 < n ^ n.
Proof.
  move=> n.
  case H : (n == 0).
  (* H : (n == 0) = true と (n == 0) = false になる。 *)
  Undo 1.
  case: (boolP (n == O)).
  (* スタックトップは、n == 0  *)
  - move/eqP.
    move=> ->.
    rewrite expn0.
    rewrite mul0n.
      by rewrite sub0n.
  (* スタックトップは、n != 0  *)
  - move=> n0.
    case: (boolP (n == 1)).
    + move/eqP.
      move=> ->.
      rewrite expn1.
      rewrite muln1.
        by rewrite subnn.
    + move=> n1.
      have [m Hm] : exists m, n = m.+2.
      * case: n n0 n1 => //.
        case=> // n _ _.
          by exists n.
      rewrite Hm.
      rewrite expnS.  
      rewrite expnS.
      rewrite mulnA.
      rewrite subn1.
      rewrite prednK; last first.
      * by rewrite muln_gt0.
      * rewrite leq_pmulr //.
          by rewrite expn_gt0.
Qed.

(***********************************
SSREFLECT : ssrboolのifP ssrbool_example.v
*)
Lemma ifP_example : forall n : nat, odd (if odd n then n else n.+1).
Proof.
  move=> n.
  case: ifP.
  - done.
  - move=> Hn.
    rewrite -addn1.
    rewrite odd_add.
      by rewrite Hn.
Qed.

(***********************************
SSREFLECT : eqtype_example.v
*)
(* see. ssr_jsst2014_eqtype_example.v *)

(***********************************
SSREFLECT : ssrnat_example.v
about leqP
*)
(* Standard Coq の例 *)
Goal forall n : nat, (n <= 5 \/ 5 < n)%coq_nat.
Proof.
  move=> n.
  Check (Compare_dec.le_gt_dec n 5) : {(n <= 5)%coq_nat} + {(n > 5)%coq_nat}.
  destruct (Compare_dec.le_gt_dec n 5).
  (* 前提 l : n <= 5 が追加される。n <= 5 を true に置き換えるわけではない。 *)
  auto.
  (* 前提 l : n > 5 が追加される。n > 5 を true に置き換えるわけではない。 *)
  auto.
  Show Proof.
Qed.

(* SSReflect の例 *)
Goal forall n : nat, (n <= 5) || (5 < n).
Proof.
  move=> n.
  case H : (n <= 5).
  (* 前提 H : (n <= 5) = true を追加する。ゴールの n <= 5 を true にする。 *)
  - done.
  (* 前提 H : (n <= 5) = false を追加する。ゴールの n > 5 を false にする。 *)
  - Check @negbT (n <= 5) : (n <= 5) = false -> ~~ (n <= 5).
    apply (@negbT (n <= 5)) in H.
    Undo 1.
    move/(@negbT (n <= 5)) in H.
    Undo 1.

    (* すこし遠回りだが。 *)
    move/negbT in H.                        (* ~~ (n <= 5) にする。 *)
    Search (_ = ~~ (_ <= _)).
    rewrite -ltnNge in H.                   (* n < 5 にする。 *)
    move : H.
    move=> ->.
    done.
    Undo 5.
    
    (* 一番短い例。 *)
    move/negbT : H.
      by rewrite -ltnNge.
(* pros: replace (n <= 5) by true, etc.
   cons: useless rewrite in the 2nd branch,
   does not scale to three way case analysis *)
Qed.

(* もっと SSReflect らしい例 *)
Goal forall n : nat, (n <= 5) || (5 < n).
Proof.
  move=> n.
  Check (leqP n 5).
  case: (leqP n 5).
  (* 前提に n <= 5 を追加する。ゴールは true || false *)
  done.
  (* 前提に 5 < 5 を追加する。ゴールは false || true *)
  done.
Qed.

(**
類似の定理（Comparison predicates）
Lemma leqP m n : leq_xor_gtn m n (m <= n) (n < m).
Lemma ltnP m n : ltn_xor_geq m n (n <= m) (m < n).
Lemma posnP n : eqn0_xor_gt0 n (n == 0) (0 < n).
Lemma ltngtP m n : compare_nat m n (m < n) (n < m) (m == n).
  *)

(***********************************
SSREFLECT : fintype_example.v
*)

(***********************************
MATHCOMP : bigop_example.v
*)

(***********************************
MATHCOMP : tuple_example.v
*)

(***********************************
MATHCOMP : permutation_example.v
 *)

(* END *)
