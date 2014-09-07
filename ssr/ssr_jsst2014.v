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

(**
COQの基本
predicative_example.v
*)


(**
SSREFLECT
*)
(**
elimタクティク

ユーザが帰納法の補題を選べる (書き方: elim/myT_ind) (NB: 必要な時:
mutual inductive types, nested types)
*)

(*
elim/P => [|n' IH] := move=> n; elim (P n); move=> [|n' IH].

つまり、n でなく (P n) 帰納法をおこなう。
*)

(**
等式の生成

tactics_example.v
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

(**
move/H の意味。

view_example.v
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

(* ビューヒントによって、補題(例：iffLR)が適用される。 *)
Goal forall (P Q : Prop), (P <-> Q) -> P -> Q.
Proof.
  move=> P Q PQ.
  move/PQ.
  Undo 1.
  move/(iffLR PQ).
  done.
Qed.

(**
ssrboolのboolP

ssrbool_example.v
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

(**
ssrboolのifP

ssrbool_example.v
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

(* END *)

(* 
SSREFLECT
eqtype_example.v
ssrnat_example.v
fintype_example.v
*)

(*
MATHCOMP
bigop_example.v
tuple_example.v
permutation_example.v
 *)
