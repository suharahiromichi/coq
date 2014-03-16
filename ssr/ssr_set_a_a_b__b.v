Require Import ssreflect ssrbool ssrnat.
Require Import ssrfun fintype finset.

Variable T : finType.

(* B ⊆ A のとき、A - (A - B) = B を証明する。 *)

(* finsetの中の定理を使用する。 *)
Lemma a_a_b__b (A B : {set T}) : B \subset A -> (A :\: (A :\: B)) = B.
Proof.
  move=> H.
  rewrite setDDr setDv set0U.
  by apply/setIidPr.
Qed.

(* 一旦 x \in A にして、論理式にリフレクトして証明する。 *)
Lemma a_a_b__b' (A B : {set T}) : B \subset A -> (A :\: (A :\: B)) = B.
Proof.
  move/setIidPr.
  move/setP => H.
  apply/setP. move: H.
  rewrite /eq_mem => H x.
  (* x \in A の形式になる。 *)
  rewrite -(H x) {H}.
  apply/setDP/idP.
  (* -> *)
  rewrite -in_setC setDE setCI in_setU.
  case=> H1. move/orP=> H2. apply/setIP.
  (* 論理式にばらした。 *)
  case H2 => H3 {H2}.
  split.
  by [].
  by move/setCP in H3.
  by rewrite setCK in H3.
  (* <- *)  
  move/setIP.
  case=> H1 H2.
  rewrite -in_setC.
  split.
  by [].
  apply/setCP.
  unfold not=> H3.
  move/setDP in H3.
  destruct H3.
  rewrite -in_setC in H0.
  move/setCP in H0.
  unfold not in H0.
  by [].
Qed.

(* END *)

