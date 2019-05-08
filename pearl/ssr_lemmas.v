(**
Mathcomp 知らないと使えない補題たち (Proof Pearl ##5)
======
2019/05/08

この文書のソースコードは以下にあります。


https://github.com/suharahiromichi/coq/blob/master/pearl/ssr_lemmas.v

 *)

(**
# 説明

*)

From mathcomp Require Import all_ssreflect.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
(* Set Printing All. *)

(**
# eqE eqbE eqnE eqseqE
*)

Lemma test1 : forall n, n.+1.+1 + 1 == n.+2 + 1.
Proof.
  move=> n.
  rewrite !eqE /= -eqE.
  done.
Qed.

(**
# eqP
 *)

Lemma test2 : forall n m, n == m -> n.+1.+1 + 1 = m.+2 + 1.
Proof.
  move=> n m H.
  Check eqP H.
  rewrite (eqP H).
  done.
Qed.

(**
# eqP ifP
 *)

Lemma test4 : forall (n m : nat), if n == m then true else true.
Proof.
  move=> n m.
  case: ifP => H.
  Undo 1.
  case: eqP => H.
  - done.
  - done.
Qed.

(**
# inE memE topredE
 *)

(* rewrite inE *)


(**
# ffunP setP
 *)

Lemma test5 : forall (s1 s2 : {set bool}), s1 = s2.
Proof.
  move=> s1 s2.
  apply/setP.
  move=> x.
Admitted.

(* END *)
