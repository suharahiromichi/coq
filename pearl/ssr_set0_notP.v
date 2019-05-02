(**
Mathcomp の subset について (Proof Pearl ##3)
======
2019/05/02

この文書のソースコードは以下にあります。


https://github.com/suharahiromichi/coq/blob/master/pearl/ssr_set0_nP.v

 *)

(**
# 説明

Mathcomp で、型 ``T : finType`` を全体集合とするとき、
型 ``T -> bool`` の関数、すなわち述語 ``p : pred T`` 
で決まる部分集合を考えます。

その部分集合が空集合、あるいは、濃度が0である場合、
述語 p は常に false を返すはずです。
その補題を証明してみます。
*)

(*
# コード例

## 空集合の場合についての証明

証明そのものはストレートですが、
setP や inE という、知らなければ使えない補題が必須になる例です。
 *)

From mathcomp Require Import all_ssreflect.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
(* Set Print All. *)

Section Test.

  Lemma set0_notPP (A : finType) (p : pred A) :
    [set x | p x] = set0 <-> (forall x, ~ p x).
  Proof.
    split.
    - move/setP => H x.
      move: (H x).
      rewrite 2!inE.
        by move/negP.
      
    - move=> H.
      apply/setP => x.
      rewrite 2!inE.
        by apply/negP.
  Qed.
  
  Lemma set0_notPE (A : finType) (p : pred A) :
    ([set x | p x] == set0) = [forall x, ~~ p x].
  Proof.
    apply/idP/idP.
    - move/eqP => H.
      apply/forallP => x.
      apply/negP.
      move: x.
        by apply/set0_notPP.

    - move=> H.
      apply/eqP/set0_notPP.
      move/forallP in H.
      move=> x.
        by apply/negP.
  Qed.
  
(**
## 集合表記のバリエーション

集合風な表記の場合についても、証明しておきます。
 *)
  
  Lemma set0_notP' (A : finType) (p : pred A) :
    ([set x in p] == set0) = [forall x, ~~ p x].
  Proof.
      by apply: set0_notPE.
  Qed.

(**
   上記の構文糖です。
 *)
  
  Lemma set0_notP'' (A : finType) (p : pred A) :
    ([set x | x \in p] == set0) = [forall x, ~~ p x].
  Proof.
      by apply: set0_notPE.
  Qed.  


(**
## 濃度が0である場合についての証明    

空集合であることと濃度が0であることは同値ですが、それについても証明しておきます。
*)

  Lemma card0_notP (A : finType) (p : pred A) :
    (#|[set x in p]| == 0) = [forall x, ~~ p x].
  Proof.
    rewrite cards_eq0.
    apply: set0_notPE.
  Qed.


(**
## 補足

set0_notP' が直接証明できるための補題
*)

  Lemma test (A : finType) (p : pred A) :
    forall x : A, ~ p x -> forall x, (x \in p) = false.  
  Proof.
    Admitted.


(**
# 最初に使った箇所

FRAP Map.v の Mathcomp への移植
*)


(**
# 例題
*)
  
  (* 例題 *)
  Definition fmap (A : finType) (B : Type) := A -> option B.

  Definition option_dec B (x : option B) :=
    match x with
    | Some _ => true
    | None => false
    end.
  
  Definition dom A B (m : fmap A B) : {set A} := [set x | option_dec (m x)].

  Lemma domE A B (m : fmap A B) :
    (dom m == set0) = ([forall k, option_dec (m k) == false]).
  Proof.
    apply/idP/idP => H.
    
    - apply/forallP => x.
      rewrite eqbF_neg.

      rewrite set0_notPE in H.
      move/forallP in H.
      move: (H x) => {H} H.
      done.
      
    - rewrite set0_notPE.
      apply/forallP => x.
      
      move/forallP in H.
      move: (H x) => {H} H.
      rewrite eqbF_neg in H.
      done.
  Qed.

End Test.

(* END *)

