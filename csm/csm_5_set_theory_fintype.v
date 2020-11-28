(**
Coq/SSReflect/MathComp による定理証明

5. 集合の形式化
======
2018_05_03 @suharahiromichi

テキストにない、finType 値をとる具体的な集合を与える試みをした。
 *)
From mathcomp Require Import all_ssreflect.
Require Import csm_5_set_theory.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Set Print All.

(**
# 5.5 fintype を用いた有限集合の形式化

これまでの ``M : Type`` を ``M : finTypr`` に変えることで、有限型の性質を使って、
有限型を母集合とするものが集合としての性質を満たすことを示す。
 *)
Definition p2S {M : finType} (pA : pred M) : mySet M :=
  fun (x : M) => if x \in pA then True else False.
Notation "\{ x 'in' pA \}" := (p2S pA).     (* x は飾り。 *)

Section fintypeを用いた有限集合.
  (* Set Printing Coercions. *)
  
  Variable M : finType.             (* これまでは ``M : Type`` だった。 *)
  
  (* myMotherSet =
     p2S (pred_of_simpl (pred_of_argType (Equality.sort (Finite.eqType M)))) *)
  Check @p2S M M.
  Check p2S M.
  Check @p2S M (mem M).
  Check p2S (mem M).
  Check @p2S M (pred_of_simpl (pred_of_argType (Equality.sort (Finite.eqType M)))).
  Check p2S (pred_of_simpl (pred_of_argType (Equality.sort (Finite.eqType M)))).
  
(**
## myMotherSet の有限型版
*)
  Check @myMotherSet M = \{ x in M \}.
  Lemma Mother_predT : myMotherSet = \{ x in M \}.
  Proof. by []. Qed.
  
  Locate "\in".             (* := in_mem x (mem A) *)
  (* \in については、csm_4_5_fintype.v も参照のこと。 *)
  
(**
## belong の有限型版
*)
  (* 左：集合の性質、右：有限型の性質 *)
  Lemma myFinBelongP (x : M) (pA : pred M) : reflect (x ∈ \{x in pA \}) (x \in pA).
  Proof.
    rewrite /belong /p2S.
    apply/(iffP idP) => H1.
    - Check (_ : (x \in pA) = true).
        by rewrite (_ : (x \in pA) = true).
    - have testH : (x \in pA) || ~~(x \in pA).
      + set t := x \in pA.
          by case: t.
      + move: testH.
        case/orP => [| Harg]; first by [].
        Check (_ : (x \in pA) = false).
        rewrite (_ : (x \in pA) = false) in H1; first by [].
        by apply: negbTE.
  Qed.
  (* 上記の説明はもっと短くできる。 @suharahiromichi *)
  Lemma myFinBelongP' (x : M) (pA : pred M) : reflect (x ∈ \{x in pA \}) (x \in pA).
  Proof.
    rewrite /belong /p2S.
    apply/(iffP idP) => H1.
    - by rewrite H1.
    - by case H : (x \in pA); last rewrite H in H1.
  Qed.
  
(**
## mySubset の有限型版
*)
  Locate "\subset".                    (* := subset (mem A) (mem B) *)
  (* \subset については、csm_4_5_fintype.v も参照のこと。 *)
  
  (* 左：集合の性質、右：有限型の性質 *)
  Lemma myFinSubsetP (pA pB : pred M) :
    reflect (\{ x in pA \} ⊂ \{ x in pB \}) (pA \subset pB).
  Proof.
    rewrite /mySub.
    apply/(iffP idP) => H.
    - move=> x /myFinBelongP => H2.
      apply/myFinBelongP.
      move: H => /subsetP.
      rewrite /sub_mem.
      by apply.
    - apply/subsetP.
      rewrite /sub_mem => x /myFinBelongP => HpA.
      apply/myFinBelongP.
      by apply H.
  Qed.
  
  (* fintype.v の補題 ： 有限型としての部分集合 *)
  Check predT_subset : forall (T : finType) (A : pred T),
      T \subset A -> forall x : T, x \in A.
  
  (* predT_subset の mySet版 *)
  Lemma Mother_Sub (pA : pred M) :
    myMotherSet ⊂ \{ x in pA \} -> forall x, x ∈ \{ x in pA \}.
  Proof.
    rewrite Mother_predT => /myFinSubsetP => H x.
    apply/myFinBelongP.
    by apply: predT_subset.
  Qed.

  (* fintype.v の補題 *)
  Check subset_trans : forall (T : finType) (A B C : pred T),
      A \subset B -> B \subset C -> A \subset C.
  
  (* subset_trans の mySet版 *)
  Lemma transitive_Sub' (pA pB pC : pred M) :
    \{ x in pA \} ⊂ \{ x in pB \} ->
    \{ x in pB \} ⊂ \{ x in pC \} ->
    \{ x in pA \} ⊂ \{ x in pC \}.
  Proof.
    move/myFinSubsetP => HAB /myFinSubsetP HBC.
      by apply/myFinSubsetP/(subset_trans HAB HBC).
  Qed.

  Lemma transitive_Sub'' (pA pB pC : pred M) :
    \{ x in pA \} ⊂ \{ x in pB \} ->
    \{ x in pB \} ⊂ \{ x in pC \} ->
    \{ x in pA \} ⊂ \{ x in pC \}.
  Proof.
    by apply: transitive_Sub.               (* see. 5.2 *)
  Qed.
End fintypeを用いた有限集合.  

(**
# 具体的なfinTypeを適用した例

以下はテキストから離れた内容である。 @suharahiromichi
 *)
Section 具体的なfinType.

(**
## 準備  

具体的な finType として、'I_5 を与える。
 *)
  (* 'I_5 の要素として、p0 を定義する。 *)
  Definition p0 := @Ordinal 5 0 is_true_true.
  Check p0 : 'I_5 : Type.
  Compute val p0.                           (* = 0 *)
  
  Check Finite.sort (ordinal_finType 5) : Type.
  Check              ordinal_finType 5  : finType.
  Check              ordinal_finType 5  : Type.      (* コアーション *)
  Check p0 : Finite.sort (ordinal_finType 5) : Type.
  Check p0 :              ordinal_finType 5  : Type. (* コアーション *)
  (** コアーションによって、(ordinal_finType 5) は型として見える。
      つまり、(ordinal_finType 5) は finType型クラスから作られた、型インスタンスである。 *)
  
  (* 'I_5 を要素とする集合を定義する。 *)
  Check @p2S : forall M : finType, pred M -> mySet M.
  
  (* see also. ssr/ssr_in_operator.v *)
  (* 'I_5 は finType のインスタンスである。(あ) *)
  Goal 'I_5 = ordinal_eqType 5. Proof. done. Qed.
  
  (* (pred_of_simpl (pred_of_argType 'I_5)) は、pred 'I_5 型である。(い) *)
  Check pred_of_simpl (pred_of_argType 'I_5) : pred 'I_5.
  
  (* (あ)(い) より、(pred_of_simpl (pred_of_argType 'I_5)) は、
     T : finType, P : pred T なる P である。 *)
  Check pred_of_argType : forall T : predArgType, simpl_pred T.
  Check pred_of_simpl   : forall T : Type, simpl_pred T -> pred T.
  Check (fun T => pred_of_simpl (pred_of_argType T)) : forall T : predArgType, pred T.
  
  (* (pred_of_simpl (pred_of_argType 'I_5)) は、
     mem の引数に書くことができ、また、mem も省略できる。 *)
  Check p2S (mem (pred_of_simpl (pred_of_argType 'I_5))) : mySet 'I_5. (* (1) *)
  Check p2S (mem                                 'I_5)   : mySet 'I_5. (* (2) *)
  Check p2S      (pred_of_simpl (pred_of_argType 'I_5))  : mySet 'I_5.  
  Check p2S                                      'I_5    : mySet 'I_5.
  Check \{ x in 'I_5 \}                                  : mySet 'I_5.  
  
(**
## ここからが本題
*)
  Goal p0 ∈ \{ x in 'I_5 \}.
  Proof.
      (*
        rewrite /belong /p2S.
        by case H : (p  1 \in 'I_5).
       *)
      by [].
  Qed.
End 具体的なfinType.

(* END *)
