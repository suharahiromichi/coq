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

Section 具体的なfinType.                    (* suhara *)
  (* 具体的な finType として、'I_5 を与える。 *)
  
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
  
  (* *************** *)
  (* ここからが本題。 *)
  (* *************** *)
  
  (* p0 は素の集合の要素である。 *)
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
