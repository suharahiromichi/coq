From mathcomp Require Import all_ssreflect.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Set Print All.

(* csm_5_set_theory.v は不使用である。 *)

Section ライブラリfinsetの利用.
  Variable M : finType.

  Check setP : forall (T : finType) (A B : {set T}), A =i B <-> A = B. (* 定理 *)
  
  (* 有限集合の ∪ (:|:) と ∩ (:&:) を ∈ (\in) と || と && にする。 *)
  Check in_setU : forall (T : finType) (x : T) (A B : {set T}),
      (x \in A :|: B) = (x \in A) || (x \in B).
  
  Check in_setI : forall (T : finType) (x : T) (A B : {set T}),
      (x \in A :&: B) = (x \in A) && (x \in B).
  
  (* 実際は、inEだけ覚えておけばよい。 *)
  Check inE.                                (* 略 *)
  
  Lemma demorgan (A B C : {set M}) : (A :&: B) :|: C = (A :|: C) :&: (B :|: C).
  Proof.
    (* = を =i に変換する。 *)
    (* ``P =i Q`` は ``∀x, x \in P = x \in Q`` の構文糖衣である。 *)
    apply/setP => x.
    (* Goal : A :&: B :|: C =i (A :|: C) :&: (B :|: C) *)
    (* Goal : (x \in A :&: B :|: C) = (x \in (A :|: C) :&: (B :|: C)) *)

    (* Goal : (x \in A :&: B :|: C) = (x \in (A :|: C) :&: (B :|: C)) *)
    (* :|: と :&: を || と && に変換する。 *)
(*
    rewrite !in_setU.
    rewrite !in_setI.    
    rewrite !in_setU.
    Undo 3.
*)    
    rewrite !inE.
    (* Goal : (x \in A) && (x \in B) || (x \in C) =
       ((x \in A) || (x \in C)) && ((x \in B) || (x \in C)) *)
    
    (* || と && の ド・モルガンの定理 *)
    Check orb_andl : forall x y z : bool, x && y || z = (x || z) && (y || z).
      by rewrite -orb_andl.
  Qed.
  
End ライブラリfinsetの利用.

(* END *)
