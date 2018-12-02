From mathcomp Require Import all_ssreflect.
From mathcomp Require Import finset.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Section SetTheory.
  
  Variable T : finType.
  
  Lemma a_a_b__b (A B : {set T}) : B \subset A -> (A :\: (A :\: B)) = B.
  Proof.
    move=> H.
    rewrite setDDr.   (* A :\: (B :\: C) = (A :\: B) :|: (A :&: C). *)
    (* A :\: A :|: A :&: B = B *)
    rewrite setDv.           (* A :\: A = set0. *)
    (* set0 :|: A :&: B = B *)
    rewrite set0U.           (* set0 :|: A = A. *)
    (* A :&: B = B *)
    apply/setIidPr.          (* reflect (A :&: B = B) (B \subset A) *)
    (* B \subset A *)
    done.
  Qed.

  Lemma l_set_dif_1 (A B : {set T}) : (A :\: B) \subset A.
  Proof.
    Search _ (reflect _ _) in finset.
    apply/setIidPl.
    Search _ ((_ :\: _) :&: _).
    rewrite setIDAC.
    Search _ ((_ :&: _) :\: _).
    rewrite setIid.
    done.
  Qed.
    
  Lemma l_set_dif_2 (A B : {set T}) : (A :\: B) :&: B = set0.
  Proof.
    rewrite setIDAC.
    Search _ ((_ :&: _) :\: _).
    rewrite setDIl.
    Search _ (_ :\: _ = set0).
    rewrite setDv.
    Search _ (set0 :&: _ = set0).
    rewrite setIC.
    rewrite set0I.
    done.
  Qed.
  
  Lemma exA_8 (A B : {set T}) : (A :\: B) :|: (A :&: B) = A.
  Proof.
    Search _ ((_ :\: _) :|: (_ :&: _)).
    rewrite -setDDr.
    Search _ (_ :\: _ = set0).
    rewrite setDv.
    Search _ (_ :\: set0 = _).
    rewrite setD0.
    done.
  Qed.
  
  Lemma exA_9 (A B C D : {set T}) : A \subset C -> D \subset B ->
                                    A :\: B \subset C :\: D.
  Proof.
    move=> HAC HDB.
    rewrite -setD_eq0 in HAC.
    rewrite -setD_eq0 in HDB.
  Admitted.
  
  Lemma exA_10 (A B : {set T}) : A \subset B <-> A :\: B = set0.
  Proof.
    rewrite -setD_eq0.
      by split=> H; move/eqP in H.
  (*              
      split=> H.
        move/setIidPl=> H.
        rewrite -H.
        Search _ (_ :&: _ :\: _).
        rewrite -setIDA.
        Search _ (_ :\: _ = set0).
        rewrite setDv.
        Search _ (_ :&: set0 = set0).
        rewrite setI0.
        done.
*)        
  Qed.
  
  Lemma exA_11 (A B :{set T}) : A :\: (A :\: B) = A :&: B.
  Proof.
    Search _ (_ :\: (_ :\: _)).
    rewrite setDDr.
    rewrite setDv.
    rewrite set0U.
    done.
  Qed.
  
  Lemma exA_12 (A B C : {set T}) : A \subset C -> B \subset C ->
                                   (A :\: B = set0 <-> A \subset C :\: B).
  Proof.
  Admitted.
  

  Lemma test (C B : {set T}) : C :|: (B :\: C) = C :|: B.
  Proof.
  Admitted.
  
  Lemma exA_13 (A B C : {set T}) : A :\: C \subset (A :\: B) :|: (B :\: C).
  Proof.
    Search _ (_ \subset _).
    rewrite -setD_eq0.
    
    Search _ (_ :\: (_ :|: _)).
    Check setDUr (A :\: C) (A :\: B) (B :\: C).
    rewrite setDUr.

    rewrite setI_eq0.
    Search _ ([disjoint _  & _ ]).
    apply/setDidPl.
    
    
    

    (* この形にもちこむ *)
    Check l_set_dif_2 : forall A B : {set T}, (A :\: B) :&: B = set0.
  Admitted.
  
  Lemma exA_14_1 (A B C : {set T}) : A :\: (B :|: C) = (A :\: B) :&: (A :\: C).
  Proof.
    Search _ (_ :\: (_ :|: _)).
    now rewrite setDUr.
  Qed.
  
  Lemma exA_15_1 (A B C : {set T}) : (A :|: B) :\: C = (A :\: C) :|: (B :\: C).
  Proof.
    Search _ ((_ :|: _) :\: _).
    now rewrite setDUl.
  Qed.

  Search _ ((_ :|: _) :\: _).
  
  Lemma exA_15_4 (A B C : {set T}) : (A :|: C) :\: B \subset (A :\: B) :|: C.
  Proof.
    rewrite setDUl.
    Search _ (_ \subset _).
    apply setUS.
    now apply l_set_dif_1.
  Qed.
  
End SetTheory.

(* END *)
