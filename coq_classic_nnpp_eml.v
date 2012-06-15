(* 二重否定除去と排中律の同値性 *)
(* Double negative elimination, Excluded Middle Low *)


Lemma NNPP_EML :
  (forall A, ~~A -> A) <-> (forall A B, (~B -> ~A) -> (A -> B)).
Proof.
  unfold not.
  split.


  intros NNPP A B H0.
  intros HA.
  apply NNPP.
  intros HnB.
  apply H0.
  apply HnB.
  apply HA.
  
  intros HEM A.
  Check (HEM ((A -> False) -> False) A).
  apply (HEM ((A -> False) -> False) A).
  intros HnA HnnA.
  apply HnnA.
  apply HnA.
Qed.


(* 模範回答 *)


Lemma p10 :
  (forall A, ~~A -> A) <-> (forall A B, (~B -> ~A) -> (A -> B)).
Proof.
  split.
  
  intros.
  apply H.
  intro.
  elim (H0 H2).                             (* apply (H0 H2). *)
  apply H1.
  
  intros.
  apply (H True A).
  intro.
  intro.
  elim H0.                                  (* apply H0. *)
  apply H1.
  apply I.
Qed.


(* END *)