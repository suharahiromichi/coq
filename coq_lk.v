(**
   coq は 自然演繹に基づいた体系であることがわかる。
   
   - 自然演繹


                [A \/ B]  [A \/ B]
   ---------------------------
                B         A
   ---------------------------
   [A \/ B]     B \/ A
   ---------------------------
   A \/ B    -> B \/ A


   ---
   - シークエント計算
   古典論理 LK、直観論理 LJ
   
   A --> B,A        B --> B,A
   ---------------------------
   A \/ B --> B,A
   ---------------------------
   A \/ B --> B /\ A
   ---------------------------
   --> A \/ B -> B \/ A
*)


Goal forall A B, A \/ B -> B \/ A.
Proof.
  intros.
  destruct H.
  right.
  apply H.
  left.
  apply H.
Qed.


Goal forall A B, A \/ B -> B \/ A.
Proof.
  intros.
  case H.
  intro HA.
  constructor 2.
  apply HA.


  intro HB.
  constructor 1.
  apply HB.
Qed.


(* END *)