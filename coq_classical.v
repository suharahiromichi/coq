(*
   Anarchy Proof
   
   Peirce
   http://as305.dyndns.org/aps/problem/view/3


   Converse Peirce
   http://as305.dyndns.org/aps/problem/view/4


   call/cc
   http://as305.dyndns.org/aps/problem/view/5
*)


Require Import Classical.                   (* 古典論理パッケージ *)


(****************)
(* Prove 'Peirce's law'. *)
(* 「パースの論理式」を証明する。*)
(* 古典論理では証明できるが、直観論理では証明できない。*)
(* 「パースの論理式」を排中律で証明する。*)
(****************)


Theorem Peirce : forall (P Q: Prop), ((P -> Q) -> P) -> P.
Proof.
  intros p q H.
  Check classic.                            (* 排中律の公理 *)
  (* Logic/Classical_Prop.v で定義されている。*)
  elim (classic p).
  intros P.
  assumption.


  intros H0.
  apply H0 in H.
  elim H.
  intros H1.
  (* H0 : ~P と H1 : P から Falseを求める *)
  apply H0 in H1.
  case H1.                                  (* 前提がFalseで証明は終了。 *)
Qed.


(* 「パースの論理式」を二重否定除去で証明する。*)


Theorem Peirce' : forall (P Q: Prop), ((P -> Q) -> P) -> P.
Proof.
  intros p q H.
  Check NNPP.                               (* 二重否定の除去 *)
  apply NNPP.
  intros nHp.
  apply nHp in H.
  apply H.
  intros Hp.
  case (nHp Hp).
Qed.


(* Verifier *)
Definition check_Peirce: forall (P Q: Prop), ((P -> Q) -> P) -> P := Peirce.
  
(* Classical パッケージを使用しない。*)


(****************)
(* パースの論理式を使って、排中律を証明する。*)
(****************)


(* 古典論理で(Classicalパッケージを使う)、パースの論理式の証明は、
   coq_classical.v を参照せよ。*)
(* Axiom Peirce : forall (P Q: Prop), ((P -> Q) -> P) -> P. *)


Theorem Excluded_Middle : forall (P: Prop), P \/ ~P.
Proof.
  intros p.
  Check (Peirce p False).
  apply (Peirce _ False).                   (* apply Peirce with False. *)
  intros H.
  right.
  intros Hp.                                (* ~ p に対して、さらにintrosする！ *)
  apply H.
  left.
  apply Hp.
Qed.


(* Verifier *)
Definition check_Excluded_Middle : forall (P: Prop), P \/ ~P := Excluded_Middle.


(****************)
(* Prove 'call/cc implies excluded middle'. *)
(* call/cc を使って、排中律 (law of the excluded middle) を証明する。*)
(****************)


Axiom callcc: forall (P: Prop), ((P -> False) -> P) -> P.


Theorem Excluded_Middle' : forall (P: Prop), P \/ ~P.
Proof.
  intros p.
  apply callcc.                             (* パースの論理式の特別な形。 *)
  (* パースの論理式による証明と同じだが、
     auto で済ますこともできる。*)
  auto.
Qed.


(* Verifier *)
Definition check_Excluded_Middle' : forall (P: Prop), P \/ ~P := Excluded_Middle'.


(* END *)