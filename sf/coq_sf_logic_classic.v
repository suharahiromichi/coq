(** * Logic_J: Coqにおける論理 *)
(* @suharahiromochi 2012_11_26 *)

(** **** 練習問題: ★★★★★, optional (classical_axioms) *)

(** さらなる挑戦を求める人のために、 Coq'Art book (p. 123) から一つ練習問題を
   取り上げてみます。次の五つの文は、よく「古典論理の特性」と考えられているもの
   （Coqにビルトインされている構成的論理の対極にあるもの）です。
   これらをCoqで証明することはできませんが、古典論理を使うことが必要なら、矛盾なく
   「証明されていない公理」として道具に加えることができます。
   これら五つの命題が等価であることを証明しなさい。 *)

Definition peirce := forall P Q: Prop,
  ((P -> Q) -> P) -> P.
Definition classic := forall P:Prop,
  ~ ~ P -> P.
Definition excluded_middle := forall P:Prop,
  P \/ ~ P.
Definition de_morgan_not_and_not := forall P Q:Prop,
  ~ (~ P /\ ~ Q) -> P \/ Q.
Definition implies_to_or := forall P Q:Prop,
  (P -> Q) -> (~ P \/ Q).

(* 上記の命題が、同値であることの証明をする。 *)

Theorem classic__peirce : classic -> peirce.
Proof.
  intros H P Q HPQP.
  (* P *)
  apply (H P).
  intros HP_F.
  apply HP_F.
  (* P *)
  apply HPQP.
  intros HP.
  (* Q *)
  apply (H Q).
  intros HQ_F.
  apply HP_F.
  apply HP.
Qed.

Theorem excluded_middle__peirce :
  excluded_middle -> peirce.
Proof.
  unfold peirce.
  unfold excluded_middle.
  unfold not.

  intros H P.
  intros Q HPQ_P.
  destruct (H P) as [HP | HnP].
  (* H = P *)
  apply HP.
  (* H = ~P *)
  apply HPQ_P.
  intros HP.
  exfalso.
  apply HnP.
  apply HP.
Qed.

Theorem de_morgan_not_and_not__peirce :
  de_morgan_not_and_not -> peirce.
Proof.
  unfold de_morgan_not_and_not.
  unfold peirce.
  unfold not.

  intros H P Q HPQP.
  destruct (H P Q).
  (* (P -> False) /\ (Q -> False) -> False *)
  intros HnPnQ.
  destruct HnPnQ as [HnP HnQ].
  apply HnP.
  apply HPQP.
  intros HP.
  exfalso.
  apply HnP.
  apply HP.
  (* P *)
  apply H0.
  (* P *)
  apply HPQP.
  intros HP.
  apply H0.
Qed.

Theorem peirce__classic : peirce -> classic.
Proof.
  unfold classic.
  unfold peirce.
  unfold not.

  intros H P.
  intros HnnP.
  apply (H P False).
  intros HnP.
  induction HnnP.                           (* ！ *)
  apply HnP.
Qed.
(* 前提が二重否定のとき、そをinductionすると、
   一重否定が得られる。 *)

(* http://joaoff.com/2012/01/29/on-peirces-law-and-the-law-of-the-excluded-middle/ *)
Theorem peirce__excluded_middle : peirce -> excluded_middle.
Proof.
  unfold excluded_middle.
  intros H P.
  apply H with (Q := ~ (P \/ ~ P)).
  unfold not.
  intros HPP.
  right.
  intros HP.
  apply HPP.
  left. apply HP.
  left. apply HP.
Qed.

Theorem excluded_middle__classic :
  excluded_middle -> classic.
Proof.
  unfold classic.
  unfold excluded_middle.
  unfold not.
  
  intros H P.
  intros HnnP.
  destruct (H P) as [HP | HnP].
  (* P *)
  apply HP.
  (* ~P *)
  induction HnnP.                           (* ！ *)
  apply HnP.
Qed.

Theorem classic__de_morgan_not_and_not :
  classic -> de_morgan_not_and_not.
Proof.
  unfold classic.
  unfold de_morgan_not_and_not.
  unfold not.
  (* coq'n artの回答から。 *)
  intros H P Q Hn_nPnQ.
  apply H.
  intro Hn_PQ.
  apply Hn_nPnQ.
  split.
  intro HP.
  apply Hn_PQ.
  left.
  apply HP.
  intros HQ.
  apply Hn_PQ.
  right.
  apply HQ.
Qed.

Theorem implies_to_or__classic :
  implies_to_or -> classic.
Proof.
  unfold classic.
  unfold implies_to_or.
  unfold not.
  
  intros H P HnnP.
  destruct (H P P) as [HnP1 | HnP2].
  intros HP.
  apply HP.
  induction HnnP.                           (* ！ *)
  apply HnP1.
  apply HnP2.
Qed.

(*
   情報論理学
   九州大学大学院システム情報科学研究院 情報学部門 長谷川先生
   平成24年4月
   http://opal.is.kyushu-u.ac.jp/~hasegawa/lecture/infologic/h24/il-txt-haifu-h24.pdf
   p.32, p.33
   
   自然演繹の証明図をcoqに写す練習でもある。
   *)
Theorem classic__excluded_middle :
  classic -> excluded_middle.
Proof.
  unfold classic.
  unfold excluded_middle.
  unfold not.

  intros H P.
  apply H.
  intros Hn_P_or_n_P.
  apply Hn_P_or_n_P.
  right.
  (* not P *)
  intros HP.
  apply Hn_P_or_n_P.
  left.
  apply HP.
Qed.

Theorem de_morgan_not_and_not__excluded_middle :
  de_morgan_not_and_not -> excluded_middle.
Proof.
  (* Coq'n Artの回答を参考にした。 *)
  intros H P.
  apply H.
  intro Hn_nPnnP.
  destruct Hn_nPnnP as [HnP HnnP].
  apply HnnP.
  intros HP.
  apply HnP.
  apply HP.
Qed.

Theorem implies_to_or__excluded_middle :
  implies_to_or -> excluded_middle.
Proof.
  intros H P.
  destruct (H P P) as [HnP | HP].
  (* P -> P *)
  intros HP.
  apply HP.
  (* P \/ ~P *)
  right.
  (* ~P *)
  apply HnP.
  left.
  (* P *)
  apply HP.
Qed.

Theorem de_morgan_not_and_not__classic: 
  de_morgan_not_and_not -> classic.
Proof.
  intros H P HnnQ.
  Check (H P P).
  destruct (H P P) as [HP1 | HP2].
  intros Hn_nPnP.
  apply HnnQ.
  intros HP.
  destruct Hn_nPnP as [HnP1 HnP2].
  apply HnP1.
  apply HP.
  apply HP1.
  apply HP2.
Qed.

Theorem excluded_middle__de_morgan_not_and_not :
  excluded_middle -> de_morgan_not_and_not.
Proof.
  unfold excluded_middle.
  unfold de_morgan_not_and_not.
  unfold not.
  
  intros H P Q Hn_nPnQ.
  destruct (H P) as [HP | HnP].
  (* H1 = P *)
  left.
  apply HP.
  (* H1 = ~P *)
  destruct (H Q) as [HQ | HnQ].
  right.
  apply HQ.
  induction Hn_nPnQ.                        (* ！ *)
  split.
  apply HnP.
  apply HnQ.
Qed.

Theorem excluded_middle__implies_to_or :
  excluded_middle -> implies_to_or.
Proof.
  unfold excluded_middle.
  unfold implies_to_or.
  unfold not.

  intros H P Q HPQ.
  destruct (H P) as [HP | HnP].
  (* ~P *)
  right.
  apply HPQ.
  apply HP.
  (* Q *)
  left.
  apply HnP.
Qed.

(* 上記以外の証明は、間接的に行える。 *)

Theorem implies_to_or__peirce' : implies_to_or -> peirce.
Proof.
  intros.
  apply classic__peirce.
  apply excluded_middle__classic.
  apply implies_to_or__excluded_middle.
  apply H.
Qed.

(* END  *)
