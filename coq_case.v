(* Caseやelimを使わずに、apply と intro だけで証明する *)
(* お茶大 浅井研、Coqゼミ 第4回、第5回 を参考にした。 *)


Print and_ind.
Print conj.


Lemma and_commutative : forall A B : Prop, A /\ B -> B /\ A.
  intros.
  case H.
  split.
  exact H1.
  exact H0.
  Restart.


(*********)
  intros.
  (* H : A /\ B *)
  (* Goal : B /\ A *)
  apply and_ind with (P := B /\ A) in H.
  apply H.
  (* Goal : A -> B -> B /\ A *)


  intros.
  apply conj.
  apply H1.
  apply H0.
Qed.




Print or_ind.
Print or_introl.
Print or_intror. 


Lemma or_commutative : forall A B : Prop, A \/ B -> B \/ A.
  intros.
  case H.
  intros.
  right.
  exact H0.
  left.
  exact H0.
  Restart.


(*********)
  intros.
  (* H : A \/ B *)
  (* Goal : B \/ A *)
  apply or_ind with (P := B \/ A) in H.
  apply H.
  (* Goal : A -> B \/ A *)
  (* Goal : B -> B \/ A *)
  
  intros.
  apply or_intror.
  apply H0.
  apply or_introl.
Qed.




Print False_ind.


Lemma nonsense : forall A Q : Prop, not (1 = 1) -> (2 = 3).
  intros.
  case H.
  reflexivity.
  Restart.


(*********)
  intros.
  (* H : 1 <> 1 *)
  (* Goal : 2 = 3 *)
  apply False_ind with (P := (2 = 3)) in H.
  apply H.
  (* Goal : 1 = 1 *)
  reflexivity.
Qed.




Print ex_ind.
Print ex_intro.


Lemma ex_1 : (exists x : nat, x = 1) -> True.
  intros.
  case H.
  intros.
  auto.
  Restart.


(*********)
  intros.
  (* H : exists x : nat, x = 1 *)
  (* Goal : True *)
  apply ex_ind with (P0 := True) in H.      (* eapply ex_ind in H を試すとよい。 *)
  apply H.
  (* Goal : forall x : nat, x = 1 -> True *)
  intros.
  (* Goal : True *)
  apply I.
Qed.


Lemma ex_2 : (exists x : nat, x = 1).
  exists 1.
  reflexivity.
  Restart.


(*********)
  intros.
  (* Goal : exists x : nat, x = 1 *)
  apply ex_intro with (x := 1).
  (* Goal : 1 = 1 *)
  reflexivity.
Qed.


(**** おまけ ******)


Variables A : Set.
Variables P Q : A -> Prop.
Lemma ex_3 : (exists x : A, P x \/ Q x) -> ex P \/ ex Q.
  intros.
  case H.
  intros.
  case H0.


  intros.
  left.
  exists x.
  exact H1.


  intros.
  right.
  exists x.
  exact H1.
  Restart.


(*********)
  intros.
  apply ex_ind with (P0 := ex P \/ ex Q) in H.
  apply H.
  intros.
  apply or_ind with (P := (ex P \/ ex Q)) in H0.
  apply H0.
  intro.
  apply or_introl.
  apply ex_intro with (x := x).
  apply H1.
  intro.
  apply or_intror.
  apply ex_intro with (x := x).
  apply H1.
Qed.


(*********)
(* nat型 *)
(*********)
Print nat.
Print nat_ind.
Print nat_rec.


Lemma pred_s_n : forall n : nat, pred (S n) = n.
  intros.
  induction n.
  simpl.
  reflexivity.
  simpl.
  reflexivity.
  Restart.


(*********)
  intros.
  case n.
  simpl.
  reflexivity.
  simpl.
  reflexivity.
  Restart.


(*********)
  intros.
  (* Goal : pred (S n) = n *)
  apply nat_ind with (n := n).
  (* Goal : pred 1 = 0 *)
  (* Goal : forall n0 : nat, pred (S n0) = n0 -> pred (S (S n0)) = S n0 *)
  simpl.
  reflexivity.
  simpl.
  reflexivity.
Qed.


(*********)
(* season 型 *)
(*********)
Inductive season : Set :=
  | Spring : season
  | Summer : season
  | Fall : season
  | Winter : season.


Print season_ind.
Print season_rec.


Definition next (s : season) :=
  match s with
  | Spring => Summer
  | Summer => Fall
  | Fall => Winter
  | Winter => Spring
  end.


Definition last (s : season) :=
  match s with
  | Spring => Winter
  | Summer => Spring 
  | Fall => Summer
  | Winter => Fall
  end.


Eval compute in last (next Spring).


Lemma last_next : forall s : season , last (next s) = s.
  intros.
  induction s; simpl; reflexivity.
  Restart.


(*********)
  intros.
  case s; simpl; reflexivity.
  Restart.


(*********)
  intros.
  apply season_ind with (s := s); simpl; reflexivity.
  Restart.


(*********)
  intros.
  apply season_ind with (s := s).
  simpl; reflexivity.
  simpl; reflexivity.
  simpl; reflexivity.
  simpl; reflexivity.
Qed.


(* おまけ *)


Print eq.
Check eq.
Check refl_equal.


Lemma test_equal : 1 = 1.
  reflexivity.
  Restart.


(********)
  apply refl_equal.
Qed.


(* END *)