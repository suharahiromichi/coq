(* Coq
   覚えておくと便利なコンストラクター
   2010_09_19
*)
(*
  (1) コンストラクタを直接使う例。apply(またはcase)を使用。
  (1') コンストラクタを直接使う例。constructorを使用。constructor 1の1は省くことができる。
  (2) 推論規則に対応した戦略(またはdestruct)を使う例。
*)


Parameters P Q R : Prop.


(************************)
(* And                  *)
(************************)
Print and.


Theorem goal_and : P -> Q -> P /\ Q.
  intros H1 H2.
  (* Goal : P/\Q *)
  apply conj.                               (* constructor. *) (* split. *) 
  apply H1.
  apply H2.
Qed.


Theorem hypothese_and : P /\ Q -> P.
  intros.
  (* H : P/\Q *)
  case H.
  intros H1 H2.
  apply H1.
Qed.


Theorem hypothese_and2 : P /\ Q -> P.
  intros.
  (* H : P/\Q *)
  destruct H as [ H1 H2 ].
  apply H1.
Qed.


(************************)
(* Or                   *)
(************************)
Print or.


Theorem goal_or : Q -> P \/ Q \/ R.
  intros H.
  (* Goal : P\/Q\/R *)
  apply or_intror.                          (* constructor 2. *) (* right. *)
  (* Goal : Q\/R *)
  apply or_introl.                          (* constructor 1. *) (* left *)
  (* Goal : Q *)
  apply H.
Qed.


Theorem hypothese_or : P \/ Q -> (P -> R) -> (Q -> R) -> R.
  intros H1 H2 H3.
  (* H1 : P\/Q *)
  case H1.
  (* Subgoal 1 : P-> R,  Subgoal 2 : Q->R *)
  intros HA.
  apply (H2 HA).                            (* apply H2. apply HA. *)


  intros HB.
  apply (H3 HB).
Qed.


Theorem hypothese_or2 : P \/ Q -> (P -> R) -> (Q -> R) -> R.
  intros H1 H2 H3.
  (* H1 : P\/Q *)
  destruct H1 as [ HA | HB ].
  apply (H2 HA).
  apply (H3 HB).
Qed.


(************************)
(* Ex                   *)
(************************)


Print ex.


Theorem goal_exists : exists n : nat, n = 0.
  apply ex_intro with 0.                    (* constructor 1 with 0. *) (* exists 0. *)
  reflexivity.                              (* goal_eq を参照のこと。 *)
Qed.


Theorem hypothese_exists : forall P : nat -> Prop,
  (exists n : nat, ~ P n) -> ~ (forall n : nat, P n).
  intros p H1 H2.
  
  case H1.
  intros n H3.
  
  apply H3.
  apply H2.
Qed.


Theorem hypothese_exists2 : forall P : nat -> Prop,
  (exists n : nat, ~ P n) -> ~ (forall n : nat, P n).
  intros p H1 H2.
  
  destruct H1 as [ n H3 ].
  
  apply H3.
  apply H2.
Qed.


(************************)
(* Eq                   *)
(* 等式論理は、新たに項目を立てる *)
(************************)
Print eq.


Theorem goal_eq : forall m n, m = n -> S m = S n.
  intros m n H.
  (* Goal : Sm = Sn、H :  m=n *)
  case H.                                   (* hypothese_eq参照  *)
  
  (* Goal : Sm = Sm *)
  apply refl_equal.                         (* constructor *) (* reflexivity. *) 
Qed.


(************************)
(* True                 *)
(************************)
Print True.


Theorem goal_true : True.
  (* Goal True *)
  apply I.                                  (* trivial. *) (* constructor. *)
  (* 引数を取らないコンストラクタIを適用する。 *)
Qed.
(* 前提にTureがあっても、役に立たない *)


(************************)
(* False                *)
(************************)
Print False.


(* ゴールのFalseは、証明できない。*)
Theorem hypothese_false : False -> True.
  intro.
  case H.
  (* 場合分けをすると、直ちに証明が終了する *)
Qed.


(* END *)