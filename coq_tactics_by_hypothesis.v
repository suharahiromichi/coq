(* Coq Tactics、前提が。。。のとき、一覧 *)
(* by hypothesis *)


Parameters P Q R : Prop.


(* coqide では、線より上が前提、下がゴールである *)
(* hypothese : 仮説、前提 *)


Theorem hypothese_goal : P -> P.
  intros.
  (* Goal P *)
  assumption.                           (* 前提Hが、ゴール P に等しい。 *)
Qed.


(*********************)
(* 前提に、→がある。含意 *)
(*********************)
Theorem hypothese_imp : P -> (P -> Q) -> Q.
  intros H1 H2.
  (* Goal Q *)
  apply H2.                             (* 前提H2が、含意 P->Q である。*)
  (* Goal P *)
  assumption.                           (* 前提H1が、ゴール P に等しい。 *)
Qed.


Theorem hypothese_imp' : P -> (P -> Q) -> Q.
  intros H1 H2.
  (* Goal Q *)
  apply H2 in H1.                       (* 前提H2が、含意 P->Q である。*)
  (* Goal Q *)
  assumption.                           (* 前提H1が、ゴール Q に等しい。 *)
Qed.


(*********************)
(* 前提に、∀がある。全称記号 *)
(*********************)
Theorem hypothese_forall : forall P : nat -> Prop,
  (forall n : nat, P n) -> P 0.
  intros p H.
  (* Goal 0 *)
  apply (H 0).                          (* 前提Hが、∀...。 *)
  (* apply H. だけでもよい。n=0 と推論されるから *)
Qed.


(***********************)
(* 前提に、Trueがある。*)
(* 証明の役には立たない。*)
(***********************)


(************************)
(* 前提に、Falseがある。*)
(************************)
Theorem hypothese_false : False -> 0 = 1.
  intros H.
  (* Goal 0 = 1 *)
  case H.                               (* 前提に、Falseがある場合。 *)
  (* 場合分けで、ただちに証明が完了する。 *)
Qed.


Theorem hypothese_mujun : P -> ~P -> 0 = 1.
  intros H1 H2.
  (* Goal 0 = 1 *)
  (* 前提に、Pと~Pがある。 *)
  exfalso.                                  (* elimtype False. *)
  (* ソフトウェアの基礎では、apply ex_falso_quodlibet *)
  (* Goal を False に置き換える。 *)
  apply H2.
  apply H1.
Qed.


Theorem hypothese_mujun' : P -> ~P -> 0 = 1.
  intros H1 H2.
  (* Goal 0 = 1 *)
  absurd P.                                 (* 前提に、Pと~Pがある。 *)
  apply H2.
  apply H1.
Qed.

Theorem hypothese_mujun'' : P -> ~P -> 0 = 1.
  contradiction.                            (* 完全に自動化する。 *)
Qed.

Theorem hypothese_mujun2 : (P -> Q) -> (P -> ~Q) -> ~P.
  intros H1 H2 H3.
  (* Goal False *)
  (* 前提に、P->QとP->~Qがある。 *)
  absurd Q.                                 (* いまのゴールを捨て、Qと~Qをゴールにする。*)
  apply H2.
  apply H3.
  apply H1.
  apply H3.
Qed.


(***********************)
(* 前提が、P/\Qである。*)
(***********************)
Theorem hypothese_and : P /\ Q -> P.
  intros H.
  (* Goal P *)
  (* 前提が、P/\Qである。 *)
  destruct H as [ H1 H2 ].               (* 前提をH1:PとH2:Qのふたつに分ける。 *)
  assumption.                            (* 前提H1が、ゴール P に等しい。 *)
Qed.


Theorem hypothese_and' : P /\ Q -> P.
  intros H.
  (* Goal P *)
  (* 前提が、P/\Qである。 *)
  case H.                                 (* 場合分けする。 *)
  (* Goal P->Q->P *)
  intros H1 H2.                           (* ゴールが、含意である *)
  (* Goal P *)
  assumption.                             (* 前提H1が、ゴール P に等しい。 *)
Qed.


(***********************)
(* 前提が、P\/Qである。*)
(***********************)
Theorem hypothese_or : P \/ Q -> (P -> R) -> (Q -> R) -> R.
  intros H1 H2 H3.
  (* Goal R *)
  (* 前提が、P\/Qである。*)
  destruct H1 as [ HA | HB ].             (* ゴールをHA:RとHB:Rのふたつに分ける。 *)
  (* Goal R。前提は、HA : P, H2 : P->R *) 
  apply (H2 HA).
  (* Goal R。前提は、HB : Q, H3 : Q->R *)
  apply (H3 HB).
Qed.


Theorem hypothese_or' : P \/ Q -> (P -> R) -> (Q -> R) -> R.
  intros H1 H2 H3.
  (* Goal R *)
  (* 前提が、P\/Qである。*)
  case H1.                              (* ゴールをP->RとQ->Rのふたつに分ける。 *)
  (* Goal P->R。前提は、H2 : P->R *)
  assumption.                           (* 前提がゴールに等しい。 *)
  (* Goal Q->R。前提は、H3 : Q->R *)
  assumption.                           (* 前提がゴールに等しい。 *)
Qed.


(*********************)
(* 前提に、∃がある。 存在記号 *)
(*********************)
Theorem hypothese_exists : forall P : nat -> Prop,
  (exists n : nat, ~ P n) -> ~ (forall n : nat, P n).
  intros p H1 H2.
  destruct H1 as [ n H3 ].
  apply H3.
  apply H2.
Qed.


Theorem hypothese_exists' : forall P : nat -> Prop,
  (exists n : nat, ~ P n) -> ~ (forall n : nat, P n).
  intros p H1 H2.
  case H1.
  intros n H3.
  apply H3.
  apply H2.
Qed.


(*********************)
(* 前提に、=がある。 等号 *)
(*********************)
Theorem hypothese_eq : forall m n : nat,
  m = n -> S m = S n.
  intros m n H.
  (* Goal S m = S n。前提は、H : m=n *)
  rewrite H.                            (* 前提の左辺で、ゴールの左辺を置換る *)
  (* Goal n = n *)
  reflexivity.                          (* 左辺と右辺が同じ場合 *)
Qed.


Theorem hypothese_eq' : forall m n : nat,
  m = n -> S m = S n.
  intros m n H.
  (* Goal S m = S n。前提は、H : m=n *)
  case H.                               (* ????? *)
  (* Goal S n = S n *)
  reflexivity.                          (* 左辺と右辺が同じ場合 *)
Qed.


Theorem hypothese_eq2 : forall m n : nat,
  S m = S n -> m = n.
  intros m n H.
  (* Goal m = n。前提は、H : Sm=Sn *)
  injection H.                          (* 単射性を使う *)
  (* Goal m=n -> m=n *)
  trivial.                              (* auto 1、introとapply *)
Qed.

(* 等式の両辺が明らかに異なるコンストラクタである場合は、discriminate
   を使うことで False を導き直ちに任意のゴールを証明することができる。 *)
Theorem hypothese_eq3 : 0 = 1 -> 2 = 4.
  intros H.
  discriminate H.
(* 単にdiscriminateでもよい。 *)
Qed.

(*********************)
(* 前提に、~がある。 否定 *)
(*********************)
Theorem hypothese_not : P -> ~P -> 0 = 1.
  intros H1 H2.
  (* Goal 0=1 , 前提は、H1:P, H2:~P *)
  apply H2 in H1.                       (* 前提どうし適用して、前提をFalseにする。*)
  (* 前提は、H1 : False *)
  case H1.                              (* 前提がFalseの場合を参照 *)
Qed.


(*********************)
(* 前提に、<>がある。 不等号 *)
(*********************)
Theorem hypothese_neq : forall n, n<>0 -> n=0 -> 1=2.
  intros n H1 H2.
  apply H1 in H2.         (* 前提どうし適用して、前提をFalseにする。*)
  case H2.                (* 前提がFalseの場合を参照 *)
Qed.

(* 不等式の両辺が明らかに等しくない場合。 *)
Theorem hypothese_neq' : forall n, n<>0 -> n=0 -> 1=2.
  congruence.
Qed.

Theorem hypothese_neq2 :
  forall m, m <> 0 -> exists n, m = S n.
  intros m H.
  destruct m as [ | m' ].
  congruence.
  exists m'.
  reflexivity.
Qed.

(* <>と=から矛盾を導くのではなく、
  reflexivityの逆に、(not false) <> false を証明するには、
  discriminate を使う。*)
Theorem hypothese_neq3 : 2 <> 3.
  intros H.
  discriminate H.
(* 単にdiscriminateでもよい。 *)
Qed.

(* END *)
