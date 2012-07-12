(* Coq Tactics、ゴールが。。。のとき、一覧 *)
(* by goal *)


Parameters P Q R : Prop.


(* coqide では、線より上が前提、下がゴールである *)
(* hypothese : 仮説、前提 *)


(***********************)
(* ゴールが、→である。含意 *)
(***********************)
(* intro を使う。 *)


(***********************)
(* ゴールが、∀である。全称記号 *)
(***********************)
(* intro を使う。*)


(*************************)
(* ゴールが、TRUEである。*)
(*************************)
Theorem goal_true : True.
  (* Goal True *)
  apply I.                              (* 引数を取らないコンストラクタIを適用する。 *)
Qed.


(**************************)
(* ゴールが、FALSEである。*)
(**************************)
Theorem goal_false : False -> False.
  intros.
  (* Goal False、前提 False。つまり前提に矛盾がなければFalseは導けない。 *)
  assumption.
Qed.


(*************************)
(* ゴールが、P/\Qである。連言 *)
(*************************)
Theorem goal_and : P -> Q -> P /\ Q.
  intros H1 H2.
  (* Goal P/\Q *)
  split.                                (* ゴールをふたつに分ける。*)
  (* apply conj. と同じ意味である。 *)
  (* 最初のGoal P *)
  apply H1.
  (* 次のGoal Q *)
  apply H2.
Qed.


(*************************)
(* ゴールが、P\/Qである。選言 *)
(*************************)
Theorem goal_or : Q -> P \/ Q \/ R.
  intros H.


  (* Goal P\/Q\/R *)
  right.                                (* ゴールorの右をとる。 *)
  (* apply or_intror. と同じ意味である。*)


  (* Goal Q\/R *)
  left.                                 (* ゴールorの左をとる。 *)
  (* apply or_introl. と同じ意味である。*)


  (* Goal Q *)
  apply H.
Qed.




(*************************)
(* ゴールが、∃である。限定記号 *)
(*************************)
Theorem ex_0 : exists n : nat, n = 0.
  exists 0.                              (* 実例である「0」を与える。 *)
  (* apply ex_intro with 0.        apply ではかならず、with X が必要である。*)
  reflexivity.
Qed.


(*************************)
(* ゴールが、=である。等号 *)
(*************************)
Theorem goal_eq : 1 = 1.
  reflexivity.
  (* apply refl_equal. と同じ意味である *)
Qed.

(* ゴール f a = f b を a = b に変形する。 *)
Theorem goal_eq2 : forall m n, m = n -> S m = S n.
  intros m n H.
  (* Goal Sm = Sn、前提 m=n *)
  f_equal.                              (* ゴールの、fa=fbをa=bに変換する。 *)
  (* Goal m=n *)
  apply H.
Qed.

(* 前提が。。。、で使った方法 *)
Theorem goal_eq2' : forall m n, m = n -> S m = S n.
  intros m n H.
  case H.
  reflexivity.
Qed.

(* ゴールが同値変形の繰り返しで導ける場合。*)
Theorem goal_eq3 :
  forall a b c d e, a = b + c -> a = e -> b + c = d -> d = e.
  congruence.
Qed.

(* END *)
