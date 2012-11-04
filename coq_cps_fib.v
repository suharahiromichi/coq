(**
   CPS
   フィボナッチ数
   2012_11_02

   参考：
   「CPS変換されたフィボナッチ関数の証明をしてみた」
   http://d.hatena.ne.jp/yoshihiro503/20100830#p2
   *)

(** 普通のフィボナッチ関数の定義 *)
Fixpoint fib (n: nat) {struct n} : nat :=
  match n with
      | 0 => 1
      | 1 => 1
      | S (S m as sm) => fib sm + fib m
  end.
Eval cbv in fib 5.                          (* 8 *)
Eval cbv in fib 6.                          (* 13 *)

(** CPS変換されたフィボナッチ関数の定義 *)
Fixpoint fib_cps (n : nat) (cont : nat -> nat) {struct n} : nat :=
  match n with
    | 0 =>  cont 1
    | 1 =>  cont 1
    | S ((S m) as sm) =>
      fib_cps sm (fun r1 => fib_cps m (fun r2 => cont (r1 + r2)))
  end.
Eval cbv in fib_cps 5 (fun r => r).
Eval cbv in fib_cps 6 (fun r => r).

(** 補題: fib_cpsの定義の三番目の節を取り出したもので、
   fib_cpsの計算を一段進めるのに使う。 *)
Lemma fib_cps_SSn : forall n f,
  fib_cps (S (S n)) f =
  fib_cps (S n) (fun r1 => fib_cps n (fun r2 => f (r1 + r2))).
Proof.
  reflexivity.
Qed.

(** より強い定理 *)
Theorem eq_fib_fib_cps_aux : forall n,
  (forall f, f (fib n) = fib_cps n f) /\
  (forall g, g (fib (S n)) = fib_cps (S n) g).
Proof.
  induction n.

  (* 0 のとき *)
  split.                                   (* Goalのandを分解する。 *)
  (** andの左 *)
  intro f.
  simpl.                                 (* f (fib 0) = fib_cps 0 f *)
  reflexivity.
  (** andの右 *)
  intro g.
  simpl.                                 (* g (fib 1) = fib_cps 1 g *)
  reflexivity.

  (* Sn のとき *)
  destruct IHn as [Hf Hg].                 (* 前提のandを分解する。 *)
  split.                                   (* Goalのandを分解する。 *)
  (** andの左 *)
  intro f.
  apply Hg.
  (** andの右 *)
  intro g.
  rewrite fib_cps_SSn.
  rewrite <- Hg.
  rewrite <- Hf.
  simpl.               (* g (fib (S (S n))) = g (fib (S n) + fib n) *)
  reflexivity.
Qed.
Print eq_fib_fib_cps_aux.

(** 証明するべきもの *)
Theorem eq_fib_fib_cps : forall n f, f (fib n) = fib_cps n f.
Proof.
  intros n f.
  destruct (eq_fib_fib_cps_aux n).
  apply H.
Qed.
Print eq_fib_fib_cps.

(* END *)
