
(*
   フィボナッチ数
   *)


(** 普通のフィボナッチ関数の定義 *)
Fixpoint fib (n: nat) : nat :=
  match n with
    | 0 => 1
    | 1 => 1
    | S (S m as sm) => fib sm + fib m
  end.


(** CPS変換されたフィボナッチ関数の定義 *)
Variable A : Type.
Fixpoint fib_cps (n : nat) (cont : nat -> A) : A :=
  match n with
    | 0 =>  cont 1
    | 1 =>  cont 1
    | S (S m as sm) =>
      fib_cps sm (fun r1 =>
        fib_cps m (fun r2 => cont (r1 + r2)))
  end.



(** 補助的な性質をいくつか。ほとんど自明だが。 *)
Lemma fib0: fib 0 = 1.
  reflexivity.
Qed.


Lemma fib1: fib 1 = 1.
  reflexivity.
Qed.


Lemma fib_SSn : forall n, fib (S (S n)) = fib (S n) + fib n.
  reflexivity.
Qed.


Lemma fib_cps0 : forall f, fib_cps 0 f = f 1.
  reflexivity.
Qed.


Lemma fib_cps1 : forall f, fib_cps 1 f = f 1.
  reflexivity.
Qed.


Lemma fib_cps_SSn : forall n f,
  fib_cps (S (S n)) f = fib_cps (S n) (fun r1 => fib_cps n (fun r2 => f (r1+r2))).
  reflexivity.
Qed.


(** 等価性の証明 *)


(* まず、あえて より強い性質を証明する *)
Theorem eq_fib_fib_cps_aux : forall n,
  (forall f, f (fib n) = fib_cps n f) /\ (forall g, g (fib (S n)) = fib_cps (S n) g).
Proof.
  induction n.
  (* 0 のとき *)
  split.
  intro.
  reflexivity.
  reflexivity.

  intro.
  rewrite fib1.
  rewrite fib_cps1.
  reflexivity.
  
  (* nでOKと仮定して(S n)を示す *)
  destruct IHn.                             (* 仮定に /\ があるときはdestruct *)
  split.
  intro f.
  apply H0.
  
  intro g.
  rewrite fib_cps_SSn.
  rewrite <- H0.
  rewrite <- H.
  rewrite fib_SSn.
  reflexivity.
Qed.


(* そしてこれがメインの定理 *)



(* END *)

Lemma fib_cps_SSn' : forall n f,
  fib_cps (S (S n)) f = fib_cps (S n) (fun r1 => fib_cps n (fun r2 => f (r1+r2))).
  reflexivity.
Qed.

Theorem eq_fib_fib_cps_aux' : forall n, forall f,
  f (fib n) = fib_cps n f.
Proof.
  (* 0 のとき *)
  intro.
  (* nでOKと仮定して(S n)を示す *)
  intro f.

  rewrite <- H0.
  rewrite <- H.
  rewrite fib_SSn.
  reflexivity.
Qed.

Theorem eq_fib_fib_cps' : forall n f, f (fib n) = fib_cps n f.
Proof.
  intros.
  induction n.
  simpl.
  reflexivity.
  
  rewrite <- fib_SSn.


  
  destruct (eq_fib_fib_cps_aux n);
      apply H.
Qed.








