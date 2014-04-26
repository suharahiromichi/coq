(*
   CPS
   2010_10_29
   *)


(* 階乗の再帰版 *)
Fixpoint fact (n : nat) : nat :=
  match n with
    | 0 => 1
    | (S n') => n * fact n'
  end.
Eval cbv in fact 6.                         (* 720 *)


(* CPS 版で書くとこうなる。*)
Fixpoint fact_cps (n : nat) (cont : nat -> nat) : nat :=
  match n with
    | 0 => cont 1
    | (S n') => fact_cps n' (fun (a : nat) => cont (n * a))
  end.
Eval cbv in fact_cps 6 (fun a => a).        (* 720 *)


Lemma fact_Sn :
  forall n,
    fact (S n) = (S n) * fact n.
Proof.
  reflexivity.
Qed.


Lemma fact_cps_Sn :
  forall n f,
    fact_cps (S n) f =
    fact_cps n (fun (r:nat) => (f (S n * r))).
Proof.
  intros.
  simpl.
  reflexivity.
Qed.


(* fact_cps_Sn の実験 *)
Eval cbv in fact_cps 6 (fun (r:nat) => r).  (* 720 *)
Eval cbv in fact_cps 5 (fun (r:nat) => (6 * r)). (* 720 *)


Lemma eq_fact_fact_cps_aux :
  forall (n:nat),
    (forall f, f (fact n) = fact_cps n f) /\
    (forall g, g (fact (S n)) = fact_cps (S n) g).
Proof.
  intros.
  induction n.
  (* 再帰の底 *)
  auto.
  
  destruct IHn.
  split.
  (* /\の左 *)
  apply H0.
  
  (* /\の右 *)
  intro g.
  rewrite fact_cps_Sn.
  rewrite <- H0.
  rewrite fact_Sn.
  reflexivity.
Qed.


Theorem eq_fact_fact_cps :
  forall n f, f (fact n) = fact_cps n f.
Proof.
  intros.
  destruct (eq_fact_fact_cps_aux n).
  apply H.
Qed.


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
Fixpoint fib_cps (n:nat) (cont:nat -> A) : A :=
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
  rewrite fib0.
  rewrite fib_cps0.
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
Theorem eq_fib_fib_cps : forall n f, f (fib n) = fib_cps n f.
Proof.
  intros; destruct (eq_fib_fib_cps_aux n); apply H.
Qed.


(* END *)
