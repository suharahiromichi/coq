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

(* END *)
