Require Import List.
Require Import Cpdt.CpdtTactics.

Set Implicit Arguments.
Set Asymmetric Patterns.

Section stream.
  Variable A : Type.
  
  CoInductive stream : Type :=
  | Cons : A -> stream -> stream.
End stream.

Section stream_eq.
  Variable A : Type.
  
  CoInductive stream_eq : stream A -> stream A -> Prop :=
  | Stream_eq : forall h t1 t2,
      stream_eq t1 t2 -> stream_eq (Cons h t1) (Cons h t2).
End stream_eq.

Definition hd A (s : stream A) : A :=
  match s with
  | Cons x _ => x
  end.

Definition tl A (s : stream A) : stream A :=
  match s with
  | Cons _ s' => s'
  end.

Section stream_eq_coind.
  Variable A : Type.
  Variable R : stream A -> stream A -> Prop.

  Hypothesis Cons_case_hd : forall s1 s2, R s1 s2 -> hd s1 = hd s2.
  Hypothesis Cons_case_tl : forall s1 s2, R s1 s2 -> R (tl s1) (tl s2).

  Theorem stream_eq_coind : forall s1 s2, R s1 s2 -> stream_eq s1 s2.
    cofix; destruct s1; destruct s2; intro.
    generalize (Cons_case_hd H); intro Heq; simpl in Heq; rewrite Heq.
    constructor.
    apply stream_eq_coind.                  (* cofix で仮定に入る。 *)
    apply (Cons_case_tl H).
  Qed.
End stream_eq_coind.

Section stream_eq_loop.
  Variable A : Type.
  Variables s1 s2 : stream A.
  
  Hypothesis Cons_case_hd : hd s1 = hd s2.
  Hypothesis loop1 : tl s1 = s1.
  Hypothesis loop2 : tl s2 = s2.
  
  Theorem stream_eq_loop : stream_eq s1 s2.
    apply (stream_eq_coind (fun s1' s2' => s1' = s1 /\ s2' = s2));
      crush.
  Qed.
End stream_eq_loop.

Section stream_eq_onequant.
  Variables A B : Type.
  Variables f g : A -> stream B.
  
  Hypothesis Cons_case_hd : forall x, hd (f x) = hd (g x).
  Hypothesis Cons_case_tl : forall x, exists y, tl (f x) = f y /\ tl (g x) = g y.
  
  Theorem stream_eq_onequant : forall x, stream_eq (f x) (g x).
    intro; apply (stream_eq_coind (fun s1 s2 => exists x, s1 = f x /\ s2 = g x));
      crush; eauto.
  Qed.
End stream_eq_onequant.

(* ****** *)
(* sample *)
(* ****** *)
Fixpoint approx A (s : stream A) (n : nat) : list A :=
  match n with
  | O => nil
  | S n' =>
    match s with
    | Cons h t => h :: approx t n'
    end
  end.

Section map.
  Variables A B : Type.
  Variable f : A -> B.

  CoFixpoint map (s : stream A) : stream B :=
    match s with
    | Cons h t => Cons (f h) (map t)
    end.
End map.

CoFixpoint zeroes : stream nat := Cons 0 zeroes.
CoFixpoint ones : stream nat := Cons 1 ones.
Definition ones' := map S zeroes.

Theorem ones_eq'' : stream_eq ones ones'.
  apply (stream_eq_coind (fun s1 s2 => s1 = ones /\ s2 = ones')); crush.
Qed.

Theorem ones_eq''' : stream_eq ones ones'.
  apply stream_eq_loop; crush.
Qed.

(* ****** *)
(* sample *)
(* ****** *)
Require Import Arith.
Print fact.

CoFixpoint fact_slow' (n : nat) := Cons (fact n) (fact_slow' (S n)).
Definition fact_slow := fact_slow' 1.

CoFixpoint fact_iter' (cur acc : nat) := Cons acc (fact_iter' (S cur) (acc * cur)).
Definition fact_iter := fact_iter' 2 1.

Eval simpl in approx fact_iter 5.
Eval simpl in approx fact_slow 5.

Lemma fact_def : forall x n,
  fact_iter' x (fact n * S n) = fact_iter' x (fact (S n)).
  simpl; intros; f_equal; ring.
Qed.
Hint Resolve fact_def.

Lemma fact_eq' : forall n, stream_eq (fact_iter' (S n) (fact n)) (fact_slow' n).
  intro; apply (stream_eq_coind (fun s1 s2 => exists n, s1 = fact_iter' (S n) (fact n)
    /\ s2 = fact_slow' n)); crush; eauto.
Qed.

Theorem fact_eq : stream_eq fact_iter fact_slow.
  apply fact_eq'.
Qed.

Lemma fact_eq'' : forall n, stream_eq (fact_iter' (S n) (fact n)) (fact_slow' n).
  apply stream_eq_onequant; crush; eauto.
Qed.

Theorem fact_eq''' : stream_eq fact_iter fact_slow.
  apply fact_eq''.
Qed.

(* end *)
