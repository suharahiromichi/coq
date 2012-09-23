(* 有限な等差級数（等差数列の和）の「公式」を証明する。 *)
(*
   以下の式を証明する。
   Sum(n) = Σ(i=0, n) = 0 + 1 + ... + n = n * (n + 1) / 2

   ただし、(1/2)は扱い難いので、2倍して、以下を証明する。
   Sum2(n) = 2 * Σ(i=0, n) = 2 * (0 + 1 + ... + n) = n * (n + 1)
   *)

(*****************************************************************
   0以上の自然数と、その足し算と掛け算を定義する。
   ***************************************************************)
Inductive nat : Type :=
  | O : nat
  | S : nat -> nat.                         (* Sは後者関数 *)

Fixpoint plus (n : nat) (m : nat) : nat :=
  match n with
    | O => m
    | S n' => S (plus n' m)
  end.
Notation "x + y" := (plus x y)  (at level 50, left associativity) : nat_scope.

Fixpoint mult (n m : nat) : nat :=
  match n with
    | O => O
    | S n' => plus m (mult n' m)
  end.
Notation "x * y" := (mult x y)  (at level 40, left associativity) : nat_scope.
(* 自然数の定義、おわり *)

(*****************************************************************
   等差数列の和の（帰納的、繰り返し的）定義
   Sum(0) = 0
   Sum(n + 1) = 1 + Sum(n)

   実際は2倍のほうを使う。
   Sum2(0) = 0
   Sum2(n + 1) = 2 + Sum2(n)
   ***************************************************************)
(* issum n s は、0からnまでの（等差数列）の総和がsであることを示す。 *)
Inductive issum : nat -> nat -> Prop :=
| Sum_0 : issum O O                         (* 0までの総和は0 *)
| Sum_N : 
  forall (n s : nat),
    issum n s -> issum (S n) (S n + s).     (* nまでの総和が *)

(* issum2 n s は、0からnまでの（等差数列）の総和の2倍がsであることを示す。 *)
Inductive issum2 : nat -> nat -> Prop :=
| Sum2_0 : issum2 O O                       (* 0までの総和は0 *)
| Sum2_N : 
  forall (n s : nat),
    issum2 n s -> issum2 (S n) (S n + S n + s). (* nまでの総和が *)
(* 等差数列の和の定義、終わり *)

(*****************************************************************
   自然数の足し算と掛け算の法則のうち必要なものを泥縄式に証明する。
   ***************************************************************)
Theorem plus_n_Sm : forall n m,
  S (m + n) = m + S n.
Proof.  
  intros n m.
  induction m as [| m'].
  simpl.
  reflexivity.
  simpl.
  rewrite IHm'.
  reflexivity.
Qed.

Theorem plus_swap : forall n m p : nat,
  n + (m + p) = m + (n + p).
Proof.
  intros n m p.
  induction n as [| n'].
  simpl.
  reflexivity.

  simpl.
  rewrite <- plus_n_Sm.
  f_equal.
  apply IHn'.
Qed.

Theorem plus_assoc : forall n m p : nat,
  n + (m + p) = (n + m) + p.
Proof.
  intros n m p.
  induction n as [| n'].
  reflexivity.
  simpl.
  rewrite -> IHn'.
  reflexivity.
Qed.

Theorem mult_n_Sm : forall n m,
  n + n * m = n * S m.
Proof.
  intros n m.
  induction n as [| n'].
  simpl.
  reflexivity.
  simpl.
  f_equal.
  rewrite <- IHn'.
  apply plus_swap.
Qed.

Theorem mult_develop : forall n m,
  S n + m + n * m  = S n * S m.
Proof.
  intros n m.
  simpl.
  f_equal.
  rewrite <- mult_n_Sm.
  rewrite <- plus_swap. 
  rewrite plus_assoc.
  reflexivity.
Qed.
(* 自然数の足し算と掛け算の法則、終わり *)

(*****************************************************************
   等差数列の和の（帰納的、繰り返し的）定義と、いわゆる「公式」が一致す
   ることを証明する。
   Sum(n) = n * (n + 1) / 2
   
   実際は、2倍して証明する。
   Sum2(n) = n * (n + 1)
   ***************************************************************)
Theorem sum_of_arith_progress : forall n,
  issum2 n (n * S n).
Proof.
  intros n.
  
  (* nについての帰納法をおこなう。*)
  induction n as [| n'].

  (* n = 0 のとき *)
  simpl.
  apply Sum2_0.

  (* n = S n' *)
  rewrite <- mult_develop.
  Check Sum2_N.
  apply Sum2_N.
  apply IHn'.
Qed.

(* [] *)
