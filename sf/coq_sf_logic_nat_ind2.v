(** ソフトウエアの基礎 Benjamin C. Pierceさん他、梅村さん他訳
   Prop_J: 命題と根拠
   Logic_J: Coqにおける論理 *)

(**
   nat_ind について考えてみる。
   *)

(** 通常のnatの定義 *)
Inductive nat : Type :=
| O : nat
| S : nat -> nat.
Print nat_rect.
Print nat_ind.

(** nat_rect を自分で定義してみる。 *)
Definition nat_rect_me : forall P : nat -> Type,
  P O ->
  (forall n : nat, P n -> P (S n)) ->
  forall n : nat, P n.
Proof.
  intros P f f0.
  (** Fは任意な名前。1はゴールの最初の前提 n を示す。*)
  fix F 1.                                  (* nによる帰納 *)
  intros n.
  destruct n.
  apply f.
  apply f0.
  apply F.
Qed.

(** nat_ind を自分で定義してみる。 *)
Definition nat_ind_me : forall P : nat -> Prop,
    P O ->                                  (* O : nat *)
    (forall n : nat, P n -> P (S n))  ->    (* S : nat -> nat *)
    forall n : nat, P n.
Proof.
  (* fun P : nat -> Prop => nat_rect P *)
  intros P H H0 n.
  apply nat_rect_me.
  apply H.
  apply H0.
Qed.

(** nat_ind を自分で定義してみる。nat_rectを使わない。 *)
Definition nat_ind_me'' :
  forall P : nat -> Prop,
    P O ->
    (forall n : nat, P n -> P (S n)) ->
    forall n : nat, P n.
Proof.
  intros P H H0 n.
  induction n.
  apply H.
  apply H0.
  apply IHn.
Qed.

(** nat_ind を自分で定義してみる。nat_rectを使わない。
   証明オブジェクトを直接書く。 *)
Definition nat_ind_me' :
  forall P : nat -> Prop,
    P O ->
    (forall n : nat, P n -> P (S n)) ->
    forall n : nat, P n :=
      fun (P : nat -> Prop)
        (f : P O)
    (f0 : forall n : nat, P n -> P (S n)) =>
    fix F (n : nat) : P n :=
    match n as n0 return (P n0) with
      | O => f
      | S n0 => f0 n0 (F n0)
    end.

(** nat_indを使った証明の例 *)
Fixpoint plus (n : nat) (m : nat) : nat :=
  match n with
    | O => m
    | S n' => S (plus n' m)
  end.
Notation "x + y" := (plus x y)  (at level 50, left associativity) : nat_scope.
Definition one : nat := S O.

(** 定理 n + 1 = S n *)
Theorem plus_one_r : forall n : nat,
  n + one = S n.
Proof.
  intros n.
  induction n as [ | n'] using nat_ind_me'.
  reflexivity.
  simpl.
  rewrite IHn'.
  reflexivity.
Qed.

(**
   nat_ind2 - 標準的でない帰納法の原理（二つずつ、となるような）
   *)
Definition nat_ind2 :
  forall (P : nat -> Prop),
    P O ->
    P (S O) ->
    (forall n : nat, P n -> P (S(S n))) ->
    forall n : nat , P n :=
      fun P => fun P0 => fun P1 => fun PSS =>
        fix f (n:nat) :=
        match n return P n with
          O => P0
          | (S O) => P1
          | S (S n') => PSS n' (f n')
        end.

(** nat_ind2を使ってみる。 *)
Inductive ev : nat -> Prop :=
| ev_0 : ev O
| ev_SS : forall n : nat, ev n -> ev (S (S n)).

Fixpoint evenb (n:nat) : bool :=
  match n with
    | O        => true
    | S O      => false
    | S (S n') => evenb n'
  end.

Definition even (n : nat) : Prop :=
  evenb n = true.

Lemma even_ev : forall n, even n -> ev n.
Proof.
 intros.
 induction n as [ | | n'] using nat_ind2.
 (* ev O *)
 apply ev_0.
 (* ev (S O) *)
 inversion H.
 (* ev (S (S n')) *)
 apply ev_SS.
 apply IHn'.
 unfold even.
 unfold even in H.
 simpl in H. apply H.
Qed.

(** ev_even は、coq_sf_prop.v と
   coq_sf_prop_proof_obj.v の両方で扱っている *)

(* END *)
