From mathcomp Require Import all_ssreflect.
From mathcomp Require Import ssrZ zify ring lra.
(* opam install coq-equations *)
From Equations Require Import Equations.
Import Arith.                               (* Nat.land_spec *)
Require Import Coq.Arith.Wf_nat.
Require Import Coq.Arith.Arith.

(**
ChatGPTに「div2 は整礎か」とだけ質問した回答をベースにしている。
*)

Section a.

(*
  Definition nat_ind2 :
    forall (P : nat -> Prop),
      P 0 ->
      P 1 ->
      (forall n : nat, P n -> P (S(S n))) ->
      forall n : nat , P n :=
    fun P => fun P0 => fun P1 => fun PSS =>
      fix f (n : nat) := match n with
                       | 0 => P0
                       | 1 => P1
                       | n'.+2 => PSS n' (f n')
                       end.
  (* .+1 はコンストラクタであるので、=> の左の書ける。 *)
*)
  
  Lemma nat_ind2 :
    forall P : nat -> Prop,
      P 0 ->
      P 1 ->
      (forall n : nat, P n -> P n.+2) ->
      forall n : nat, P n.
  Proof.
    move=> P HP0 HP1 IH n.
    have H : (P n /\ P n.+1).
    {
      elim : n => [| n [] HPn HPsn]; split => //=.
      by apply: IH.
    }.
    by case: H.
  Qed.

  Lemma coq_divn2 n : Nat.div2 n = n./2.
  Proof.
    elim/nat_ind2 : n => //= n IHn.
    by rewrite IHn.
  Qed.
  
(*
Fixpoint div2 (n : nat) : nat :=
  match n with
  | 0 => 0
  | 1 => 0
  | S (S n') => S (div2 n')
  end.
 *)
  Print Nat.div2.
  (*
Nat.div2 = fix div2 (n : nat) : nat := match n with
                                       | n'.+2 => (div2 n').+1
                                       | _ => 0
                                       end
*)

  Lemma div2_lt : forall n, 2 <= n -> Nat.div2 n < n.
  Proof.
    intros n H.
    destruct n as [| [| n']]; simpl in *.
    - inversion H. (* n = 0 の場合 *)
    - inversion H. (* n = 1 の場合 *)
    - (* n >= 2 の場合 *)
      (* n = S (S n') *)
      rewrite -[_.+1]addn1 -[_.+2]addn1 leq_add2r.
      rewrite ltnS.
      apply/leP/Nat.div2_decr.
      lia.
  Qed.

  Print Acc.
(*
Inductive Acc (A : Type) (R : A -> A -> Prop) (x : A) : Prop :=
    Acc_intro : (forall y : A, R y x -> Acc R y) -> Acc R x.
*)

  Print well_founded.
(*
fun (A : Type) (R : A -> A -> Prop) => forall a : A, Acc R a
     : forall [A : Type], (A -> A -> Prop) -> Prop
*)

  Definition div2_wf : well_founded (fun x y => Nat.div2 y = x /\ x < y).
  Proof.
    apply well_founded_lt_compat with (f := fun x => x).
    move=> x y [Heq Hlt].
    by apply/ltP.
  Qed.
  
  Lemma div2_ind :
    forall (P : nat -> Prop),
      P 0 ->
      P 1 ->
      (forall n, 1 < n -> P n./2 -> P n) ->
      forall n, P n.
  Proof.
    move=> P H0 H1 Hstep.
    apply: (well_founded_induction (well_founded_ltof _ (fun n => n))).
    case=> [| [| n'] IH] //=.
    apply: Hstep => //.
    apply: IH.
    rewrite /ltof.
    apply/ltP.
    rewrite -coq_divn2.
    by apply div2_lt.
  Qed.

(**
## 試みた類似の帰納法
*)
  
  Lemma double_ind :
    forall (P : nat -> Prop),
      P 0 ->
      P 1 ->
      (forall n, P n -> P n.*2) ->
      (forall n, P n -> P n.*2.+1) ->
      forall n, P n.
  Proof.
    move=> P HP0 HP1 IH1 IH2 n.
    have : P n.*2.
    elim: n.
    - by apply IH1.
    - move=> n H'.
      apply IH1.
  (* 通常の帰納法で n に対して構造帰納法を行う *)
  Admitted.


(* END *)
