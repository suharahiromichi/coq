From mathcomp Require Import all_ssreflect.
From mathcomp Require Import ssrZ zify ring lra.
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

  Locate "_ ./2".                        (* := (half n) : nat_scope *)
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
  Lemma coq_divn2 n : Nat.div2 n = n./2.
  Proof.
    elim/nat_ind2 : n => //= n IHn.
    by rewrite IHn.
  Qed.
  
  Lemma div2_lt : forall n, 2 <= n -> Nat.div2 n < n.
  Proof.
    (*
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
*)
    case => [| [| n' IH]] //.
    rewrite -2!addn1 leq_add2r.
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

  (* 不使用 *)
  Definition div2_wf : well_founded (fun x y => Nat.div2 y = x /\ x < y).
  Proof.
    (* 関係R から lt が導けるなら、関係 R は整礎である。 *)
    Check (@well_founded_lt_compat _ id)
      : forall R : nat -> nat -> Prop, (forall x y : nat, R x y -> (x < y)%coq_nat) -> well_founded R.
    apply: (@well_founded_lt_compat _ id).
    
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
    
    (* lt についての整礎帰納法で証明する。 *)
    Check well_founded_induction
      : forall (A : Type) (R : A -> A -> Prop),
        well_founded R ->
        forall P : A -> Set, (forall x : A, (forall y : A, R y x -> P y) -> P x) -> forall a : A, P a.
(*
    Check well_founded_ltof
      : forall (A : Type) (f : A -> nat), well_founded (ltof A f).
    Print ltof. (* = fun (A : Type) (f : A -> nat) (a b : A) => (f a < f b)%coq_nat *)
    (* ltof ではばく、単に lt が整礎であればよい。 *)
*)
    Check lt_wf : well_founded lt.
    Check lt_wf : forall a : nat, Acc lt a.  (* lt が well_founded である。 *)
    Check forall P : nat -> Set,
        (forall x : nat, (forall y : nat, (y < x)%coq_nat -> P y) -> P x) -> forall a : nat, P a.

    Check well_founded_induction lt_wf
      : forall P : nat -> Set,
        (forall x : nat, (forall y : nat, (y < x)%coq_nat -> P y) -> P x) -> forall a : nat, P a.
    
    apply: (well_founded_induction lt_wf).
(*
    case=> //=.                   (* n を 0 と n'+1 に場合分する。 *)
    case=> //=.                   (* n を 1 と n'+2 に場合分する。 *)
*)
    case=> [| [|]] //= n IH. (* n を 0 と 1 と n'+2 に場合分けする。 *)
    apply: Hstep => //.
    apply: IH.
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
