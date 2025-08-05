From mathcomp Require Import all_ssreflect.
From mathcomp Require Import ssrZ zify ring lra.
(* opam install coq-equations *)
From Equations Require Import Equations.
Import Arith.                               (* Nat.land_spec *)
Require Import Coq.Arith.Wf_nat.
Require Import Coq.Arith.Arith.

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
  intros x y [Heq Hlt]. subst.
  apply/ltP.
  done.
Qed.

Lemma div2_ind :
  forall (P : nat -> Prop),
    P 0 ->
    P 1 ->
    (forall n, 1 < n -> P (Nat.div2 n) -> P n) ->
    forall n, P n.
Proof.
  move=> P H0 H1 Hstep.
  apply: (well_founded_induction (well_founded_ltof _ (fun n => n))).
  case=> [| [| n'] IH] //=.
  apply: Hstep => //.
  apply: IH.
  rewrite /ltof.
  apply/ltP.
  by apply div2_lt.
Qed.

(* END *)
