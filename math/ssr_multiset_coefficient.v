From mathcomp Require Import all_ssreflect.
Require Import ssromega.
Require Import Recdef.                      (* Function *)
Require Import Wf_nat.                      (* wf *)
Require Import Program.Wf.                  (* Program wf *)
(* Import Program とすると、リストなど余計なものがついてくるので、Wfだけにする。 *)

Require Import Extraction.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
(* Set Print All. *)

(**
# 多重集合係数 (Multiset Coefficient, Homogeneous Product)

https://ja.wikipedia.org/wiki/重複組合せ
*)
Section MC.

  Definition ltnn (p : nat * nat) : Prop := True.

  Fail Fixpoint multiset_rec n m : nat :=
    match n, m with
    | n'.+1, m'.+1 => multiset_rec n' m + multiset_rec n m'
    | _, 0 => 1
    | 0, _.+1 => 0
    end.
  
  (* nat と nat ペアの合計 *)
  Definition ptotal (p : nat * nat) : nat :=
    match p with
    | (n, m) => n + m
    end.

  Function multiset_rec p {measure ptotal p} : nat :=
    match p with
    | (n'.+1 as n, m'.+1 as m)  => multiset_rec (n', m) + multiset_rec (n, m')
    | (_, 0) => 1
    | (0, _.+1) => 0                        (* (0, _) でもよい。 *)
    end.
  Proof.
    - move=> p n m n' _ m' _ _.
      rewrite /ptotal.
      apply/ltP.
        by rewrite [n'.+1 + m'.+1]addnS.
    - move=> p n m n' _ m' _ _.
      rewrite /ptotal.
      apply/ltP.
        by rewrite [n'.+1 + m'.+1]addSn.
  Defined.

  Definition multiset := nosimpl multiset_rec.
  
  (* Homogeneous Product *)
  Notation "''H' ( n , m )" := (multiset (n, m))
  (at level 8, format "''H' ( n ,  m )") : nat_scope.
  
  Check bin0 : forall n : nat, 'C(n, 0) = 1.
  Check bin0n : forall m : nat, 'C(0, m) = (m == 0).
  Check binS : forall n m : nat, 'C(n.+1, m.+1) = 'C(n, m.+1) + 'C(n, m).
  Check bin1 : forall n : nat, 'C(n, 1) = n.
  Check bin_ffact : forall (n m : nat), 'C(n, m) * m`! = n ^_ m.
  Check bin_ffactd : forall (n m : nat), 'C(n, m) = n ^_ m %/ m`!.

  Lemma mulE : multiset = multiset_rec.
  Proof. by []. Qed.
  
  Lemma mul0 (n : nat) : 'H(n, 0) = 1.
  Proof. by case: n. Qed.

  Lemma mul0n (m : nat) : 'H(0, m) = (m == 0).
  Proof. by case: m. Qed.
  
  Lemma mulS n m : 'H(n.+1, m.+1) = 'H(n, m.+1) + 'H(n.+1, m).
  Proof.
      by rewrite /multiset multiset_rec_equation.
  Qed.
  
  Lemma mul1 n : 'H(n, 1) = n.
  Proof.
    elim: n => //=.
    move=> n IHn.
      by rewrite mulS mul0 IHn addn1.
  Qed.

  Lemma mul_ffact : forall (n m : nat), 'H(n, m) * m`! = (n + m - 1) ^_ m.
  Proof.
  Admitted.

  Lemma mul_ffactd n m : 'H(n, m) = (n  + m - 1) ^_ m %/ m`!.
  Proof. by rewrite -mul_ffact mulnK ?fact_gt0. Qed.
  
  (* ************************* *)
  (* H(n, m) = C(n + m - 1, m) *)
  (* ************************* *)  
  
  Compute 'H(3, 2).                         (* 6 *)
  Compute 'C(4, 2).                         (* 6 *)
  
  Goal forall (n m : nat), 'H(n.+1, m) = 'C(n + m, m).
  Proof.
    move=> n m.
    rewrite bin_ffactd.
    rewrite mul_ffactd.
      by rewrite addSn subn1 -pred_Sn.
  Qed.
  
  (* 帰納法による直接証明。途中 *)
  Goal forall (n m : nat), 'H(n.+1, m) = 'C(n + m, m).
  Proof.
    move=> n m.
    elim : m.
    - by rewrite mul0 bin0.
    - move=> m IHm.
      rewrite addnS binS mulS IHm.
      congr (_ + _).
      (* 'H(n, m.+1) = 'C(n + m, m.+1) *)
  Admitted.

End MC.

(* END *)
