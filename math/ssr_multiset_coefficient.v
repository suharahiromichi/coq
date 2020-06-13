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
  Check bin_fact : forall n m : nat, m <= n -> 'C(n, m) * (m`! * (n - m)`!) = n`!.
  Check bin_ffact : forall (n m : nat), 'C(n, m) * m`! = n ^_ m.
  Check bin_ffactd : forall (n m : nat), 'C(n, m) = n ^_ m %/ m`!.
  
  (* multset coefficient から msc とする。mul だと衝突するため。 *)
  Lemma mscE : multiset = multiset_rec.
  Proof. by []. Qed.
  
  Lemma msc0 (n : nat) : 'H(n, 0) = 1.
  Proof. by case: n. Qed.

  Lemma msc0n (m : nat) : 'H(0, m) = (m == 0).
  Proof. by case: m. Qed.
  
  Lemma mscS n m : 'H(n.+1, m.+1) = 'H(n, m.+1) + 'H(n.+1, m).
  Proof.
      by rewrite /multiset multiset_rec_equation.
  Qed.
  
  Lemma msc1 n : 'H(n, 1) = n.
  Proof.
    elim: n => //=.
    move=> n IHn.
      by rewrite mscS msc0 IHn addn1.
  Qed.

  Compute 'C(0, 0).                         (* 1 *)
  Compute 'C(0, 1).                         (* 0 *)
  Compute 'C(0, 2).                         (* 0 *)
  Compute 'C(1, 2).                         (* 0 *)

  Compute 'H(0, 0).                         (* 1 *)
  Compute 'H(0, 1).                         (* 0 *)
  Compute 'H(0, 2).                         (* 0 *)
  Compute 'H(1, 2).                         (* 1 *)
  
  Lemma msc_small n m : n < m -> 'H(n, m) = 0.
(*
  Proof. by rewrite ltnNge -bin_gt0; case: posnP. Qed.
 *)
  Admitted. 
  
Lemma bin_ffact n m : 'C(n, m) * m`! = n ^_ m.
Proof.
apply/eqP; have [lt_n_m | le_m_n] := ltnP n m.
  by rewrite bin_small ?ffact_small.
by rewrite -(eqn_pmul2r (fact_gt0 (n - m))) ffact_fact // -mulnA bin_fact.
Qed.

  Lemma msc_ffact (n m : nat) : 'H(n, m) * m`! = (n + m - 1) ^_ m.
  Proof.
    apply/eqP; have [lt_n_m | le_m_n] := ltnP n m.
    - rewrite msc_small.
      rewrite mul0n.
      + rewrite ?ffact_small.
        done.
      + 
      
    rewrite /multiset multiset_rec_equation.
    apply/eqP.
    


(*
      by rewrite msc_small ?ffact_small.
        by rewrite -(eqn_pmul2r (fact_gt0 (n - m))) ffact_fact // -mulnA bin_fact.
*)
  Admitted.

  Lemma msc_ffactd n m : 'H(n, m) = (n  + m - 1) ^_ m %/ m`!.
  Proof. by rewrite -msc_ffact mulnK ?fact_gt0. Qed.
  
  (* ************************* *)
  (* H(n, m) = C(n + m - 1, m) *)
  (* ************************* *)  
  
  Compute 'H(3, 2).                         (* 6 *)
  Compute 'C(4, 2).                         (* 6 *)
  
  Goal forall (n m : nat), 'H(n.+1, m) = 'C(n + m, m).
  Proof.
    move=> n m.
    rewrite bin_ffactd.
    rewrite msc_ffactd.
      by rewrite addSn subn1 -pred_Sn.
  Qed.
  
  (* 帰納法による直接証明。途中 *)
  Goal forall (n m : nat), 'H(n.+1, m) = 'C(n + m, m).
  Proof.
    move=> n m.
    elim : m.
    - by rewrite msc0 bin0.
    - move=> m IHm.
      rewrite addnS binS mscS IHm.
      congr (_ + _).
      (* 'H(n, m.+1) = 'C(n + m, m.+1) *)
  Admitted.

End MC.

(* END *)
