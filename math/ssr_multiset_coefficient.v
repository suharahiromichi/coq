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
    | _.+1, 0 => 1
    | (_, 0) => 1                           (* H(0, 0) = 1 になる。 *)
    | (0, _.+1) => 0 
    end.
  
  (* nat と nat ペアの合計 *)
  Definition sum (p : nat * nat) : nat :=
    match p with
    | (n, m) => n + m
    end.

  Function multiset_rec p {measure sum p} : nat :=
    match p with
    | (n'.+1 as n, m'.+1 as m)  => multiset_rec (n', m) + multiset_rec (n, m')
    | (_, 0) => 1                           (* H(0, 0) = 1 になる。 *)
    | (0, _.+1) => 0 
    end.
  Proof.
    - move=> p n m n' _ m' _ _.
      rewrite /sum.
      apply/ltP.
        by rewrite [n'.+1 + m'.+1]addnS.
    - move=> p n m n' _ m' _ _.
      rewrite /sum.
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

  Lemma msc1n (n : nat) : 'H(1, n) = 1.
  Proof.
    elim: n => //=.
    move=> n IHn.
    rewrite mscS msc0n add0n.
    done.
  Qed.
  
  Compute 'C(0, 0).                         (* 1 *)
  Compute 'C(0, 1).                         (**0**)
  
  Compute 'C(1, 0).                         (* 1 *)
  Compute 'C(1, 1).                         (* 1 *)
  Compute 'C(1, 2).                         (**0**)
  
  Compute 'C(2, 0).                         (* 1 *)
  Compute 'C(2, 1).                         (* 2 *)
  Compute 'C(2, 2).                         (* 1 *)
  Compute 'C(2, 3).                         (**0**)

  Compute 'C(3, 0).                         (* 1 *)
  Compute 'C(3, 1).                         (* 3 *)
  Compute 'C(3, 2).                         (* 3 *)
  Compute 'C(3, 3).                         (* 1 *)
  Compute 'C(3, 4).                         (**0**)
  
  Compute 'C(4, 0).                         (* 1 *)
  Compute 'C(4, 1).                         (* 4 *)
  Compute 'C(4, 2).                         (* 6 *)
  Compute 'C(4, 3).                         (* 4 *)
  Compute 'C(4, 4).                         (* 1 *)
  Compute 'C(4, 5).                         (**0**)

  (* **** *)

  Compute 'H(0, 0).                         (**1**) (* 漸化式では使わない。 *)
  Compute 'H(0, 1).                         (* 0 *)
  
  Compute 'H(1, 0).                         (* 1 *)
  Compute 'H(1, 1).                         (* 1 *)
  Compute 'H(1, 2).                         (* 1 *)
  
  Compute 'H(2, 0).                         (* 1 *)
  Compute 'H(2, 1).                         (* 2 *)
  Compute 'H(2, 2).                         (* 3 *)
  Compute 'H(2, 3).                         (* 4 *)
  Compute 'H(2, 4).                         (* 5 *)
  Compute 'H(2, 5).                         (* 6 *)
  Compute 'H(2, 6).                         (* 7 *)
  Compute 'H(2, 7).                         (* 8 *)
  Compute 'H(2, 8).                         (* 9 *)

  Compute 'H(3, 0).                         (* 1 *)
  Compute 'H(3, 1).                         (* 3 *)
  Compute 'H(3, 2).                         (* 6 *)
  Compute 'H(3, 3).                         (* 10 *)
  Compute 'H(3, 4).                         (* 15 *)
  Compute 'H(3, 5).                         (* 21 *)
  Compute 'H(3, 6).                         (* 28 *)
  Compute 'H(3, 7).                         (* 36 *)
  Compute 'H(3, 8).                         (* 45 *)
  
  Compute 'H(4, 0).                         (* 1 *)
  Compute 'H(4, 1).                         (* 4 *)
  Compute 'H(4, 2).                         (* 10 *)
  Compute 'H(4, 3).                         (* 20 *)
  Compute 'H(4, 4).                         (* 35 *)
  Compute 'H(4, 5).                         (* 56 *)
  Compute 'H(4, 6).                         (* 84 *)
  Compute 'H(4, 7).                         (* 120 *)
  Compute 'H(4, 8).                         (* 165 *)

(** ### *)

  Compute 3 * 'H(3.+1, 2).                  (* 30 *)
  Compute 2.+1 * 'H(3, 2.+1).               (* 30 *)
  
  Lemma mul_msc_diag n m : n * 'H(n.+1, m) = m.+1 * 'H(n, m.+1).
  Proof.
    elim: n m.
    - move=> m.
      by rewrite mul0n msc0n /= muln0.
    - move=> n IHn m.
      elim: m n IHn.
      + move=> n IHn.
          by rewrite msc0 muln1 msc1 mul1n.
      + move=> m IHm n IHn.
        rewrite mscS mulnDr IHm.
        * rewrite ['H(n.+1, m.+2)]mscS mulnDr -IHn.
          rewrite -!mulnDl.
          congr (_ * _).
          ssromega.
        * done.
  Qed.
  
  (* m の帰納法 *)
  Lemma msc_fact n m : 'H(n.+1, m) * n`! * m`! = (n + m)`!.
  Proof.
    elim: m n.
    - move=> n.
      rewrite msc0 mul1n.
      rewrite fact0 muln1.
      rewrite addn0.
      done.
    - move=> m IHm n.
      rewrite [(m.+1)`!]factS.
      rewrite !mulnA.
      rewrite [_ * m.+1]mulnC.
      rewrite !mulnA.
      rewrite -mul_msc_diag.
      
      rewrite [_ * n`!]mulnC mulnA.
      rewrite [n`! * n.+1]mulnC -factS.
      rewrite [(n.+1)`! * 'H(n.+2, m)]mulnC.
      rewrite IHm.
      
      rewrite addSnnS addnS.
      done.
  Qed.
  
  (* 条件が必要かも *)
  Lemma msc_factd (n m : nat) : 'H(n.+1, m) = (n + m)`! %/ (n`! * m`!).
  Proof.
    Proof.
      rewrite -msc_fact.
      rewrite -mulnA.
      Search _ ((_ * _) %/ _).
      rewrite mulnK.
      + done.
      + rewrite muln_gt0.
        rewrite 2!fact_gt0.
        done.
    Qed.
    
  Compute 'H(4, 3) * 3`!.                   (* 120 *)
  Compute (4 + 3 - 1) ^_ 3.                 (* 120 *)

  Lemma test (n m : nat) :
    ((n + m)`! %/ (n`! * m`!)) * m`! = (n + m)`! %/ (n + m - m)`!.
  Proof.
    Search _ (_ %/ _ * _).
    rewrite divn_mulAC.                     (* ******* *)
    - Search _ ((_ * _) %/ (_ * _)).    
      rewrite divnMr.
      + Search _ (_ + _ - _).
        rewrite -addnBA.
        * Search _ (_ - _ = 0).
            by rewrite subnn addn0.         (* subnn n : n - n = 0 *)
        * done.
      + Search _ (0 < _`!).
          by rewrite fact_gt0.
    - (* n`! * m`! %| (n + m)`! *)
  Admitted.                                 (* ******* *)
  
  Lemma msc_ffact (n m : nat) : 'H(n, m) * m`! = (n + m - 1) ^_ m.
  Proof.
    case: n => [| n].
    - rewrite add0n.
      rewrite msc0n.
      case: m => [| m].
      + rewrite mul1n.
        rewrite subn1 PeanoNat.Nat.pred_0.  (* 0.-1 = 0 *)
        rewrite fact0 ffact0n.
        done.
      + rewrite ffact_small; first by done.
        rewrite subn1.
        ssromega.
    - rewrite ffact_factd.
      + rewrite msc_factd.
        rewrite addSn subn1 -pred_Sn.
          by rewrite test.
      + by ssromega.
  Qed.
  
  Lemma msc_ffactd n m : 'H(n, m) = (n  + m - 1) ^_ m %/ m`!.
  Proof.
      by rewrite -msc_ffact mulnK ?fact_gt0.
  Qed.
  
  (* ************************* *)
  (* H(n, m) = C(n + m - 1, m) *)
  (* ************************* *)  
  
  Compute 'H(3, 2).                         (* 6 *)
  Compute 'C(4, 2).                         (* 6 *)
  
  Compute 'H(5, 3).                         (* 6 *)
  Compute 'C(7, 3).                         (* 6 *)

  Compute 'H(2, 1).                         (* 2 *)
  Compute 'C(2, 1).                         (* 2 *)
  
  Compute 'H(1, 0).                         (* 2 *)
  Compute 'C(0, 0).                         (* 2 *)
  
  (* **************** *)
  (* 求めたかったもの *)
  (* **************** *)
  
  Lemma multiset_binominal (n m : nat) : 'H(n.+1, m) = 'C(n + m, m).
  Proof.
    rewrite bin_ffactd.
    rewrite msc_ffactd.
      by rewrite addSn subn1 -pred_Sn.
  Qed.
  
  (* ******************* *)
  (* 帰納法による直接証明 *)
  (* ******************* *)
  
  Lemma multiset_binominal' (n m : nat) : 'H(n.+1, m) = 'C(n + m, m).
  Proof.
    elim: m n => [n | m IHm n].
    - by rewrite msc0 bin0.
    - elim: n IHm => [IHm | n IHn IHm].
      + rewrite add0n.
        rewrite binS.
        rewrite mscS.
        rewrite IHm.
        f_equal.
        (* 両辺とも 0 になる。 *)
        Compute 'H(0, 4).                   (* 0 *)
        Compute 'C(3, 5).                   (* 0 *)
        rewrite msc0n.
        rewrite bin_small.
        * done.
        * done.
      + rewrite mscS.
        rewrite [n.+1 + m.+1]addnC addnS binS.
        rewrite IHm.
        f_equal.
        rewrite IHn.
        * by rewrite addnS addSn addnC.
        * move=> n'.
          by rewrite IHm.
        * by rewrite 2!addSn addnC.
  Qed.

End MC.

(* END *)
