From mathcomp Require Import all_ssreflect.
From common Require Import ssromega.
Require Import Recdef.                      (* Function *)
Require Import Wf_nat.                      (* wf *)
Require Import Program.Wf.                  (* Program wf *)
(* Import Program とすると、リストなど余計なものがついてくるので、Wfだけにする。 *)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
(* Set Print All. *)

(**
# 多重集合係数 (Multiset Coefficient, Homogeneous Product)

https://ja.wikipedia.org/wiki/重複組合せ
*)
Section DEFINE.

  Definition ltnn (p : nat * nat) : Prop := True.

  Fail Fixpoint multiset_rec n m : nat :=
    match n, m with
    | n'.+1, m'.+1 => multiset_rec n' m + multiset_rec n m'
    | _, 0 => 1                           (* H(0, 0) = 1 になる。 *)
    | 0, _.+1 => 0 
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

End DEFINE.
  
(* Homogeneous Product *)
Notation "''H' ( n , m )" := (multiset (n, m))
(at level 8, format "''H' ( n ,  m )") : nat_scope.
  
Section LEMMAS.
  (* multset coefficient から msc とする。mul だと衝突するため。 *)
  
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
  
  Lemma msc_factd (n m : nat) : 'H(n.+1, m) = (n + m)`! %/ (n`! * m`!).
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
  
  (* こんな補題くらいは、証明されていないのだろうか？ *)
  Compute 0`! * 0`! %| (0 + 0)`!.   (* true *)
  Compute 1`! * 0`! %| (1 + 0)`!.   (* true *)
  Compute 1`! * 1`! %| (1 + 1)`!.   (* true *)
  Compute 2`! * 1`! %| (2 + 1)`!.   (* true *)
  Compute 2`! * 2`! %| (2 + 2)`!.   (* true *)
  Compute 3`! * 1`! %| (3 + 1)`!.   (* true *)
  
  Lemma divn_fact_mul_add_fact (n m : nat) : n`! * m`! %| (n + m)`!.
  Proof.
    rewrite -msc_fact.
    rewrite -[n`! * m`!]mul1n.
    rewrite -['H(n.+1, m) * n`! * m`!]mulnA.
    by apply: dvdn_mul.
  Qed.
  
  (* bin を使っても証明できる。こちらのほうがよいかもしれない。 *)
  Lemma divn_fact_mul_add_fact' (n m : nat) : n`! * m`! %| (n + m)`!.
  Proof.
    have H : 'C(n + m, m) * (n`! * m`!) = (n + m)`!.
    - rewrite -(@bin_fact (n + m) m); last by rewrite leq_addl.
      rewrite -[n + m - m]addnBA; last by rewrite leqnn.
      by rewrite subnn addn0 [m`! * n`!]mulnC.
    - rewrite -H.
      rewrite -{1}[n`! * m`!]mul1n.
      by apply: dvdn_mul.
  Qed.  
  
  Lemma msc_ffact (n m : nat) : 'H(n.+1, m) * m`! = (n + m) ^_ m.
  Proof.
    case: n => [| n].
    - rewrite msc1n mul1n.
      rewrite add0n ffactnn.
      done.
    - rewrite ffact_factd.
      + rewrite msc_factd.
        rewrite divn_mulAC.
        * rewrite divnMr.
          ** rewrite -addnBA; last done.
               by rewrite subnn addn0.    (* subnn n : n - n = 0 *)
          ** by rewrite fact_gt0.
        * by rewrite divn_fact_mul_add_fact.
      + by ssromega.
  Qed.
  
  Lemma msc_ffactd n m : 'H(n.+1, m) = (n + m) ^_ m %/ m`!.
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
  
  Lemma multiset_binomial (n m : nat) : 'H(n.+1, m) = 'C(n + m, m).
  Proof.
    rewrite bin_ffactd.
    rewrite msc_ffactd.
    done.
  Qed.
  
  (* ******************* *)
  (* 帰納法による直接証明 *)
  (* ******************* *)
  
  (* m -> n の順番 *)
  Lemma multiset_binomial' (n m : nat) : 'H(n.+1, m) = 'C(n + m, m).
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
  
  (* n -> m の順番 *)
  Lemma multiset_binomial'' (n m : nat) : 'H(n.+1, m) = 'C(n + m, m).
  Proof.
    elim: n m => [m |n IHn m].
    - by rewrite msc1n add0n binn.
    - elim: m IHn => [IHn | m IHm IHn].
      + by rewrite msc0 bin0.
      + rewrite mscS.
        rewrite [n.+1 + m.+1]addnC addnS binS.
        rewrite IHm => [| m'].
        * rewrite [n.+1 + m]addSn.
          rewrite [m.+1 + n]addSn.
          rewrite [m + n]addnC.
          f_equal.
          rewrite IHn.
          rewrite [n + m.+1]addnS.
          done.
        * rewrite IHn.
          done.
  Qed.
  
End LEMMAS.

(* END *)
