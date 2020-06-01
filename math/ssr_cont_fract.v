From mathcomp Require Import all_ssreflect.
Require Import ssromega.
Require Import FunInd.                      (* Functional Scheme *)
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
# 連分数 Continued fraction
 *)
Section CF.
  
  (* notu *)
  Program Fixpoint f2cf'p (n m : nat) {wf lt m} : (seq nat) :=
    match m with
    | 0 => [::]
    | _ => (n %/ m) :: f2cf'p m (n %% m)
    end.
  Obligation 1.
  Proof.
    apply/ltP/ltn_pmod.
    move/Lt.neq_0_lt in H.
    apply/ltP/H.
  Qed.
  Compute f2cf'p 36 11.                     (* [:: 3; 3; 1; 2] *)
  
  Function f2cf' (n m : nat) {wf lt m} : (seq nat) :=
    match m with
    | 0 => [::]
    | _ => (n %/ m) :: f2cf' m (n %% m)
    end.
  Proof.
    - move=> n m m0 _.
      apply/ltP.
        by rewrite ltn_mod.
    - by apply: lt_wf.
  Defined.                                (* Defined が必要である。 *)
  (* functional inducntion が可能になる。 *)

  Definition f2cf (p : (nat * nat)) : (seq nat) := f2cf' p.1 p.2.
  Compute f2cf (36, 11).
  
  Fixpoint cf2f (sa : seq nat)  : (nat * nat) :=
    match sa with
    | a :: sa' =>
      (a * (cf2f sa').1 + (cf2f sa').2, (cf2f sa').1)
    (* let (p1, p2) := cf2f sa' in (a * p1 + p2, p1) *)
    | [::] => (1, 0)
    end.

  Compute cf2f [:: 3; 3; 1; 2].             (* (36, 11) *)
  Compute cf2f [:: 0; 1; 1; 1; 1; 1; 1].
  Compute cf2f [:: 1; 2; 2; 2; 2; 2; 2].  
  
  Compute cf2f (f2cf (36, 11)).             (* (36, 11) *)
  Compute cf2f (f2cf (72, 22)).             (* (36, 11) *)
  
  Goal forall p, cf2f (f2cf p) = p.
  Proof.
    case=> n m.
    functional induction (f2cf' n m).
    - rewrite /=.
      (* (1, 0) = (n, 0) .... p は既約になるので。 *)
      admit.
    - case: m y IHl => [H IHl | m H IHl].
      + done.
      + admit.
(**
  IHl : cf2f (f2cf (m.+1, n %% m.+1)) = (m.+1, n %% m.+1)
  ============================
  cf2f (f2cf (n, m.+1)) = (n, m.+1)
 *)
  Admitted.                                 (* OK *)

(**
cf2f (f2cf p) = p は証明できない（pが簡約される）ので、
f2cf (cf2f s) = s を証明する。
*)  
  Lemma f2cfE (n m : nat) : f2cf' n m = (n %/ m) :: f2cf' m (n %% m).
  Proof.
  Admitted.                                 (* あきらめ *)

  Search _ ((_ * _ + _) %/ _). 
  Lemma test1 n m r : (n * m + r) %/ m = n.
  Proof.
    rewrite divnMDl.
    (* n + r %/ m = n *)
  Admitted.                                 (* あきらめ *)

  Search _ ((_ * _ + _) %% _).   
  Lemma test2 n m r : (n * m + r) %% m = r.
  Proof.
    rewrite modnMDl.
    (* r %% m = r *)
  Admitted.                                 (* あきらめ *)
  
  Goal forall s, f2cf (cf2f s) = s.
  Proof.
    elim.
    - done.
    - move=> n s IHs.
      simpl.
      rewrite /f2cf /=.
      rewrite f2cfE /=.
      rewrite test1.
      rewrite test2.
      rewrite /f2cf in IHs.
      rewrite IHs.
      done.
  Qed.
End CF.

(**
# continuant polynomial

平方根の連分数とペル方程式
有澤健治
https://leo.aichi-u.ac.jp/~keisoken/research/books/book51/book51.pdf
では H(・) と表記されている。前に追加する。リストによる定義。

Concrete Mathematics
6.7 CONTINUANTS
では K(・) と表記されている。後ろに追加する。revによる定義。
 *)
Section CP.

  (* notu *)
  Program Fixpoint GaussHp (s : seq nat) {measure (size s)} : nat :=
    match s with
    | [::] => 1
    | [:: n] => n
    | n0 :: n1 :: s' => n0 * GaussHp (n1 :: s') + GaussHp s'
    end.
  Obligation 2.
  Proof.
    apply/ltP => /=.
    (* size s' < (size s').+2 *)
    ssromega.
  Qed.

  Function GaussH (s : seq nat) {measure size s} : nat :=
    match s with
    | [::] => 1
    | [:: n] => n
    | n0 :: n1 :: s' => n0 * GaussH (n1 :: s') + GaussH s'
    end.
  Proof.
    - move=> s n0 l n1 s' H1 H2.
      apply/ltP => /=.
      ssromega.
    - move=> s n0 l n1 s' H1 H2.
      apply/ltP => /=.
      ssromega.
  Defined.
  
  Compute GaussH [:: 3; 3; 1; 2].           (* 36 *)
  Compute GaussH [:: 3; 1; 2].              (* 11 *)
  Compute cf2f [:: 3; 3; 1; 2].             (* (36, 11) *)
  
(**
## 連分数とcontinuant
*)
  Lemma cf2fE n0 n1 s :
    (cf2f [:: n0, n1 & s]).1 = n0 * (cf2f (n1 :: s)).1 + (cf2f s).1.
  Proof.
    done.
  Qed.
  
  Goal forall s, (cf2f s).1 = GaussH s.
  Proof.
    move=> s.
    functional induction (GaussH s).
    - done.
    - by rewrite /cf2f muln1 addn0.
    - rewrite -IHn -IHn0.
      rewrite -cf2fE.
      done.
  Qed.
  
  Goal forall n s, (cf2f (n :: s)).2 = GaussH s.
  Proof.
    move=> n s.
    functional induction (GaussH s).
    - done.
    - by rewrite /cf2f muln1 addn0.
    - rewrite -IHn0 -IHn1.
      rewrite -cf2fE.
      done.
  Qed.
  
(**
## continuant の性質
*)

  Compute GaussH [:: 1;2;3;4;5].                       (* 225 *)
  Compute GaussH [:: 5;4;3;2;1].                       (* 225 *)
  Compute 5 * GaussH [:: 1;2;3;4] + GaussH [:: 1;2;3]. (* 225 *)

  Compute (GaussH [:: 1;2;3] * GaussH [:: 4;5]) + (GaussH [:: 1;2] * GaussH [:: 5]).
  (* 225 *)

  Lemma GaussHE (n0 n1 : nat) (s : seq nat) :
    GaussH (n0 :: n1 :: s) = n0 * GaussH (n1 :: s) + GaussH s.
  Proof.
    functional induction (GaussH s).
    - done.
    - done.
    - Admitted.                             (* あきらめ *)
  
  Lemma GaussHEr (n0 n1 : nat) (s : seq nat) :
    GaussH (rcons (rcons s n1) n0) = n0 * GaussH (rcons s n1) + GaussH s.
  Proof.
    functional induction (GaussH s).
    - rewrite GaussHE /GaussH /=.
      by rewrite mulnC.
    - rewrite GaussHE /GaussH /=.
    (* n * (n1 * n0 + 1) + n0 = n0 * (n * n1 + 1) + n *)
      rewrite !mulnDr !mulnA !muln1.
      rewrite ?addnA addnAC.                (* n を最後に。 *)
      rewrite ?mulnA mulnAC.                (* n1 を最後に。 *)
      rewrite -?mulnA mulnCA.               (* n0 を最初に。 *)
      done.
    - rewrite /=.
      rewrite GaussHE IHn0 /=.
      rewrite GaussHE IHn /=.
      rewrite !mulnDr.
      rewrite ?addnA.
      rewrite [n2 * (n0 * GaussH (n3 :: rcons s' n1))]mulnCA.
      ssromega.
  Qed.
  
  Goal forall s, GaussH s = GaussH (rev s).
  Proof.
    move=> s.
    functional induction (GaussH s).
    - done.
    - done.
      rewrite !rev_cons.
      rewrite GaussHEr.
      rewrite -rev_cons.
      rewrite IHn IHn0.
      done.
  Qed.

(**
## 黄金比はフィボナッチ数に等しい。
*)
  Compute GaussH [::].                      (* 1 = fib 1 *)
  Compute GaussH [:: 1].                    (* 1 = fib 2 *)
  Compute GaussH [:: 1; 1].                 (* 2 = fib 3 *)
  Compute GaussH [:: 1; 1; 1].              (* 3 = fib 4 *)
  Compute GaussH (nseq 3 1).                (* 3 = fib 4 *)

  Function fib (n : nat) : nat :=
    match n with
    | 0 => 0
    | 1 => 1
    | (m.+1 as pn).+1 => fib m + fib pn (* fib n.-2 + fib n.-1 *)
    end.
  
  Lemma fibE n : fib n.+2 = fib n + fib n.+1.
  Proof.
    done.
  Qed.
  
  Goal forall n, GaussH (nseq n 1) = fib n.+1.
  Proof.
    move=> n.
    functional induction (fib n).
    - done.
    - done.
    - rewrite fibE -IHn0 -IHn1.
      rewrite [nseq _.+2 1]/=.
      rewrite GaussHE mul1n.
      rewrite [nseq _.+1 1]/=.
        by rewrite addnC.
  Qed.
End CP.

(* END *)
