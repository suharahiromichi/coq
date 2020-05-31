(**
連分数 Continued fraction
*)

From mathcomp Require Import all_ssreflect.
From mathcomp Require Import all_algebra.
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

Section CF.

  Program Fixpoint f2cf'' (n m : nat) {wf lt m} : (seq nat) :=
    match m with
    | 0 => [::]
    | _ => (n %/ m) :: f2cf'' m (n %% m)
    end.
  Obligation 1.
  Proof.
    apply/ltP/ltn_pmod.
    move/Lt.neq_0_lt in H.
    apply/ltP/H.
  Qed.
  Compute f2cf'' 36 11.                     (* [:: 3; 3; 1; 2] *)
  
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
  (* f2fc'_ind が定義されるので、functional inducntion が可能になる。 *)

  Definition f2cf (p : (nat * nat)) : (seq nat) := f2cf' p.1 p.2.
  Compute f2cf (36, 11).
  
  Fixpoint cf2f (sa : seq nat)  : (nat * nat) :=
    match sa with
    | a :: sa' =>
      let (p1, p2) := cf2f sa' in (a * p1 + p2, p1)
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
  Admitted.

(**
continuant polynomial

Concrete Mathematics
6.7 CONTINUANTS
では K_n(・) と表記されている。

平方根の連分数とペル方程式
有澤健治
https://leo.aichi-u.ac.jp/~keisoken/research/books/book51/book51.pdf
 *)

  Program Fixpoint GaussH' (s : seq nat) {measure (size s)} : nat :=
    match s with
    | [::] => 1
    | [:: n] => n
    | n0 :: n1 :: s' => n0 * GaussH' (n1 :: s') + GaussH' s'
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
  
(*
  letが入ると証明がむつかしくなる。
*)  
  Lemma cf2fE n sa :
    cf2f (n :: sa) =
    (let (p1, p2) := cf2f sa in (n * p1 + p2, p1)).
  Proof.
    simpl.
    done.
  Qed.

  Goal forall s, let: (n, _) := cf2f s in GaussH s = n.
  Proof.
    move=> s.
    functional induction (GaussH s).
    - done.
    - by rewrite /cf2f muln1 addn0.
    - admit.
  Admitted.
  
  
  Fixpoint cf2f' (sa : seq nat)  : (nat * nat) :=
    match sa with
    | a :: sa' => (a * (cf2f' sa').1 + (cf2f' sa').2, (cf2f' sa').1)
    | [::] => (1, 0)
    end.

  Compute cf2f' [:: 3; 3; 1; 2].             (* (36, 11) *)
  Compute cf2f' [:: 0; 1; 1; 1; 1; 1; 1].
  Compute cf2f' [:: 1; 2; 2; 2; 2; 2; 2].  
  
  Lemma cf2fE' n0 n1 s :
    (cf2f' [:: n0, n1 & s]).1 = n0 * (cf2f' (n1 :: s)).1 + (cf2f' s).1.
  Proof.
    done.
  Qed.
  
  Goal forall s, (cf2f' s).1 = GaussH s.
  Proof.
    move=> s.
    functional induction (GaussH s).
    - done.
    - by rewrite /cf2f' muln1 addn0.
    - rewrite -IHn -IHn0.
      rewrite -cf2fE'.
      done.
  Qed.

  Goal forall n s, (cf2f' (n :: s)).2 = GaussH s.
  Proof.
    move=> n s.
    functional induction (GaussH s).
    - done.
    - by rewrite /cf2f' muln1 addn0.
    - rewrite -IHn0 -IHn1.
      rewrite -cf2fE'.
      done.
  Qed.
  
(**
Concrete Mathematics, 6.7 CONTINUANTS (6.128)

黄金比はフィボナッチ数に等しい。
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

  Lemma GaussHE (n0 n1 : nat) (s : seq nat) :
    GaussH (n0 :: n1 :: s) = n0 * GaussH (n1 :: s) + GaussH s.
  Proof.
  Admitted.
  
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
  
  Compute GaussH [:: 1;2;3;4;5].            (* 225 *)
  Compute (GaussH [:: 1;2;3] * GaussH [:: 4;5]) + (GaussH [:: 1;2] * GaussH [:: 5]).
  (* 225 *)

  







  Goal forall s, GaussH s = GaussH (rev s).
  Proof.
    move=> s.
    functional induction (GaussH s).
    - done.
    - done.
    - admit.
  Admitted.

(**
cf2f (f2cf p) = p は証明できない（pが簡約される）ので、
f2cf (cf2f s) = s を証明する。
*)  
  Lemma f2cfE (n m : nat) : f2cf' n m = (n %/ m) :: f2cf' m (n %% m).
  Proof.
  Admitted.

  Lemma test1 n m r : (n * m + r) %/ m = n.
  Proof.
  Admitted.
  Lemma test2 n m r : (n * m + r) %% m = r.
  Proof.
  Admitted.
  
  Goal forall s, f2cf (cf2f' s) = s.
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

Extraction f2cf'.
(* 
let rec f2cf' n = function
| O -> Nil
| S n0 -> Cons ((divn n (S n0)), (f2cf' (S n0) (modn n (S n0))))
 *)

Extraction cf2f.
(* 
let rec cf2f = function
| Nil -> Pair ((S O), O)
| Cons (a, sa') -> let Pair (p1, p2) = cf2f sa' in Pair ((addn (muln a p1) p2), p1)
 *)

Extraction GaussH.
(* 
let rec gaussH = function
| Nil -> S O
| Cons (n0, l) ->
  (match l with
   | Nil -> n0
   | Cons (n1, s') -> addn (muln n0 (gaussH (Cons (n1, s')))) (gaussH s'))
 *)

(* END *)
