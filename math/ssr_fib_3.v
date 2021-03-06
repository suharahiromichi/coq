From mathcomp Require Import all_ssreflect.
Require Import ssromega.
Require Import FunInd.                      (* Functional Scheme *)
Require Import Recdef.                      (* Function *)
Require Import Wf_nat.                      (* wf *)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
(* Set Print All. *)

Section Fib3.

  Function fib (n : nat) : nat :=
    match n with
    | 0 => 0
    | 1 => 1
    | (m.+1 as pn).+1 => fib m + fib pn (* fib n.-2 + fib n.-1 *)
    end.
  
  Fail Functional Scheme gcdn_ind := Induction for gcdn Sort Prop.
  (* Error: A fixpoint needs at least one parameter. *)
  
  Function gcd (m n : nat) {wf lt m} : nat :=
    match m with
    | 0 => n
    | _ => gcd (n %% m) m
    end.
  Proof.
    - move=> m n m0 _.
      apply/ltP.
        by rewrite ltn_mod.
    - by apply: lt_wf.
  Qed.
  Check gcd_ind
    : forall P : nat -> nat -> nat -> Prop,
      (forall m n : nat, m = 0 -> P 0 n n) ->
      (forall m n _x : nat,
          m = _x ->
          match _x with
          | 0 => False
          | _.+1 => True
          end -> P (n %% m) m (gcd (n %% m) m) -> P _x n (gcd (n %% m) m)) ->
      forall m n : nat, P m n (gcd m n).
  
  (* GCDの補題 *)
  Lemma gcdnE m n : gcd m n = gcd (n %% m) m.
  Proof.
    Check gcdn_modl m n : gcdn (m %% n) n = gcdn m n.
  Admitted.
  
  Lemma gcdnC m n : gcd m n = gcd n m.
    Check gcdnC m n : gcdn m n = gcdn n m.
  Admitted.

  Lemma gcdnn m : gcd m m = m.
    Check gcdnn m : gcdn m m = m.
  Admitted.

  Lemma gcdn0 m : gcd m 0 = m.
    Check gcdn0 m : gcdn m 0 = m.
  Admitted.
  
  (* 補題 *)
  Lemma lemma912 m n :
    1 <= m ->
    1 <= n ->
    m <= n ->
    gcd (fib m) (fib n) = gcd (fib (n %% m)) (fib m).
    (* see. ssr_fib_2.v *)
  Admitted.

  (* 消すな *)
  Lemma leq_mod n x : 0 < x -> n %% x <= x.
  Proof.
    move=> Hx.
    rewrite leq_eqVlt.
    apply/orP/or_intror.
      by rewrite ltn_mod.
  Qed.
  
(*
m <= n としても一般性を失わない。
m = n は自明だが、lemma912 で必要なので残しておく。
*)
  Compute gcdn 0 0.                         (* 0 *)
  Compute fib 0.                            (* 0 *)

  Lemma lemma9 (m n : nat) :
    1 <= m ->
    1 <= n ->
    m <= n ->    
    (gcd (fib m) (fib n) = fib (gcd m n)).
  Proof.
    move=> Hm Hn Hmn.
    rewrite lemma912.
    - rewrite [gcd m n]gcdnE.
      functional induction (gcd m n).
      + done.                               (* Hm の矛盾 *)
      + rewrite lemma912.
        * rewrite [gcd (n %% _x) _x]gcdnE.
          apply: IHn0.
        
          ** (* 0 < n %% _x *)
            (* ゴールの 1 <= m のが反映される。 *)
            admit.                          (* 754 *)
          
          ** (* 0 < _x *)
            done.
          ** (* n %% _x < x *)
            by rewrite leq_mod.

        * (* 0 < n %% _x *)
          admit.                 (* 733 *)
        (* lemma912 の 1 <= m に由来する。 *)
      
        * (* 0 < _x *)
          ssromega.
        * (* n %% _x <= _x *)
            by rewrite leq_mod.

    - (* 0 < m *)
      ssromega.
    - (* 0 < n *)
      ssromega.
    - (* m < n *)
      done.
  Admitted.

(* ******************** *)
(* 条件をはずしてみる。 *)
(* ******************** *)
  
  Lemma lemma912' m n :
    gcd (fib m) (fib n) = gcd (fib (n %% m)) (fib m).
    (* see. ssr_fib_2.v *)
  Admitted.
  
  Lemma lemma9' (m n : nat) :
    (gcd (fib m) (fib n) = fib (gcd m n)).
  Proof.
    rewrite lemma912'.
    - rewrite [gcd m n]gcdnE.
      functional induction (gcd m n).
      + rewrite modn0 /=.
        by rewrite 2!gcdn0.
        
      + rewrite lemma912.
        * rewrite [gcd (n %% _) _]gcdnE.
            by apply: IHn0.
          
        * (* 0 < n %% m *)
          admit.
          
        * (* 0 < m *)
          admit.

        * (* n %% m <= m *)
          (* 0 %% 0 = 0 なので、どちらかは 1以上であること。 *)
          admit.
  Admitted.

End Fib3.

(* END *)
