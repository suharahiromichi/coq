(*
コンピュータの数学 6.6

整数（負数）のフィボナッチ数
 *)
From mathcomp Require Import all_ssreflect.
From mathcomp Require Import all_algebra.

Import GRing.Theory.         (* mulrA などを使えるようにする。 *)
Import Num.Theory.           (* unitf_gt0 などを使えるようにする。 *)
Import intZmod.              (* addz など *)
Import intRing.              (* mulz など *)
Open Scope ring_scope.       (* 環の四則演算を使えるようにする。 *)


Section INTFIB.

  Fixpoint fibn (n : nat) : nat :=
    match n with
    | 0 => 0
    | 1 => 1
    | (m.+1 as pn).+1 => fibn m + fibn pn (* fibn n.-2 + fibn n.-1 *)
    end.

(*
  Definition fibz (i : int) : int :=
    match i with
    | Posz n => fibn n
    | Negz n => (-1)^n * (fibn n.+1)%:Z
    end.
*)
  Definition fibz (i : int) : int :=
    let n := `|i|%N in
    if 0 <= i then (fibn n)%:Z
    else (-1)^n.-1 * (fibn n)%:Z.
  
  Lemma expr_1_even (n : nat) : (-1) ^ n.*2%N = 1%:Z.
  Proof.
    rewrite -muln2.
    rewrite -exprnP exprM.
    rewrite sqrr_sign.
    done.
  Qed.
  
  Lemma expr_1_odd (n : nat) : (-1) ^ n.*2.+1%N = -1%:Z.
  Proof.
    rewrite -muln2 -addn1.
    rewrite -exprnP exprD exprM.
    rewrite sqrr_sign mul1r expr1.
    done.
  Qed.
  
(**
``n`` 正数
 *)
  Lemma fibz_pos_n (n : nat) : fibz n%:Z = fibn n.
  Proof.
    done.
  Qed.
  
(**
``-(2n + 1)`` 負の奇数 その1
 *)
  Lemma fibz_neg_odd_n (n : nat) : fibz (- n.*2.+1%:Z) = fibn n.*2.+1.
  Proof.
    rewrite /fibz.
    have -> : 0 <= - n.*2.+1%:Z = false by done.
    have -> : `|- n.*2.+1%:Z|%N = n.*2.+1 by done.
    rewrite -pred_Sn.
    rewrite expr_1_even mul1r.
    done.
  Qed.
  
  Lemma fibz_neg_odd_z (n : nat) : fibz (- n.*2.+1%:Z) = fibz n.*2.+1%:Z.
  Proof.
    rewrite fibz_neg_odd_n.
    rewrite /fibz.
    have -> : 0 <= n.*2.+1%:Z = true by done.
    have -> : `|n.*2.+1|%N = n.*2.+1 by done.
    done.
  Qed.
  
(**
``-(2n - 1)`` 負の奇数 その2
 *)
  Lemma fibz_neg_odd'_n (n : nat) : fibz (- n.*2.-1%:Z) = fibn n.*2.-1.
  Proof.
    case: n => // n.                        (* n = 0 の場合 *)
    have -> : - n.+1.*2.-1%:Z = - n.*2.+1%:Z by done.
    have -> : n.+1.*2.-1 = n.*2.+1 by done.
    rewrite fibz_neg_odd_n.
    done.
  Qed.  

  Lemma fibz_neg_odd'_z (n : nat) : fibz (- n.*2.-1%:Z) = fibz n.*2.-1%:Z.
  Proof.
    case: n => // n.                        (* n = 0 の場合 *)
    have -> : - n.+1.*2.-1%:Z = - n.*2.+1%:Z by done.
    have -> : n.+1.*2.-1 = n.*2.+1 by done.
    rewrite fibz_neg_odd_z.
    done.
  Qed.
  
(**
``-2n`` 負の偶数
 *)
  Lemma fibz_neg_even' (n : nat) : fibz (- n.*2.+2%:Z) = - (fibn n.*2.+2)%:Z.
  Proof.
    rewrite /fibz.
    have -> : 0 <= - n.*2.+2%:Z = false by done.
    have -> : `|- n.*2.+2%:Z|%N.-1 = n.*2.+1 by done.
    rewrite expr_1_odd mulN1r.
    done.
  Qed.
  
  Lemma fibz_neg_even_n (n : nat) : fibz (- n.*2%:Z) = - (fibn n.*2)%:Z.
  Proof.
    case: n => // n.                        (* n = 0 の場合 *)
    have -> : n.+1.*2 = n.*2.+2 by done.
    by rewrite fibz_neg_even'.
  Qed.
  
  Lemma fibz_neg_even_z (n : nat) : fibz (- n.*2%:Z) = - (fibz n.*2).
  Proof.
    rewrite fibz_neg_even_n.
    rewrite /fibz.
    have -> : 0 <= n.*2%:Z = true by done.
    have -> : `|n.*2%:Z|%N = n.*2 by done.
    done.
  Qed.

End INTFIB.  








  Lemma fibn_n n : (fibn n + fibn n.+1)%N = fibn n.+2.
  Proof.
    done.
  Qed.

  
  Variant case_of_int : int -> Prop :=
    | c_pos : forall (n : nat), case_of_int n
    | c_zero : case_of_int 0
    | c_neg_odd : forall (n : nat), case_of_int (- n.*2.+1%:Z)
    | c_neg_even : forall (n : nat), case_of_int (- n.*2.+2%:Z).

  Lemma fibz_i i : case_of_int i -> fibz i + fibz (i + 1) = fibz (i + 2).
  Proof.
    case.
    - move=> n.
      rewrite 3!fibz_pos.
      rewrite addn1 addn2.
      apply/eqP.
      rewrite eqz_nat.
      apply/eqP.
      by rewrite fibn_n.
    - rewrite 2!add0r.
      by rewrite fibz_2.
    - move=> n.
      rewrite fibz_neg_odd'.
      have -> : (- n.*2.+1%:Z + 1) = - n.*2%:Z by admit.
      rewrite fibz_neg_even'.
      have -> : (- n.*2.+1%:Z + 2) = - n.*2.-1%:Z by admit.
      


End FIB.

(* *************** *)
(* *************** *)
(* *************** *)
(* *************** *)
(* *************** *)
(* *************** *)


  Lemma fibn_ind (P : nat -> nat -> Prop) :
    P 0%N 0%N ->
    P 1%N 1%N ->
    (forall m : nat, P m (fibn m) ->
                     P m.+1 (fibn m.+1) ->
                     P m.+2 (fibn m + fibn m.+1))%N
    ->
      forall m : nat, P m (fibn m).
  Proof.
    move=> H1 H2 IH.
    (* m について2回場合分して、m.+2 を取り出す。 *)
    elim/ltn_ind => [[_ | [_ | m]]].
    - by rewrite /fibn.
    - by rewrite /fibn.
    - move: (IH m).
      rewrite -fibn_n => {IH} IH H.
      by apply: IH; apply: H.
  Qed.

  Definition Pfibn m0 n0 :=
    forall n, fibn (n + m0.+1) = (fibn m0.+1 * fibn n.+1 + n0 * fibn n)%N.
  
  Definition fibz (i : int) : int :=
    match i with
    | Posz n => fibn n
    | Negz n => (-1)^n * (fibn n.+1)%:Z
    end.
  
  Compute fibz 0.                           (* 0 *)
  Compute fibz (-1%:Z).                     (* 1 *)
  Compute fibz (-2%:Z).                     (* Negz 0 *)
  Compute fibz (-3%:Z).                     (* 2 *)
  
  Lemma fibz_i (i : int) : fibz i + fibz (i + 1) = fibz (i + 2).
  Proof.
    case: i => n.
    - by rewrite /= addn1 addn2.
    - Admitted.


  Lemma fibz_i' (i : int) : fibz (oppz (i + 2)) + fibz (oppz (i + 1)) = fibz i.
  Proof.
    case: i => n.
    - admit.
    - rewrite /fibz.
      have -> : Negz n + 2 = Negz (n.-2) by admit.
      have -> : Negz n + 1 = Negz (n.-1) by admit.
      simpl.
  
    - 
      case H1 : (Negz n + 1); case H2 : (Negz n + 2).
      + elim: n H1 H2 => //= IH1n IH2n.
        rewrite expr0z.
        admit.                              (* 1 + fib 0 = fib 1 *)
      + by elim: n H1 H2 => //= IH1n IH2n.
      + admit.
      + elim: n H1 H2 => // n IHn H1 H2.
        
      have -> : oppz n.+1 + 1 = oppz n by admit.
      have -> : oppz n.+1 + 2 = oppz n.-1 by admit.
      
      Search _ (oppz _).

elim: n => // n IHn.
      Search _ (Negz _).
      
      rewrite !NegzE in IHn.
      

      Print oppz.
      Search _ (oppz _).

  Definition test (i : int) : nat :=
    match i with
    | Posz n => n
    | Negz n => n.+1                       (* 2の補数なので+1する。 *)
    end.
  Compute test 0.
  Compute test (-1)%Z.                      (* 1 *)
  Compute test (-2%:Z).                     (* 2 *)
  Compute test (-3%:Z).                     (* 3 *)
  

(*
  NG.
  Definition fibz' (i : int) : int :=
    let: n := `|i|%N in (-1)^(n.-1) * (fibn n)%:Z.

  Compute fibz' 0.                          (* 0 *)
  Compute fibz' (-1%:Z).                    (* 1 *)
  Compute fibz' (-2%:Z).                    (* Negz 0 *)
  Compute fibz' (-3%:Z).                    (* 2 *)
 *)
  

      Search (_ %N + _ %N).

      elim=> // n IHn.
      + rewrite /fibn.


rewrite /= expr0z add0n.
        rewrite expr1z.
        Search _ (_ ^ 1).
        
        Search _ ( _ ^ 0).
        rewrite mulz0.
        
      + rewrite sub0n.



  Lemma fibz_i (i : int) : fibz i + fibz (i + 1) = fibz (i + 2).
  Proof.
    case: i => n.
    - rewrite /fibz.
      
    
