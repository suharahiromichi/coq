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
  
  (* ********* *)

  Lemma absz_total (i : int) : (i = `| i |%N%:Z) \/ (i = - `| i |%N%:Z).
  Proof.
    case: i => n.
    - by left.
    - rewrite /absz.
      right.
      by case: n.
  Qed.

  Lemma addzn1 (m : nat) : m%:Z + 1  = m.+1.
  Proof.
    rewrite -[m.+1]addn1.
    done.
  Qed.
  
  Lemma addzn2 (m : nat) : m%:Z + 2  = m.+2.
  Proof.
    rewrite -[m.+2]addn2.
    done.
  Qed.
  
  (* これは成り立たない。m = 0 なら -1 = 0 *)
  Lemma subzn1 (m : nat) : m%:Z - 1  = m.-1%:Z.
  Proof.
  Abort.
  
  Lemma double_half (m : nat) : m.*2./2 = m.
  Proof.
    elim: m => //= m IHm.
    by congr (_.+1).
  Qed.
  
  Lemma even_odd_total (n : nat) : n = n./2.*2 \/ n = n./2.*2.+1.
  Proof.
    elim: n => /=.
    - by left.
    - move=> n [IHe | IHo].
      * right.
        by rewrite 2!IHe uphalf_double.
      * left.
        rewrite {2}IHo /= double_half doubleS.
        by rewrite {1}IHo.
  Qed.
  
(**
# F_n  =   F_n     n は正
# F_-n = - F_n     n は偶数
# F_-n =   F_n     n は奇数
 *)
  
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

  Lemma fibn_n n : (fibn n + fibn n.+1)%N = fibn n.+2.
  Proof.
    done.
  Qed.

  Lemma fibz_i i : fibz i + fibz (i + 1) = fibz (i + 2).
  Proof.
    case: (absz_total i) => ->.
    - rewrite addzn1 addzn2.
      done.
    - case: (even_odd_total `|i|%N) => ->.
      + pose n := `|i|./2.
        rewrite -/n.
        (* fibz (- n.*2) + fibz (- n.*2 + 1) = fibz (- n.*2 + 2) *)
        case: n => //= n.
        (* fibz (- (n.+1).*2) + fibz (- (n.+1).*2 + 1) = fibz (- (n.+1).*2 + 2) *)
        (* -2n *)
        have -> : - n.+1.*2%:Z + 2 = - n.*2%:Z.
        {rewrite doubleS.
         rewrite addrC.
         rewrite -opprB.
         congr (- _).
         apply/eqP.
         rewrite subr_eq.
         rewrite -addzn2.             (* 整数の + 2 を .+2 にする。 *)
         done.
        }
        (* -(2n + 1) *)
        have -> : - n.+1.*2%:Z + 1 = - n.*2.+1%:Z.
        {rewrite -addzn1.
         rewrite doubleS.
         rewrite addrC.
         rewrite -opprB.
         congr (- _).
         rewrite -addzn2.
         rewrite -addrA.
         done.
        }
        (* -(2n + 2) *)
        
        (* fibz (- n+1.*2) + fibz (- n.*2.+1) = fibz (- n.*2) *)
        rewrite 2!fibz_neg_even_n.
        rewrite fibz_neg_odd_n.
        (* - fibn (n.+1).*2 + fibn n.*2.+1 = - fibn n.*2 *)
        have -> : n.+1.*2 = n.*2.+2 by done.
        (* - fibn n.*2.+2 + fibn n.*2.+1 = - fibn n.*2 *)
        apply/eqP.
        Check addr_eq0 : forall [V : zmodType] (x y : V), (x + y == 0) = (x == - y).
        Check subr_eq0 : forall (V : zmodType) (x y : V), (x - y == 0) = (x == y).
        Check subr_eq : forall (V : zmodType) (x y z : V), (x - z == y) = (x == y + z).
        rewrite -addr_eq0.
        rewrite -addrA.
        rewrite -addrC.
        rewrite subr_eq.
        rewrite add0r.
        rewrite addrC.
        (* fibn n.*2 + fibn n.*2.+1 = fibn n.*2.+2 *)        
        done.
      + pose n := `|i|./2.
        rewrite -/n.
        (* fibz (- n.*2.+1) + fibz (- n.*2.+1 + 1) = fibz (- n.*2.+1 + 2) *)
        case: n => //= n.
        (* fibz (- (n.+1).*2.+1) + fibz (- (n.+1).*2.+1 + 1) = fibz (- (n.+1).*2.+1 + 2) *)
        (* -(2n + 1) *)
        have -> : - n.+1.*2.+1%:Z + 2 = - n.*2.+1%:Z.
        {rewrite doubleS.
         rewrite addrC.
         rewrite -opprB.
         congr (- _).
        }
        (* -(2n + 2) *)
        have -> : - n.+1.*2.+1%:Z + 1 = - n.+1.*2%:Z.
        {rewrite doubleS.
         rewrite addrC.
         rewrite -opprB.
         congr (- _).
         }
        (* -(2n + 3) *)
        rewrite fibz_neg_even_n.
        rewrite 2!fibz_neg_odd_n.
        have -> : n.+1.*2.+1 = n.*2.+3 by done.
        have -> : n.+1.*2 = n.*2.+2 by done.
        (* fibn n.*2.+3 - fibn n.*2.+2 = fibn n.*2.+1 *)
        apply/eqP.
        rewrite subr_eq.
        (* fibn n.*2.+3 == fibn n.*2.+1 + fibn n.*2.+2 *)
        done.
  Qed.
  
End INTFIB.

(* *************** *)
(* *************** *)
(* *************** *)


Check eqz_nat : forall m n : nat, (m == n :> int) = (m == n).

(* END *)

