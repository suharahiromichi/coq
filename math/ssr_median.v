(**
多数決関数とfull adder
========================

@suharahiromichi

2020/04/30
 *)

From mathcomp Require Import all_ssreflect.
Require Import ssr_omega.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
(* Set Print All. *)

Section Majority.

  Definition maj3 (b c d : bool) : bool := if (b + c + d <= 1) then false else true.

  Definition maj3_0 (a b c : bool) : bool :=
    a && b && ~~c || ~~a && b && c || a && ~~b && c || a && b && c.
  Definition maj3_1 (a b c : bool) : bool := a && b || b && c || c && a.
  Definition maj3_2 (a b c : bool) : bool := a * b + b * c + c * a != 0.
  
  Goal forall (a b c : bool), maj3_0 a b c = maj3_1 a b c.
  Proof.
    move=> a b c.
    rewrite /maj3_0 /maj3_1.
    
    rewrite [_ || a && b && c]orbC !orbA.   (* 先頭に移動する。 *)
    rewrite -[a && b && c]Bool.orb_diag.    (* 項を複製する。 *)
    rewrite -{1}[a && b && c]Bool.orb_diag. (* 項を複製する。 *)
    rewrite [_ || a && ~~b && c]orbC !orbA. (* 先頭に移動する。 *)
    have -> : a && ~~b && c || a && b && c = a && c.
      (* 一旦右結合にして、~~bとbを末尾にして、左結合に戻す。 *)
      by rewrite -!andbA [~~b && _]andbC [b && _]andbC ?andbA
         -andb_orr orbC orbN andbT andbC.
    rewrite [a && c]andbC.
    
    rewrite [_ || a && b && c]orbC !orbA.   (* 先頭に移動する。 *)
    rewrite [_ || ~~a && b && c]orbC !orbA. (* 先頭に移動する。 *)
    have -> : ~~ a && b && c || a && b && c = b && c.
      (* 一旦右結合にして、~~aとaを末尾にして、左結合に戻す。 *)
      by rewrite -!andbA [~~a && _]andbC [a && _]andbC ?andbA
         -andb_orr orbC orbN andbT andbC.
      
    rewrite [_ || a && b && c]orbC !orbA.   (* 先頭に移動する。 *)
    rewrite [_ || a && b && ~~c]orbC !orbA. (* 先頭に移動する。 *)
    have -> : a && b && ~~c || a && b && c = a && b
      (* すでに、~~cとcは末尾にある。 *)
      by rewrite -andb_orr orbC orbN andbT andbC.                                             done.
  Qed.

  Lemma test2 (a b :nat) : (a + b != 0) = (a != 0) || (b != 0).
  Proof.
      by elim: a; elim: b.
  Qed.
  
  Lemma test a : (nat_of_bool a != 0) = a.
  Proof.
    by case: a.
  Qed.
  
  Goal forall (a b c : bool), maj3_1 a b c = maj3_2 a b c.
  Proof.
    move=> a b c.
    rewrite /maj3_1 /maj3_2.
    rewrite !mulnb.
    rewrite 2!test2.
    rewrite 3!test.
    done.
  Qed.
  
  Goal forall (a b c : bool), maj3 a b c = maj3_1 a b c.
  Proof.
      by case; case; case.
  Qed.

End Majority.

Section Median.
  
  (* 5回比較するので、効率悪い *)
  Definition median (m n p : nat) := maxn (maxn (minn m n) (minn n p)) (minn p m).
  
  (* 展開したバブルソート *)
  Definition median' (n1 n2 n3 : nat) :=
    let (n1', n2') := if n1 < n2 then (n1, n2) else (n2, n1) in
    let (n2'', n3') := if n2' < n3 then (n2', n3) else (n3, n2') in
    let (n1'', n2''') := if (n1' < n2'') then (n1', n2'') else (n2'', n1') in n2'''.
  
  (* 上記をswapなしにしたもの *)
  Definition median'' (m n p : nat) :=
    if m < n then
      if n < p then n else (if m < p then p else m)
    else
      if m < p then m else (if n < p then p else n).
  
  Goal forall (a b c : bool), median a b c = maj3 a b c.
  Proof.
      by case; case; case.
  Qed.

  Goal forall (a b c : bool), median a b c = median' a b c.
  Proof.
    rewrite /median /median'.
      by case; case; case.
  Qed.
  
  Goal forall (a b c : bool), median a b c = median'' a b c.
  Proof.
    rewrite /median /median'.
      by case; case; case.
  Qed.
  
  (* nat *)
  
  Goal forall (m n p : nat), median' m n p = median'' m n p.
  Proof.
    move=> m n p.
    rewrite /median' /median''.
    case: ifP => Hmn; case: ifP => Hnp; case: ifP => Hpm; ssromega.
  Qed.
  
  Goal forall (m n p : nat), median m n p = median'' m n p.
  Proof.
    move=> m n p.
    rewrite /median /median'' /maxn /minn.
    case Hmn : (m < n); case Hnp : (n < p); case Hpm : (p < m);
      case Hmp : (m < p); case Hnm : (n < m);
        case Hpp : (p < p); case Hnn : (n < n); case Hmm : (m < m);
        rewrite ?Hmn ?Hnp ?Hpm ?Hmp ?Hnm ?Hpp ?Hnn; ssromega.
  Qed.
  
  Goal forall (m n p : nat), median m n p = median' m n p.
  Proof.
    move=> m n p.
    rewrite /median /median' /maxn /minn.
    case Hmn : (m < n); case Hnp : (n < p); case Hpm : (p < m);
      case Hmp : (m < p); case Hnm : (n < m);
        case Hpp : (p < p); case Hnn : (n < n); case Hmm : (m < m);
        rewrite ?Hmn ?Hnp ?Hpm ?Hmp ?Hnm ?Hpp ?Hnn; ssromega.
  Qed.
  
End Median.


Section FullAdder.

  (* majority3 *)
  Definition maj (a b c : bool) : bool := (2 <= a + b + c).
  
  (* parity3 *)
  Definition par (a b c : bool) : bool := odd (a + b + c).

  
  Compute maj false false false.             (* false *)
  Compute maj true false false.              (* false *)
  Compute maj true false true.               (* true *)
  Compute maj true true true.                (* true *)

  Compute par false false false.             (* false *)
  Compute par true false false.              (* true *)
  Compute par true false true.               (* false *)
  Compute par true true true.                (* true *)  

  Goal forall (a b c : bool),
      a + b + c = 2 * maj a b c + par a b c.
  Proof.
      by case; case; case.
  Qed.

End FullAdder.


(* おまけ *)

Goal forall (a b c : bool), maj3 a b c = maj a b c.
Proof.
    by case; case; case.
Qed.

(* END *)
