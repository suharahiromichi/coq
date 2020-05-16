(**
フィボナッチ数列についての定理の証明

フィボナッチ数列と中学入試問題
http://www.suguru.jp/Fibonacci/
*)

From mathcomp Require Import all_ssreflect.
Require Import ssromega.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(**
ffibonacci
 *)

Section Fib_1.

(**
# fibonacci 関数の定義
*)
  Fixpoint fib (n : nat) : nat :=
    match n with
    | 0 => 0
    | 1 => 1
    | (ppn.+1 as pn).+1 => fib ppn + fib pn (* fib n.-2 + fib n.-1 *)
    end.

(**
# 定理

## 性質１  
 *)

  Lemma l1_sub1 (n : nat) :
    \sum_(0 <= i < n)(fib i) + \sum_(0 <= i < n)(fib i.+1) =
    \sum_(0 <= i < n)(fib i.+2).
  Proof.
    rewrite -big_split.
    (* Σf + Σg = Σ(f + g) *)
    (* https://staff.aist.go.jp/reynald.affeldt/ssrcoq/bigop_doc.pdf *)
    done.
  Qed.

  Lemma l1_sub2' (n : nat) :
    1 <= n -> \sum_(1 <= i < n.+1)(fib i) = fib 1 + \sum_(1 <= i < n)(fib i.+1).
  Proof.
    move=> H.
    rewrite -big_nat_recl; last done.
    done.
  Qed.

  Lemma test : fib 1 = \sum_(0 <= i < 1)(fib i.+1).
  Proof.
      by rewrite big_cons big_nil.
  Qed.
  
  Lemma test0 : \sum_(0 <= i < 1)(fib i) = 0.
  Proof.
      by rewrite big_cons big_nil.
  Qed.
  
  Lemma test1 (n : nat) : 1 <= n -> index_iota 0 1 ++ index_iota 1 n = index_iota 0 n.
  Proof.
    move=> Hn.
    rewrite /index_iota.
    rewrite -iota_add.
    rewrite !subn0.
    rewrite subnKC //=.
  Qed.

  Lemma test21 (n : nat) : 1 <= n -> index_iota 1 2 ++ index_iota 2 n.+1 =
                                     index_iota 1 n.+1.
  Proof.
    move=> Hn.
    rewrite /index_iota.
    rewrite -iota_add.
  Admitted.
  
  Lemma test2 (n : nat) :
    1 <= n ->
    \sum_(0 <= i < 1)(fib i.+1) + \sum_(1 <= i < n)(fib i.+1) =
    \sum_(0 <= i < n)(fib i.+1).
  Proof.
    move=> Hn.
      by rewrite -big_cat test1.
  Qed.
  
  Lemma l1_sub2 (n : nat) :
    1 <= n -> \sum_(1 <= i < n.+1)(fib i) = \sum_(0 <= i < n)(fib i.+1).
  Proof.
    move=> H.
    rewrite big_nat_recl; last done.
      by rewrite test test2.
  Qed.

  Lemma test22' : fib 2 = \sum_(1 <= i < 2)(fib i.+1).
  Proof.
      by rewrite big_cons big_nil.
  Qed.

  Lemma test22 (n : nat) :
    1 <= n ->
    \sum_(1 <= i < 2)(fib i.+1) + \sum_(2 <= i < n.+1)(fib i.+1) =
    \sum_(0 <= i < n)(fib i.+2).
  Proof.
    move=> Hn.
    rewrite -big_cat.
    rewrite test21.
    rewrite big_nat_recl; last done.
  Admitted.


  Lemma l1_sub22 (n : nat) :
    1 <= n -> \sum_(2 <= i < n.+2)(fib i) = \sum_(0 <= i < n)(fib i.+2).
  Proof.
    move=> H.
    rewrite big_nat_recl; last done.
    rewrite test22'.
    rewrite test22.
    done.
    done.
  Qed.
  
  Lemma test100 n : \sum_(1 <= i < n.+1)(fib i) = fib 1 + \sum_(2 <= i < n.+1)(fib i).
  Proof.
  Admitted.

  Lemma test101 n : \sum_(2 <= i < n.+2) fib i = \sum_(2 <= i < n.+1)(fib i) + fib n.+2.
  Proof.
  Admitted.
  
  Lemma test102 m n k : m + k = n + k -> m = n.
  Proof.
  Admitted.

  Lemma lemma1 (n : nat) :
    1 <= n -> \sum_(0 <= i < n)(fib i) = fib n.+2 - 1.
  Proof.  
    move=> Hn.
    have H := l1_sub1 n.
    rewrite -l1_sub2 in H; last done.
    rewrite -l1_sub22 in H; last done.
    rewrite test100 test101 in H.
    rewrite addnA in H.
    rewrite [\sum_(2 <= i < n.+1) fib i + fib n.+2]addnC in H.
    move/test102 in H.
    rewrite -H.
    rewrite [fib 1]/=.
    rewrite addn1 subn1 succnK.
    done.
  Qed.
  
End Fib_1.

(* END *)








  Lemma l1_sub2' (n : nat) :
    1 <= n -> fib 1 + \sum_(1 <= i < n)(fib i.+1) = \sum_(1 <= i < n.+1) fib i.
  Proof.
    move=> H.
    Check (big_nat_recl n 1 _ H).
    rewrite -big_nat_recl; last done.
    

  Lemma l1_sub2' (n : nat) :
    1 <= n -> \sum_(1 <= i < n.+1)(fib i) = \sum_(0 <= i < n)(fib i.+1).
  Proof.
    move=> H.
    Check (big_nat_recl n 1 _ H).
    rewrite big_nat_recl; last done.
    

    Admitted.
    














    


  Lemma fib_0 n : fib 0 * fib n = 0.
  Proof.
      by rewrite mul0n.
  Qed.
  
  Lemma fib_1 n : fib 1 * fib n = fib n.
  Proof.
      by rewrite mul1n.
  Qed.
        
  Lemma fib_2 n : fib 2 * fib n = fib n.
  Proof.
      by rewrite mul1n.
  Qed.

  Lemma fib_n n : fib n.+2 = fib n + fib n.+1.
  Proof.
    done.
  Qed.

End Fibonacci.

(* END *)



(**
# 参考

SFの古い版にあった even の証明に使う帰納法の例。
*)
  Definition nat_ind2 :
    forall (P : nat -> Prop),
    P 0 ->
    P 1 ->
    (forall n : nat, P n -> P n.+2) ->
    forall n : nat , P n :=
       fun P => fun P0 => fun P1 => fun PSS =>
          fix f (n : nat) := match n return P n with
                             0 => P0
                           | 1 => P1
                           | n'.+2 => PSS n' (f n')
                           end.
  
  Check nat_ind2
    : forall P : nat -> Prop,
      P 0 ->
      P 1 ->
      (forall n : nat, P n -> P n.+2) ->
      forall n : nat, P n.

(**
# fib の証明に使う帰納法

公理として与える。修正すること。
*)
  Axiom nat_fib_ind : forall P : nat -> Prop,
      P 0 ->
      P 1 ->
      (forall n : nat, P n -> P n.+1 -> P n.+2) ->
      forall n : nat, P n.




  保存版



    Lemma l1_sub2 (n : nat) :
    \sum_(0 <= i < n)(fib i.+1) = \sum_(1 <= i < n)(fib i.+1).
  Proof.
    have H : 0 <= n by rewrite leq0n.
    Check (big_nat_recl n 0 _ H).
    rewrite big_nat_recl; last done.
      by rewrite add0n.
  Qed.




    Lemma l1_sub2' (n : nat) :
    \sum_(0 <= i < n.+1)(fib i) = \sum_(0 <= i < n)(fib i.+1).
  Proof.
    have H : 0 <= n by rewrite leq0n.
    Check (big_nat_recl n 0 _ H).
    rewrite big_nat_recl; last done.
      by rewrite add0n.
  Qed.

  Lemma l1_sub3 (n : nat) :
    \sum_(0 <= i < n.+1)(fib i.+1) = 1 + \sum_(0 <= i < n)(fib i.+2).
  Proof.
    have H : 0 <= n.+1 by rewrite leq0n.
    Check (big_nat_recl n 0 _ H).
    rewrite big_nat_recl; last done.
      by rewrite [fib 1]/=.
  Qed.
  
  Lemma test : fib 1 = \sum_(0 <= i < 1)(fib i.+1).
  Proof.
    rewrite big_cons.
    rewrite big_nil.
    done.
  Qed.