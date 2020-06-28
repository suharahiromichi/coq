From mathcomp Require Import all_ssreflect.
Require Import ssromega.
Require Import Recdef.                      (* Function *)
Require Import Wf_nat.                      (* wf *)
Require Import Program.Wf.                  (* Program wf *)

Require Import ssr_multiset_coefficient.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
(* Set Print All. *)

(**
# Catalan Number カタラン数
*)

Section DEFINE.

  Definition catalan n := 'C(n.*2, n) %/ n.+1.
  
  Compute catalan 0.                          (* 1 *)
  Compute catalan 1.                          (* 1 *)
  Compute catalan 2.                          (* 2 *)
  Compute catalan 3.                          (* 5 *)
  
  Fixpoint catalan_rec n {struct n} :=
    match n with
    | 0 => 1
    | n'.+1 => \sum_(0 <= i < n'.+1)(catalan_rec (n' - (i + n')) * catalan_rec (n' - i))
    end.
  
  Compute catalan_rec 0.
  Compute catalan_rec 1.
  Compute catalan_rec 2.

End DEFINE.

Section LEMMAS.

  Lemma test n : 0 < n -> 0 < n.*2.
  Proof.
    by rewrite double_gt0.
  Qed.
  
  Lemma test2 n : n.*2 - n = n.
  Proof.
    rewrite -addnn.
    ssromega.
  Qed.
  
  Check factS : forall n : nat, n.+1`! = n.+1 * n`!.
  Lemma test3 n : 0 < n -> n`! = n * n.-1`!.
  Proof.
    move=> H.
    have Hf :(n.-1.+1)`! = n.-1.+1 * (n.-1)`! by apply: factS.
    rewrite prednK in Hf; last done.
    done.
  Qed.
  
  Lemma test4 n : n.*2 - n.+1 = n.-1.
  Proof.
    rewrite -addnn.
    ssromega.
  Qed.
  
  Lemma test5 n : 0 < n -> (n * n.-1`! * n`!) %| n.*2`!.
  Proof.
    move=> H.
    rewrite -test3; last done.
    rewrite -addnn.
      by rewrite divn_fact_mul_add_fact.
  Qed.

  Lemma test0 n m p : n + m = p -> n`! * m`! %| p`!.
  Proof.
    move=> <-.
    by apply: divn_fact_mul_add_fact.
  Qed.
  
  Lemma test6 n : 0 < n -> n.+1 * n`! * n.-1`! %| n.*2`!.
  Proof.
    move=> H.
    rewrite -[n.+1 * n`!]test3; last done.
    apply: test0.
    rewrite -subn1.
    rewrite addnBA; last done.
    rewrite -addn1.
    rewrite -addnAC.
    rewrite addn1.
    rewrite subn1.
    Search _.+1.-1.
    rewrite -[(n + n).+1.-1]pred_Sn.
    rewrite addnn.
    done.
  Qed.

(**
カタラン数の定義 : ``c_n = (1 / (n + 1)) * 'C(2*n, n)`` に対して、
   
```c_n = 'C(2*n, n) - 'C(2*n, n - 1)```

が成り立つ。ここで 'C(n, m) は二項係数 nCm。

```(1/(n+1)) * 'C(2*n, n) = 'C(2*n, n) - 'C(2*n, n - 1)```

を変形した、

```n * 'C(n*2, n) = (n+1) * 'C(n*2, n+1)```

を証明する。
*)  

  
(**
方針
左辺と右辺それぞれに、
*)
    Check muln_divA : forall d m n : nat, d %| n -> m * (n %/ d) = (m * n) %/ d.
(**
で、(N * X) %/ (N * Y) のかたちにする。
*)    
    Check divnMl : forall p m d : nat, 0 < p -> (p * m) %/ (p * d) = m %/ d.
(**
で、それを消す。
*)    

  Goal forall n, 0 < n -> n * 'C(n.*2, n) = n.+1 * 'C(n.*2, n.+1).
  Proof.
    move=> n Hn.

    (* LHS *)
    rewrite bin_factd; last by rewrite test.
    rewrite test2.
    rewrite {1}[in n`! * n`!]test3; last done.
    (* (n * X) %/ (n * Y) にする。 *)
    rewrite muln_divA; last by rewrite test5.
    rewrite -mulnA divnMl; last done.
    rewrite [(n.-1)`! * n`!]mulnC.
    
    (* RHS *)
    rewrite bin_factd; last by rewrite test.
    rewrite test4.
    rewrite factS.
    (* (n.+1 * X) %/ (n.+1 * Y) にする。 *)
    rewrite muln_divA; last by rewrite test6.
    rewrite -mulnA divnMl; last done.
    
    done.
  Qed.

End LEMMAS.
  
(* END *)
