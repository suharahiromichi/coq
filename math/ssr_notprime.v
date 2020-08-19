From mathcomp Require Import all_ssreflect.
From mathcomp Require Import bigop matrix.
Require Import ssromega.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(**
# 問題 - nが素数でない（合成数である）とき、2^n-1 も素数ではない（合成数である）。

Daniel J. Velleman, Amherst College, Massachusetts, "How To Prove it" 

証明の大筋はこの本の Introduction (p.3) からとりました。
以下から当該ページを含む前半が読めます。

https://www.cambridge.org/jp/academic/subjects/mathematics/logic-categories-and-sets/how-prove-it-structured-approach-3rd-edition?format=HB&isbn=9781108424189

 *)

(**
# 総和の補題
*)
Section Summation1.
  
  Lemma sum_distrr m n c a :
    m < n ->
    \sum_(m <= i < n)(c * (a i)) = c * (\sum_(m <= i < n)(a i)).
  Proof. by rewrite big_distrr. Qed.

  Lemma eq_sum m n a b : a =1 b ->
                         \sum_(m <= i < n)(a i) = \sum_(m <= i < n)(b i).
  Proof.
    move=> Hab.                             (* =1 は第1階の=です。 *)
    apply: eq_big_nat => i Hmn.
      by rewrite Hab.
  Qed.

  Lemma sum_add1 n a :
    \sum_(1 <= i < n.+1)(a i) = \sum_(0 <= i < n)(a i.+1).
  Proof. by rewrite big_add1 succnK. Qed.

  Lemma sum_first m n a :
    m < n ->
    \sum_(m <= i < n)(a i) = a m + \sum_(m.+1 <= i < n)(a i).
  Proof.
    move=> Hn.
      by rewrite big_ltn.
  Qed.

  Lemma sum_last m n a :
    m <= n ->
    \sum_(m <= i < n.+1)(a i) = \sum_(m <= i < n)(a i) + a n.
  Proof.
    move=> Hmn.
      by rewrite big_nat_recr.
  Qed.
  
End Summation1.

(**
# 証明
*)
Section Notprime.

(**
## さらに補題
*)

(**
合成数の定義から、それが2以上（1を越える）自然数の積であることがただちに解る。
それの補題を証明しておく。「ltn_Pmulrの逆」と思ってもよい。
*)
  Check ltn_Pmulr : forall a b : nat, 1 < b -> 0 < a -> a < a * b.
  (* これの逆を証明しておく。 *)
  
  Lemma ltn_Pmulr_r a b : 0 < a -> a < a * b -> 1 < b.
  Proof.
    Check ltn_mul2l.
    move=> Ha.
    rewrite -{1}[a]muln1.
    rewrite [a * 1 < a * b]ltn_mul2l.
    move/andP.
      by case.
  Qed.

(**
2以上（1を越える）自然数を条件とすると、次の補題が成り立つ。
*)
  Lemma e2b_1_gt1 b : 1 < b -> 1 < 2^b - 1.
  Proof.
    move=> Hb1.
    rewrite ltn_subRL addn1.
    rewrite -{1}(expn1 2).
      by rewrite ltn_exp2l.
  Qed.

(**
## 合成数の定義

「それより小さい、ふたつの0でない自然数の積で表される、自然数」としてそのまま定義する。
*)
  Definition notprime n :=
    exists a b, (0 < a) /\ (0 < b) /\ (a < n) /\ (b < n) /\ (a * b = n).

(**
## 補題

``notprime n -> notprime (2^n - 1)`` を証明する。

``x*y = 2^n - 1`` となる具体的な x と y を与えることで証明する。

``x = 2^b - 1``
``y = \sum_(0 <= i < a) 2^(i * b)``

``x*y = 2^n - 1`` であることを証明するのではだめで、
x*y もまた合成数であることを証明する必要がある。

以下にそのための補題を示す。
*)  

  (* 0 < x *) 
  Lemma e2b_1_gt0 b : 0 < b -> 0 < 2^b - 1.
  Proof.
    move=> H.
    rewrite ltn_subRL addn0.
    rewrite -{1}(expn1 2).
      by rewrite leq_exp2l.
  Qed.
  
  (* 0 < y *)
  Lemma sum0a_e2ib_gt0 a b : 0 < a -> 0 < \sum_(0 <= i < a) 2^(i * b).
  Proof.
    move=> H.
      by rewrite sum_first.
  Qed.
  
  (* x*y = 2^n - 1 *)
  Lemma l_e2_ab_1 a b :
    0 < a ->
    (2^b - 1) * (\sum_(0 <= i < a) 2^(i * b)) = 2^(a * b) - 1.
  Proof.
    move=> Ha.
    
    (* 左辺を展開する。 *)
    rewrite mulnBl.
    
    (* 左辺、第1項 *)
    rewrite -sum_distrr //=.
    have H : \sum_(0 <= i < a) 2^b * 2^(i * b) = \sum_(0 <= i < a) 2^(i.+1 * b).
      by apply: eq_sum => i; rewrite -expnD mulnC -mulnS mulnC.
    rewrite H.
    rewrite -(sum_add1 a (fun x => 2^(x * b))).
    rewrite [\sum_(1 <= i < a.+1) 2^(i * b)]sum_last //=.
    
    (* 左辺、第2項 *)
    rewrite  mul1n.
    rewrite [\sum_(0 <= i < a) 2^(i * b)]sum_first //=.
    rewrite mul0n expn0.
    rewrite [1 + \sum_(1 <= i < a) 2^(i * b)]addnC.
    
    (* 左辺を整理する。 *)
    rewrite subnDl.
    done.
  Qed.
  
  (* x < x*y *)
  Lemma e2b_1_lt_e2ab_1 a b :
    0 < a -> 0 < b -> b < a * b -> 2^b - 1 < 2^(a * b) - 1.
  Proof.
    move=> Ha Hb Hbn.
    apply: ltn_sub2r.
    - rewrite -{1}(expn0 2).
      rewrite ltn_exp2l //.
      rewrite muln_gt0.
        by apply/andP.
    - by rewrite ltn_exp2l //.
  Qed.
  
  (* y < x*y *)
  Lemma sum0a_e2ib_lt_e2ab_1 a b :
    0 < a -> 1 < b ->
    \sum_(0 <= i < a) 2^(i * b) < 2^(a * b) - 1.
  Proof.
    move=> Ha Hb1.
    rewrite -l_e2_ab_1 //=.
    rewrite -{1}[\sum_(0 <= i < a) 2^(i * b)]mul1n.
    rewrite ltn_pmul2r.
    (* 1 < 2^b - 1 *)
    - by rewrite e2b_1_gt1.
    (* 0 < \sum_(0 <= i < a) 2^(i * b) *)
    - by rewrite sum_first.
  Qed.
  
(**
## 証明したい定理
*)  
  Lemma e2_ab_1_notprime n :
    notprime n -> notprime (2^n - 1).
  Proof.
    case=> a.
    case=> b.
    case=> [Ha [Hb [Han [Hbn Hab]]]].
    rewrite -Hab in Han.
    rewrite -Hab in Hbn.
    rewrite /notprime -Hab.
    exists (2^b - 1), (\sum_(0 <= i < a) 2^(i * b)).
    split; [| split; [| split; [| split]]].
    - by apply: e2b_1_gt0.                  (* 0 < x *)
    - by apply: sum0a_e2ib_gt0.             (* 0 < y *)
    - by apply: e2b_1_lt_e2ab_1.            (* x < x*y *)
    (* ここで 1 < b が必要になる。 *)
    - have Hb1 : 1 < b by apply: (@ltn_Pmulr_r a).
        by apply: sum0a_e2ib_lt_e2ab_1.     (* y < x*y *)
    - by apply: l_e2_ab_1.                  (* x*y = 2^n - 1 *)
  Qed.

End Notprime.

(* END *)




(* *************************** *)
(* *************************** *)
(* 以下はゴミゴミゴミ *)
(* *************************** *)
(* *************************** *)










(**
2<=a, 2<=b であれば、a*bは合成数である。

任意のxに、$ (2^{b} - 1) $ を
任意にyに、$\sum_{i=0}^{a-1}2^{i b}$ を代入する。

x*y が合成数であることも言わなければばらないが、
2<=x, 2<=y であれば、x*yは合成数であるといえる。

そして先の補題で x*y = 2^(a*b) - 1 を証明する。

以上より a*bが合成数なら、2^(a*b) - 1 は合成数である。
*)  
  
  (* 何か所かで使う補題。 *)
  Lemma le2_le1 a : 2 <= a -> 1 <= a.
  Proof. move=> H. by ssromega. Qed.
  
  (* 2 <= x の証明に使用する。 *)
  Lemma e2b_1_ge2 b : 2 <= b -> 2 <= 2^b - 1.
  Proof.
    move=> H.
    rewrite ltn_subRL addn1.
    rewrite -{1}(expn1 2).
      by rewrite ltn_exp2l.
  Qed.

  (* 2 <= y の証明に使用する。 *)  
  Lemma sum0_2_e2ib a b :
    2 <= a -> 2 <= b -> 2 <= \sum_(0 <= i < a) 2^(i * b).
  Proof.
    move=> Ha Hb.
    rewrite sum_first; last by apply: le2_le1.
    rewrite sum_first; last done.
    have H1 : 1 <= 2^(0 * b) by rewrite mul0n expn0.
    have H2 : 1 <= 2^(1 * b) by rewrite mul1n expn_gt0 orb_idr.
    have H3 : 0 <= \sum_(2 <= i < a) 2^(i * b) by done. (* 0以上は自明。 *)
      by ssromega.
  Qed.
  
  (* 証明したいもの *)
  Lemma e2_ab_1_notprime (a b : nat) :
    2 <= a -> 2 <= b ->
    exists (x y : nat), 2 <= x /\ 2 <= y /\ (x * y = 2^(a * b) - 1).
  Proof.
    move=> Ha Hb.
    exists (2^b - 1), (\sum_(0 <= i < a) 2^(i * b)).
    split ; [| split].
    - by apply: e2b_1_ge2.                  (* 2 <= x *)
    - by apply: sum0_2_e2ib.                (* 2 <= y *)
    - move/le2_le1 in Ha.
        by apply: l_e2_ab_1.                (* x * y *)
  Qed.
  



  Definition zero (_ : nat) := 0.
  
  Lemma sum0_0 m n : \sum_(m <= i < n) zero i = 0.
  Proof.
    rewrite /zero.
    rewrite sum_nat_const_nat.
      by rewrite muln0.
  Qed.
  
  Lemma ge0'_sum m n a :
    (forall i, zero i <= a i) ->
    \sum_(m <= i < n) zero i <= \sum_(m <= i < n) a i.
  Proof.
    move=> H.
      by apply: leq_sum.
  Qed.
  
  Lemma ge0_sum m n a : (forall i, 0 <= a i) -> 0 <= \sum_(m <= i < n) a i.
  Proof.
    move=> H.
    rewrite -{1}(sum0_0 m n).
    apply: ge0'_sum => i.
      by rewrite /zero.
  Qed.
  

  


