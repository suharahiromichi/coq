(**
位取り記数法の変換の証明
==================

2020_9_29 @suharahiromichi
*)

(**
# はじめに

ソースコードは以下にあります。

https://github.com/suharahiromichi/coq/blob/master/math/ssr_positional_notation.v
 *)

From mathcomp Require Import all_ssreflect.
Require Import Recdef.
Require Import Wf_nat.                      (* well_founded lt *)
Require Import ssromega.

(**
https://github.com/suharahiromichi/coq/blob/master/common/ssromega.v

もダウンロードして同じディレクトリに置いて、coqc ssromega.v を実行し、
ssromega.vo ができていることを確認してください。
*)
     
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(**
総和（Σ）についての補題。
*)
Section Sum.
(**
# Σの中身の書き換え

Σの中の i は、ローカルに束縛されている（ラムダ変数である）ので、
直接書き換えることはできません。一旦、取り出して書き換えることになります。
 *)
  Lemma eq_sum m n a b : a =1 b ->
                         \sum_(m <= i < n)(a i) = \sum_(m <= j < n)(b j).
  Proof.
    move=> Hab.                             (* =1 は第1階の=です。 *)
    apply: eq_big_nat => i Hmn.
      by rewrite Hab.
  Qed.

(**
## ``a_n``項を取り出す。

$$ \sum_{i=n}^{n}a_i = a_n $$

総和をとる範囲がひとつの項の場合（n以上n以下）は、``a n`` となります。
 *)
  Lemma sum_nat1 n a :
    \sum_(n <= i < n.+1)(a i) = a n.
  Proof. by rewrite big_nat1. Qed.
(**
## 最後の項をΣの外に出す。

n(インデックスの上限)についての帰納法と組み合わせて使います。

$$ \sum_{i=m}^{n}a_i = \sum_{i=m}^{n-1}a_i + a_n $$
 *)
  Lemma sum_last m n a :
    m <= n ->
    \sum_(m <= i < n.+1)(a i) = \sum_(m <= i < n)(a i) + a n.
  Proof.
    move=> Hmn.
      by rewrite big_nat_recr.
  Qed.
End Sum.  

Section Lemmas.
(**
補題

商と剰余の関係式を変形したものを証明しておく。
*)
  Check divn_eq : forall m d : nat, m = m %/ d * d + m %% d.
  
  Lemma divn_modn_eq (m d : nat) : m %/ d * d = m - m %% d.
  Proof.
    rewrite {2}(divn_eq m d).
    rewrite -addnBA //=.
      by ssromega.
(*
    apply/eqP.
    Check eqn_add2r (a %% d) (a %/ d * d) (a - a %% d). (* 両辺に a %% d を加える。 *)
    rewrite -(eqn_add2r (a %% d) (a %/ d * d) (a - a %% d)).
    apply/eqP.
      by rewrite -[LHS]divn_eq subnK // leq_mod.
*)
  Qed.
  
  Lemma modn_divn_eq (m d : nat) : m %% d = m - m %/ d * d.
  Proof.
    rewrite {2}(divn_eq m d).
    rewrite -addnBAC //=.
      by ssromega.
  Qed.
  
(**
補題

m を 10 で割った余りよりも、100 で割った余りの方が大きい。
*)
  Lemma le__mod_le (m d q : nat) : d <= q -> m %% d <= m %% q.
  Proof.
    move=> Hab.
    rewrite 2!modn_divn_eq.
    apply: leq_sub2l.
    Search _ (_ * _ <= _ * _).
    apply: leq_mul.
    Search _ (_ %/ _ <= _ %/ _).
    - apply: leq_div2l.
  Admitted.                                 (* 不使用 *)

  Lemma mod_le_mod (m d n : nat) : 0 < d -> 0 < n -> m %% d <= m %% (d * n).
  Proof.
    move=> Hd Hn.
    rewrite 2!modn_divn_eq.
    apply: leq_sub2l.
    rewrite {2}[d * n]mulnC.
    rewrite mulnA leq_pmul2r //.
    rewrite [m %/ (d * n)]divnMA.
    Check leq_trunc_div (m %/ d) n : (m %/ d) %/ n * n <= m %/ d.
      by apply: leq_trunc_div.
  Qed.
  
(**
d^n+1 で割った余りを d^n で割った余りは、単に、d^n で割った余りに等しい。
じつは、単なる表記の違いだけであるので、使っていない。
*)
  Lemma mod_mod__mod (m n d : nat) : d %| n -> m %% n %% d = m %% d.
  Proof.
    Check modn_dvdm : forall m n d : nat, d %| m -> n %% m = n %[mod d].
    move=> H.
      by rewrite modn_dvdm.
  Qed.
End Lemmas.
  
Section PositionalNotation.
  Variables d : nat.                        (* 基数 *)

(**
m を d進数で表したときの i 桁め。
*)
  Definition digit (m i : nat) := m %% d^i.+1 %/ d^i.

(**
m を d進数で表して、もとに戻したもの。
*)
  Definition position_note (m n : nat) := \sum_(0 <= i < n.+1) (digit m i) * d^i.
  
(**
Σの中身を書き換えるための補題。
*)
  Lemma l_mod_div__mod_mod (m : nat) :
    (fun (i : nat) => m %% d^i.+1 %/ d^i * d^i)
    =1 (fun (i : nat) => m %% d^i.+1 - m %% d^i).
  Proof.
    move=> i.
    Check divn_modn_eq (m %% d^i.+1) (d^i).
    rewrite (divn_modn_eq (m %% d^i.+1) (d^i)).
    congr (m %% d^i.+1 - _).
    rewrite modn_dvdm //.
      by apply: dvdn_exp2l.
  Qed.
  
(**
証明したいもの。
*)
  Lemma positional_eq (m n : nat) : 0 < d -> m %% d^n.+1 = position_note m n.
  Proof.
    move=> Hd.
    rewrite /position_note /digit.
    Check eq_sum 0 n.+1 (l_mod_div__mod_mod m).
    rewrite (eq_sum 0 n.+1 (l_mod_div__mod_mod m)).

    elim: n => [| n IHn].
    - by rewrite sum_nat1 // expn0 modn1 subn0.
    - rewrite sum_last // -IHn subnKC //.
      rewrite -[in d ^ n.+2]addn1 expnD.
      
      apply: mod_le_mod => //=.
      rewrite expn_gt0.
        by apply/orP/or_introl.
      (* by rewrite le__mod_le //= leq_exp2l *)
  Qed.
End PositionalNotation.

Section Recurrence_Relation.
  Variables d c : nat.                      (* 基数 *)
  Variables alpha beta : nat -> nat.
  
  Function f_rec (m : nat) {wf lt m} :=
    if d <= 1 then 0
    else if m < d then alpha m
    else
      f_rec (m %/ d) + beta (m %% d).
  Proof.
    - move=> m Hd Hmd.
      apply/ltP/ltn_Pdiv.
      + move/negbT in Hd.
          by ssromega.
      + by ssromega.
    - by apply: lt_wf.                      (* Wf_nat *)
  Defined.
  
  Lemma f_rec_eq_t (j : nat) : 0 < d -> j < d -> f_rec j = alpha j.
  Proof.
  Admitted.

  Lemma f_rec_eq_s (m j : nat) :
    0 < d -> j < d -> f_rec (d * m + j) = c * (f_rec m) + beta j.
  Proof.
  Admitted.  
  
End Recurrence_Relation.
    
(**
# 参考文献

*)

(* END *)
