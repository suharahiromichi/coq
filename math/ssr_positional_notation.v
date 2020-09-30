(**
位取り記数法の変換の証明
==================

2020_9_29 @suharahiromichi
*)

(**
# はじめに

ソースコードは以下にあります。


 *)

From mathcomp Require Import all_ssreflect.

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

Section PositionalNotation.
(**
XXXXX
*)
  Lemma modn_def' (a d : nat) : a %% d = a - a %/ d * d.
  Proof.
    rewrite {2}[a](divn_eq a d).
    rewrite -[RHS]addnBAC //=.
      by ssromega.
  Qed.
  
  Lemma le__mod_le (x a b : nat) : a <= b -> x %% a <= x %% b.
  Proof.
    move=> Hab.
    rewrite 2!modn_def'.
    apply: leq_sub2l.
    Search _ (_ * _ <= _ * _).
    apply: leq_mul.
    Search _ (_ %/ _ <= _ %/ _).
    - apply: leq_div2l.
  Admitted.                                 (* 不使用 *)

  Lemma mod_le_mod (x a b : nat) : 0 < a -> 1 < b -> x %% a <= x %% (a * b).
  Proof.
    move=> Ha Hb.
    rewrite 2!modn_def'.
    apply: leq_sub2l.
    rewrite {2}[a * b]mulnC.
    rewrite mulnA leq_pmul2r //.
    rewrite [x %/ (a * b)]divnMA.
      by apply: leq_trunc_div (x %/ a) b.
  Qed.
  
(**
補題
*)
  Lemma l_div_mul (a d : nat) : a %/ d * d = a - a %% d.
  Proof.
    apply/eqP.
    Check eqn_add2r (a %% d) (a %/ d * d) (a - a %% d). (* 両辺に a %% d を加える。 *)
    rewrite -(eqn_add2r (a %% d) (a %/ d * d) (a - a %% d)).
    apply/eqP.
    Check divn_eq : forall m d : nat, m = m %/ d * d + m %% d.
      by rewrite -[LHS]divn_eq subnK // leq_mod.
  Qed.
  
(**
x を d進数で表したときの i 桁め。
*)
  Definition digit (x d i : nat) := x %% d^i.+1 %/ d^i.

(**
x を d進数で表して、もとに戻したもの。
*)
  Definition radix_disp (x d n : nat) := \sum_(0 <= i < n.+1) (digit x d i) * d^i.
  
(**
d^n+1 で割った余りを d^n で割った余りは、単に、d^n で割った余りに等しい。
じつは、単なる表記の違いだけであるので、使っていない。
*)
  Lemma mod_mod__mod (x n d : nat) : d %| n -> x %% n %% d = x %% d.
  Proof.
    Check modn_dvdm : forall m n d : nat, d %| m -> n %% m = n %[mod d].
    move=> H.
      by rewrite modn_dvdm.
  Qed.
  
(**
Σの中身を書き換えるための補題。
*)
  Lemma l_mod_div__mod_mod (x d : nat) :
    (fun (i : nat) => x %% d^i.+1 %/ d^i * d^i)
    =1 (fun (i : nat) => x %% d^i.+1 - x %% d^i).
  Proof.
    move=> i.
    Check l_div_mul (x %% d^i.+1) (d^i).
    rewrite (l_div_mul (x %% d^i.+1) (d^i)).
    congr (x %% d^i.+1 - _).
    rewrite modn_dvdm //.
      by apply: dvdn_exp2l.
  Qed.
  
(**
証明したいもの。
*)
  Lemma positional_eq (x d n : nat) : 1 < d -> x %% d^n.+1 = radix_disp x d n.
  Proof.
    move=> Hd.
    rewrite /radix_disp /digit.
    Check eq_sum 0 n.+1 (l_mod_div__mod_mod x d).
    rewrite (eq_sum 0 n.+1 (l_mod_div__mod_mod x d)).

    elim: n => [| n IHn].
    - by rewrite sum_nat1 // expn0 modn1 subn0.
    - rewrite sum_last // -IHn subnKC //.
      rewrite -[in d ^ n.+2]addn1 expnD.
      
      apply: mod_le_mod => //=.
      rewrite expn_gt0.
      apply/orP/or_introl.
        by ssromega.
      (* by rewrite le__mod_le //= leq_exp2l *)
  Qed.
End PositionalNotation.

(**
# 参考文献

*)

(* END *)
