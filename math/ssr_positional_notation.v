(**
位取り記数法と漸化式の解法
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
From common Require Import ssromega.

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
## 総和の結合と分配
*)
  Lemma sum_split m n a b :
    m < n ->
    \sum_(m <= i < n)(a i) + \sum_(m <= i < n)(b i) = \sum_(m <= i < n)(a i + b i).
  Proof. by rewrite big_split. Qed.

  Lemma sum_distrr m n c a :
    m < n ->
    \sum_(m <= i < n)(c * (a i)) = c * (\sum_(m <= i < n)(a i)).
  Proof. by rewrite big_distrr. Qed.

  Lemma sum_distrl m n a c :
    m < n ->
    \sum_(m <= i < n)((a i) * c) = (\sum_(m <= i < n)(a i)) * c.
  Proof. by rewrite big_distrl. Qed.

  Check sum_nat_const_nat : forall m n c,
      \sum_(m <= i < n) c = (n - m) * c.

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
## 最初の項をΣの外に出す。

$$ \sum_{i=m}^{n-1}a_i = a_m + \sum_{i=m+1}^{n-1}a_i $$
 *)
  Lemma sum_first m n a :
    m < n ->
    \sum_(m <= i < n)(a i) = a m + \sum_(m.+1 <= i < n)(a i).
  Proof.
    move=> Hn.
      by rewrite big_ltn.
  Qed.

(**
総和の範囲の起点を変えずに、インデックスをずらす補題もあります。

$$ \sum_{i=m}^{n}a_i = a_m + \sum_{i=m}^{n-1}a_{i + 1} $$
*)
  Lemma sum_first' m n a :
    m <= n ->
    \sum_(m <= i < n.+1)(a i) = a m + \sum_(m <= i < n)(a i.+1).
  Proof.
    move=> Hn.
      by rewrite big_nat_recl.
  Qed.

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
  
(**
# 位取り記数法
*)
Section PositionalNotation.
  Variables b c : nat.                      (* 基数 *)
  Hypothesis Hb : 2 <= b.                   (* 2以上 *)
  Hypothesis Hc : 2 <= c.
  
  (**
m を d進数で表したときの i 桁め。
*)
  Definition digit (m i : nat) := m %% b^i.+1 %/ b^i.

(**
m を d進数で表して、もとに戻したもの。
*)
  Definition position_note (m n : nat) := \sum_(0 <= i < n.+1) (digit m i) * b^i.
  
(**
Σの中身を書き換えるための補題。
*)
  Lemma l_mod_div__mod_mod (m : nat) :
    (fun (i : nat) => m %% b^i.+1 %/ b^i * b^i)
    =1 (fun (i : nat) => m %% b^i.+1 - m %% b^i).
  Proof.
    move=> i.
    Check divn_modn_eq (m %% b^i.+1) (b^i).
    rewrite (divn_modn_eq (m %% b^i.+1) (b^i)).
    congr (m %% b^i.+1 - _).
    rewrite modn_dvdm //.
      by apply: dvdn_exp2l.
  Qed.
  
  (* 2より大きいなら、1より大きい。  *)
  Lemma le1_le m x : m.+1 <= x -> m <= x.
  Proof.
    move=> H.
      by rewrite ltnW.
  Qed.

  Lemma not_leb__geb m b' : (m < b') = false -> b' <= m.
  Proof.
    move=> H.
      by ssromega.
  Qed.

(**
証明したいもの。
*)
  Lemma positional_eq (m n : nat) : m %% b^n.+1 = position_note m n.
  Proof.
    rewrite /position_note /digit.
    Check eq_sum 0 n.+1 (l_mod_div__mod_mod m).
    rewrite (eq_sum 0 n.+1 (l_mod_div__mod_mod m)).

    elim: n => [| n IHn].
    - by rewrite sum_nat1 // expn0 modn1 subn0.
    - rewrite sum_last // -IHn subnKC //.
      rewrite -[in b ^ n.+2]addn1 expnD.
      
      apply: mod_le_mod => //=.
      rewrite expn_gt0.
      + by apply/orP/or_introl/le1_le.
      + by apply: le1_le.
  Qed.
  
(**
# 位取り記数法による漸化式の解法
*)
  Variables alpha beta : nat -> nat.

  Lemma ltn_leq_trans n m p : m < n -> n <= p -> m < p.
  Proof. move=> Hmn; exact: leq_trans. Qed.
  
  Lemma geb_lt0 m : b <= m -> 0 < m.
  Proof.
    move=> H.
    move/ltn_leq_trans in H.
    move: Hb => /H Hb'.
    (* 1 < m -> 0 < m は遷移則 ltn_trans を使う。 *)
    move/(@ltn_trans 1 0 m) in Hb'.
      by apply: Hb'.
  Qed.
  
  Function f_rec (m : nat) {wf lt m} :=
    if m < b then alpha m
    else
      c * f_rec (m %/ b) + beta (m %% b).
  Proof.
    - move=> m Hmb.
      apply/ltP/ltn_Pdiv.
      + done.
      + move/not_leb__geb in Hmb.
          by apply: geb_lt0.
    - by apply: lt_wf.
  Qed.
  
  (* Coq の用意する帰納法の原理 *)
  Check f_rec_ind.
  
  (* 自分で見直した帰納法の原理 *)
  Lemma f_rec_ind'' (P : nat -> nat -> Prop) :
    (forall m : nat, (m < b) = true -> P m (alpha m)) ->
    (forall m : nat, (m < b) = false ->
                     P (m %/ b) (f_rec (m %/ b)) ->
                     P m (c * f_rec (m %/ b) + beta (m %% b))) ->
       forall m : nat, P m (f_rec m).
  Proof.
  Admitted.

  (* 教科書的な帰納法の原理 *)
  Lemma f_rec_ind' (P : nat -> nat -> Prop) :
    (forall m    : nat, (m < b) = true  -> P m (alpha m)) ->
    (forall m m' : nat, (m < b) = false -> P (m %/ b) m' ->
                        P m (c * m' + beta (m %% b))) ->
    forall m m' : nat, P m m'.
  Proof.
  Admitted.
  
  (* 帰納的な関数の仕様 *)
  Inductive f_ind : nat -> nat -> Prop :=
  | F_ind_t m : m < b -> f_ind m (alpha m)
  | F_ind_s m m' : b <= m -> f_ind (m %/ b) m' ->
                   f_ind m (c * m' + beta (m %% b)).
  
(**
``m = d * n + j`` に分解する補題
*)
  Lemma positional_step (m n : nat) :
    0 < n ->
    \sum_(0 <= i < n.+1) digit m i * b ^ i =
    b * (\sum_(0 <= i < n) (digit m i.+1) * b^i) + m %% b.
  Proof.
    move=> Hn.
    rewrite [LHS]sum_first' //.
    rewrite {1}/digit expn1 expn0 divn1 muln1.
    have H : (fun i => digit m i.+1 * b^i.+1) =1 (fun i => digit m i.+1 * b^i * b)
      by move=> i; rewrite -[RHS]mulnA -[in RHS]expnSr.
    rewrite (eq_sum 0 n H) sum_distrl //.
      by rewrite addnC mulnC.
  Qed.

  Lemma pos_rec (m n : nat) : 0 < n -> f_ind (m %% b^n.+1) (f_rec (m %% b^n.+1)).
  Proof.
    move=> Hn.
    rewrite positional_eq /position_note.
    rewrite positional_step => //.
    rewrite f_rec_equation.
    case: ifP => H.
    (* m < b *)
    - apply: F_ind_t.
      done.
    (* m ≧ b *)
    - apply: F_ind_s.
      + by ssromega.
      + admit.
  Admitted.
  
  Lemma positional_rec (m n : nat) :
    0 < n ->
    f_rec (m %% b^n.+1) =
    alpha (digit m n) * c^n + \sum_(0 <= i < n)(beta (digit m i)) * c^i.
  Proof.
    move=> Hn.
    rewrite positional_eq /position_note.
    rewrite positional_step => //.
    (* functional induction (f_rec (m %% b^n.+1)). *)
  Admitted.
  
  Lemma pos_rec2 (m n : nat) :
    0 < n -> f_ind (m %% b^n.+1)
                   (alpha (digit m n) * c^n + \sum_(0 <= i < n)(beta (digit m i)) * c^i).
  Proof.
    move=> Hn.
    rewrite positional_eq /position_note.
    rewrite positional_step => //.
  Admitted.
  
(**
不使用
*)  
  Axiom alpha0 : alpha 0 = 0.
  Axiom beta0 : beta 0 = 0.

  Lemma l_d_is_1 (d : nat) : 0 < d -> d <= 1 -> d = 1.
  Proof.
    move=> H0 H1.
      by ssromega.
  Qed.

  Lemma f_rec_eq_0 :  f_rec 0 = 0.
  Proof.
  Admitted.

  Lemma not_le1__ge2 d : (d <= 1) = false -> 2 <= d.
  Proof.
    move=> H.
      by ssromega.
  Qed.

End PositionalNotation.

(**
# 参考文献

Knuth 他著、有沢他訳、「コンピュータの数学」 共立出版。第１章
*)

(* END *)
