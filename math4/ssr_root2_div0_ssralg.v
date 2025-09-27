(**
2020_AW 6. 数の証明

``https://www.math.nagoya-u.ac.jp/~garrigue/lecture/2020_AW/ssrcoq6.pdf``
``file:///Users/suhara/Documents/CS%E6%96%87%E7%8C%AE/mathcomp/akr/202205%E5%A4%A9%E6%B3%A3%E8%A8%98.html``

3. √2 が無理数

======

2021_04_29 @suharahiromichi
 *)
From mathcomp Require Import all_ssreflect.
From mathcomp Require Import all_algebra.
From mathcomp Require Import ssrZ zify ring lra.

(* for test *)
(* lt_wf_nat, gt_wf_ind, lt_wf_double_ind *)
Require Import Wf_nat.          (* 整礎帰納法 *)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section Root2.
  
  Section Nat.
    
    Definition even x := ~~ odd x.
    
    Lemma odd_square n : odd n = odd (n * n).
    Proof.
      rewrite oddM.
      by rewrite andbb.
    Qed.
    
    Lemma even_square n : even n = even (n * n).
    Proof.
      congr (~~ _).
      by rewrite odd_square.
    Qed.
    
    Lemma l_even_d2 x : even x = (2 %| x).
    Proof.
      by rewrite dvdn2.
    Qed.
  
(**
## 簡単な算数 ``4 \ 2x = 2 \ x``
*)
    Lemma l_dd4_d2 x : (4 %| x.*2) = (2 %| x).
    Proof.
      lia.
    Qed.

(**
## n と p が偶数であることの証明
*)
    Lemma l_d4s x : 2 %| x -> 4 %| (x * x).
    Proof.
      lia.
    Qed.

(**
## nは2の倍数
*)  
    Lemma l_d2n n p : n * n = (p * p).*2 -> 2 %| n.
    Proof.
      move=> H.
      rewrite -l_even_d2.
      rewrite even_square H.
      by rewrite /even odd_double.
    Qed.

(**
## pは2の倍数
*)  
    Lemma l_d2p (n p : nat) : n * n = (p * p).*2 -> 2 %| p.
    Proof.
      move=> H.
      rewrite -l_even_d2 even_square l_even_d2.
      rewrite -l_dd4_d2 -H l_d4s => //.
      by apply: (l_d2n H).
    Qed.

(**
## ``p/2 = 0 -> p = 0`` の証明
*)  
    Lemma l_h0_0 p : 2 %| p -> p./2 = 0 -> p = 0.
    Proof.
      lia.
    Qed.
    
(**
## 直接使う補題（その１）
*)
    Lemma l_hh_sq x : 2 %| x -> x./2 * x./2 = (x * x) %/ 4.
    Proof.
      lia.
    Qed.

(**
## 直接使う補題（その２）
*)
    Lemma l_dq_qd x : 4 %| x -> x.*2 %/ 4 = (x %/ 4).*2.
    Proof.
      move=> H.
      by rewrite -2!muln2 divn_mulAC.
    Qed.
    
    Lemma ll_main_ih (n p : nat) :
      n * n = (p * p).*2 -> n./2 * n./2 = (p./2 * p./2).*2.
    Proof.
      move=> Hnp.
(*
Goal に直接 apply IH せず、一旦 p/2 = 0 に変換してからおこなう。
 *)
      - rewrite l_hh_sq;
          last apply: (l_d2n Hnp).            (* nが2の倍数なら。 *)
        rewrite Hnp.
        rewrite l_hh_sq;
          last apply: (l_d2p Hnp).            (* pが2の倍数なら。 *)
        rewrite l_dq_qd;
          last (apply: l_d4s; apply: (l_d2p Hnp)). (* p*p が4の倍数なら。 *)
        done.
    Qed.
  
(**
## 定理1

任意の自然数 n と p について，n · n = 2(p · p) ならば p = 0。

非形式的な証明：


- 右辺は偶数なので、左辺も偶数なので、n は 偶数である。
- nが偶数なら、両辺は 4 の倍数なので、p も 偶数である。
- n = 2n' と p = 2p'を代入すると、再び n'*n' = 2*p'*p' , n'<n が得られる。
- 帰納法の仮定から p' = 0 である。
- すなわち p = 0 である。

形式的な証明：
- Hn : 0 < n
- Hnp : n * n = (p * p).*2
の元で、帰納法の仮定

IH : forall m, (m < n -> forall p, (m * m = (p * p).*2 -> p = 0))

から p = 0 を証明する。具体的には、

n/2 < n なので、

- n ← n/2
- p ← p/2

という代入のもとで p/2 = 0 を証明する。p/2 = 0 ならば p = 0 といえる。
*)

    Theorem main_thm (n p : nat) : n * n = (p * p).*2 -> p = 0.
    Proof.
      move: p.
      elim/lt_wf_ind: n => n.               (* 清礎帰納法 *)
      case: (posnP n); try lia.             (* n に下駄を履かせる。 *)
      move=> Hn IH p Hnp.
(*
  n : nat
  Hn : 0 < n
  IH : forall n0 : nat, (n0 < n)%coq_nat -> forall p : nat, n0 * n0 = (p * p).*2 -> p = 0
  p : nat
  Hnp : n * n = (p * p).*2
  ============================
  p = 0
*)
      apply: l_h0_0.
      - by apply: (l_d2p Hnp).              (* pは2の倍数。 *)
      - apply: (IH n./2); try lia.
        by apply: ll_main_ih.
        
(* *************************** *)
      Restart. Show.
      move: p.
      (* ``forall p, P n p`` を
         ``forall m, m <= n -> forall p, P m p`` に一般化してから
         普通の自然数の帰納法 (nat_ind) を使う。 *)
      elim: n {-2}n (leqnn n); try lia.
      move=> n IH m Hn p Hmp.
(*
  n : nat
  IH : forall n0 : nat, n0 <= n -> forall p : nat, n0 * n0 = (p * p).*2 -> p = 0
  m : nat
  Hn : m <= n.+1
  p : nat
  Hnp : m * m = (p * p).*2
  ============================
  p = 0
*)
      apply: l_h0_0.
      - by apply: (l_d2p Hmp).              (* pは2の倍数。 *)
      - apply: (IH m./2); try lia.
        by apply: ll_main_ih.
        
(* *************************** *)
      Restart. Show.
      move: p.
      (* ``forall p, P m p`` *)
      move: n => m.
      (* ``forall m, m < n -> (forall p, P m p)`` に一般化する。 *)
      have [n] := ubnP m.                   (* upper bound Predicate *)
      (* ``forall m, m <= n -> (forall p, P m p)`` にする。 *)
      case: n => //= n; rewrite ltnS.        (* n に下駄を履かせる。 ltnS はおまけ。 *)
      (* 普通の自然数の帰納法 (nat_ind) を使う。 *)
      elim: n m; try lia.
      move=> n IH m Hn p Hmp.
(*
  n : nat
  IH : forall n0 : nat, n0 < n.+1 -> forall p : nat, n0 * n0 = (p * p).*2 -> p = 0
  m : nat
  Hn : m < n.+2
  p : nat
  Hmp : m * m = (p * p).*2
  ============================
  p = 0
*)
      apply: l_h0_0.
      - by apply: (l_d2p Hmp).              (* pは2の倍数。 *)
      - apply: (IH m./2); try lia.
        by apply: ll_main_ih.
    Qed.
    
  End Nat.

(*
# 無理数
*)
  Section Real.
    
    Open Scope ring_scope.
    Import GRing.                        (* natrM *)
    Import Num.Theory.                   (* sqr_sqrtr, eqr_nat など *)
    
    Variable R : rcfType.                   (* sqrt が計算できる型 *)
    
    Search "sqrt".
    Check sqr_sqrtr : forall (R : rcfType) (a : R), 0 <= a -> Num.sqrt a ^+ 2 = a.
    
    (* R と nat の相互変換 *)
    Check eqr_nat R : forall m n : nat, (m%:R == n%:R) = (m == n).
    Check ler_nat R : forall m n : nat, (m%:R <= n%:R) = (m <= n)%N.
    Check ltr_nat R : forall m n : nat, (m%:R < n%:R) = (m < n)%N.
    
(**
## x は無理数である。
*)
    Definition irrational (x : R) : Prop := forall (p q : nat),
        q <> 0 -> x <> p%:R / q%:R.
    
(*
## 証明したいもの ``sqrt 2`` は無理数である。
*)
    Theorem irrational_sqrt_2 : irrational (Num.sqrt 2).
    Proof.
      move=> p q Hq.
      (* 対偶を取る。ただし Hq は残しておく。 *)
      apply: contra_not (Hq) => Hrt.
      apply/(@main_thm p)/eqP.
      rewrite -(eqr_nat R) natrM -mul2n natrM.
      rewrite -(@sqr_sqrtr R 2) //= Hrt.
      apply/eqP.
      field.
      apply/negP.
      rewrite (eqr_nat R q 0).
      lia.
    Qed.

  End Real.
End Root2.

(* upper bound Predicate *)
Section Ubn.

  Variable P : nat -> nat -> bool.

  (* *********** *)
  (* バニラCoq   *)
  (* *********** *)
  (* Require Import Wf_nat.          (* 整礎帰納法 *) *)
  Search "wf_ind".
  Check lt_wf_ind : forall (n : nat) (P : nat -> Prop),
      (forall n0 : nat, (forall m : nat, (m < n0)%coq_nat -> P m) -> P n0) -> P n.
  Check gt_wf_ind : forall (n : nat) (P : nat -> Prop),
      (forall n0 : nat, (forall m : nat, (n0 > m)%coq_nat -> P m) -> P n0) -> P n.
  
  (* ubnP と同じ。 *)
  Goal forall n p, P n p.
  Proof.
    move=> n.
    elim/lt_wf_ind: n => n IH p.
    Check IH : forall n0 : nat, (n0 < n)%coq_nat -> forall p : nat, P n0 p.
    Check P n p.
  Abort.
  (* 上の問題では、n に下駄を履かせて使う。 *)

  Goal forall n p, P n p.
  Proof.
    move=> n.
    elim/lt_wf_ind: n => n IH p.
    case: (posnP n); try done.              (* n に下駄を履かせる。 *)
    - Check IH : forall n0 : nat, (n0 < n)%coq_nat -> forall p : nat, P n0 p.
      Check n = 0 -> P n p.
      admit.
    - Check IH : forall n0 : nat, (n0 < n)%coq_nat -> forall p : nat, P n0 p.
      Check 0 < n -> P n p.
  Abort.
  
  Goal forall n p, P n p.
  Proof.
    move=> n.
    elim/gt_wf_ind: n => n IH p.
    Check IH : forall n0 : nat, (n > n0)%coq_nat -> forall p : nat, P n0 p.
  Abort.
  
  (* ************** *)
  (* 常套句シリーズ *)
  (* ************** *)
  (* 有名な常套句 *)
  Goal forall n p, P n p.
  Proof.
    move=> n.
    move: n {-2}n (leqnn n) => n m.
    Check m <= n -> forall p : nat, P m p.  (* ****** *)
    elim: n m => [n Hn p | n IH m Hnm p].
    - Check P n p.
      admit.
    - Check IH : forall n0 : nat, n0 <= n -> forall p : nat, P n0 p.
      Check Hnm : m <= n.+1.
      Check P m p.
  Abort.      

  (* 有名な常套句と同じにするには、ubnP の n に下駄を履かせる。 *)
  Goal forall n p, P n p.
  Proof.
    move=> m.
    have [n] := ubnP m.
    Check m < n -> forall p : nat, P m p.
    case: n => //= n.                       (* ！！下駄を履かせる！！ *)
    Check m < n.+1 -> forall p : nat, P m p. (* ****** *)
    elim: n m => [n Hm p | n IH m Hnm p].
    - Check P n p.
      admit.
    - Check IH : forall n0 : nat, n0 < n.+1 -> forall p : nat, P n0 p. (* n0 <= n *)
      Check Hnm : m < n.+2.                 (* m <= n.+1 *)
      Check P m p.
  Abort.
  
  (* ubnP と完全に互換なのは、この常套句である。 *)
  Goal forall n p, P n p.
  Proof.
    move=> n.
    move: n.+1 {-2}n (ltnSn n).
    Check forall n0 n1 : nat, n1 < n0 -> forall p : nat, P n1 p.
    elim=> [// | n' IH m Hnm p].
    clear n.                              (* n が残るのが苦しい。 *)
    move: n' IH Hnm => n IH Hnm.          (* n' を n に書き換える。 *)
    Check IH : forall n0 : nat, n0 < n -> forall p : nat, P n0 p.
    Check Hnm : m < n.+1.                   (* m <= n *)
    Check P m p.
    Abort.
  
  (* ************** *)
  (* ubnP シリーズ  *)
  (* ************** *)
  Check ubnP : forall m : nat, {n : nat | m < n}.
  Check ubnPgeq : forall m : nat, ubn_geq_spec m m.
  Check ubnPleq : forall m : nat, ubn_leq_spec m m.
  Check ubnPeq : forall m : nat, ubn_eq_spec m m.
  
  Goal forall n p, P n p.
  Proof.
    move=> m.
    have [n] := ubnP m.
    Check m < n -> forall p : nat, P m p.
    elim: n m => // n IH m Hn p.
    Check IH : forall n0 : nat, n0 < n -> forall p : nat, P n0 p.
    Check Hn : m < n.+1.                    (* m <= n *)
    Check P m p.
  Abort.


  Goal forall n p, P n p.
  Proof.
    move=> m.
    have [n] := ubnPgeq m.
    Check n <= m -> forall p : nat, P n p.
    elim: n m => [n Hn p | n IH m Hnm p].
    - Check Hn : 0 <= n.
      Check P 0 p.
      admit.
    - Check IH : forall n0 : nat, n <= n0 -> forall p : nat, P n p.
      Check Hnm : n < m.
  Abort.
  
  Goal forall n p, P n p.
  Proof.
    move=> m.
    have [n] := ubnPleq m.
    Check m <= n -> forall p : nat, P n p.
    elim: n m => [n Hn p | n IH m Hnm p].
    - Check Hn : n <= 0.
      Check P 0 p.
      admit.
    - Check IH : forall n0 : nat, n0 <= n -> forall p : nat, P n p.
      Check Hnm : m <= n.+1.
  Abort.

  Goal forall n p, P n p.
  Proof.
    move=> m.
    have [n] := ubnPeq m.
    Check m == n -> forall p : nat, P n p.
    elim: n m => [n Hn p | n IH m Hnm p].
    - Check Hn : n == 0.
      Check P 0 p.
      admit.
    - Check IH : forall n0 : nat, n0 == n -> forall p : nat, P n p.
      Check Hnm : m == n.+1.
  Abort.
  
End Ubn.

(* END *)
