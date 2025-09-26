(**
√2 が無理数

高校数学の美しい物語 ルート２が無理数であることの４通りの証明
- https://manabitimes.jp/math/1030

# 補題：

``2 * q^2 = p^2`` ならば p と q は互いに素ではない。

下記では、互いに素についての性質を使って証明しているが、
以下のように証明もできる。

まず n^2 が偶数なら n も偶数である。
これはnが奇数ならn^2が奇数であることの対偶である。

左辺は偶数なので、右辺の p^2 は偶数、よって p は偶数。
右辺は4の倍数なので、左辺の q^2 は2の倍数で偶数、よって q は偶数。
p も q も偶数なので、互いに素ではない。


# 有名な背理法をつかう証明

√2 が有理数と仮定する。ならば、
互いに素な自然数 p と q を使って、√2 = p / q とおける。
ゴールを両辺二乗して分母を払うと 2 * q^2 = p^2
ゴールに補題を適用すると、p と q は互いに素ではない。
矛盾なので、√2は有理数ではない。


# 素因数分解を用いた証明

√2 が無理数であるなら、
互いに素な自然数 p と q を使って、``p / q`` と表すことができない、
これの対偶を取ると、``√2 = p / q`` なら、p と q は互いに素ではない。
前提を両辺二乗して分母を払うと 2 * q^2 = p^2
前提に補題を適用すると、p と q は互いに素ではない。
よって、√2は無理数である。


# 名大のcoqの授業
see. ssr_root2_div0_ssralg.v

- https://www.math.nagoya-u.ac.jp/~garrigue/lecture/2020_AW/ssrcoq6.pdf
- https://gitlab.com/proofcafe/nu/-/blob/master/nu_ssrcoq6_3_root2.v

名大のcoqの授業でのの証明と似ているが、
主補題の証明に帰納法（整礎帰納法）を使わないことで、簡単であるといえる。
また、Standard Coq の Real を使用せず、MathComp の rcfType を使用した。
*)
From mathcomp Require Import all_ssreflect.
From mathcomp Require Import all_algebra.
From mathcomp Require Import ssrZ zify ring lra.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section Root2.
  
  Section Nat.
    (**
## 自然数の補題
     *)
    Lemma evenP n : reflect (exists m, n = m.*2) (~~ odd n).
    Proof.
      have -> : ~~ odd n = (2 %| n) by lia.
      apply: (iffP eqP) => [md0 | [k ->]]; last by rewrite -mul2n modnMr.
      exists (n %/ 2).
      lia.
    Qed.
    (* m * 2 にすると、even_not_coprime で展開される順番が変わり、done で終わらなくなる。 *)
    
    Lemma even_not_coprime p q : ~~ odd p -> ~~ odd q -> ~~ coprime p q.
    Proof.
      move/evenP => [p' ->].
      move/evenP => [q' ->].
      rewrite -!mul2n coprimeMl 2!coprimeMr.
      Check ~~ [&& coprime 2 2 && coprime 2 q', coprime p' 2 & coprime p' q'].
      done.
    Qed.
    
    Lemma two_p2_implies_not_coprime (p q : nat) :
      2 * q ^ 2 = p ^ 2 -> ~~ coprime p q.
    Proof.
      move=> H.
      have Hq_even : ~~ odd p by lia.           (* q が偶数である。 *)
      case: q H => [| q] H.
      (* p = 0 の場合 *)
      - rewrite /coprime gcdn0.
        lia.
      (* p != 0 の場合 *)
      - have Hp_even : ~~ odd q.+1 by lia.      (* p が偶数である。 *)
        by rewrite even_not_coprime.
    Qed.

    (* おまけ two_p2_implies_not_coprime の別証明。 *)
    (* coprime や gcd の補題を使わないようにする。 *)
    Lemma oddP n : reflect (exists m, n = m.*2.+1) (odd n).
    Proof.
      apply: (iffP idP) => [H | [m]].
      - exists n.-1./2.
        lia.
      - lia.
    Qed.
    
    Lemma even_sq__even n : ~~ odd (n^2) <-> ~~ odd n.
    Proof.
      split.
      - apply/contra => /oddP [m] Hn.
        apply/oddP.
        exists (m^2 + m).*2.
        lia.
      - case/evenP => m ->.
        lia.
    Qed.
    
    Lemma even_sq__evenE n : ~~ odd (n^2) = ~~ odd n.
    Proof.
      apply/idP/idP; by move/even_sq__even.
    Qed.
    
    Lemma evenE n m : 2 * n = m -> ~~ odd m.
    Proof.
      lia.
    Qed.
    
    Lemma evenE2 p q : ~~ odd p -> 2 * (q^2) = p^2 -> ~~ odd q.
    Proof.
      move=> Hp.
      have H : p = p./2.*2 by rewrite (even_halfK (Hp)).
      rewrite -even_sq__evenE in Hp.
      rewrite H -muln2 expnMn.
      have -> x : x * (2^2) = 2 * (x * 2) by lia.
      have H2n2 x y : 2 * x = 2 * y -> x = y by lia.
      move/H2n2.
      rewrite mulnC.
      by move/esym/evenE/even_sq__even.
    Qed.
    
    Lemma even_even_not_coprime p q : ~~ odd p -> ~~ odd q -> ~~ coprime p q.
    Proof.
      (* これは明らかに成り立つが、証明は odd や coprime (gcd) の定義に遡る必要がある。  *)
    Admitted.      
    
    Lemma two_p2_implies_not_coprime' (p q : nat) : 2 * q ^ 2 = p ^ 2 -> ~~ coprime p q.
    Proof.
      move=> H2qp.
      move: (H2qp) => Hp.
      move/evenE/even_sq__even in Hp.
      move: (Hp) => Hq.
      move/evenE2 in Hq.
      move: (Hq q) => {} Hq.
      move: (Hq H2qp) => {} Hq.
      by apply: even_even_not_coprime.
    Qed.
    (* ******************************** *)
    
    
  End Nat.
  
  Section Real.
    Open Scope ring_scope.
    Import GRing.                        (* natrM *)
    Import Num.Theory.                   (* sqr_sqrtr, eqr_nat など *)
    
    Variable R : rcfType.                   (* sqrt が計算できる型 *)
    
    Search "sqrt".
    Check Num.Theory.sqr_sqrtr : forall (R : rcfType) (a : R), 0 <= a -> Num.sqrt a ^+ 2 = a.
    
    (* R と nat の相互変換 *)
    Check eqr_nat R : forall m n : nat, (m%:R == n%:R) = (m == n).
    Check ler_nat R : forall m n : nat, (m%:R <= n%:R) = (m <= n)%N.
    Check ltr_nat R : forall m n : nat, (m%:R < n%:R) = (m < n)%N.
    
  (**
## x は無理数である。
   *)
    Definition irrational (x : R) : Prop := forall (p q : nat),
        q <> 0 -> coprime p q -> x <> p%:R / q%:R.
    
  (**
## 証明したいもの ``sqrt 2`` は無理数である。

√2 が無理数であるとは、
互いに素な自然数 p q を使って、
``p / q`` と表すことができない、ということである。
   *)
    Theorem irrational_sqrt_2 : irrational (Num.sqrt 2).
    Proof.
      move=> p q Hq Hco.
      move/negPn/negP in Hco.
(*
  Hq : q <> 0
  Hco : ~ ~~ coprime p q
  ============================
  Num.sqrt 2 <> p%:R / q%:R
*)
(*
      move=> Hrt.
      Check Logic.False.                    (* Goal *)
      apply: Hco.                           (* 対偶を取る。 *)
*)      
      apply: contra_not Hco => Hrt.         (* 対偶を取る。 *)
(**
対偶を取ると、
``p / q`` と表すことができるなら、
p q は互いに素ではない、ということになる。
*)
(*
  Hq : q <> 0
  Hrt : Num.sqrt 2 = p%:R / q%:R
  ============================
  ~~ coprime p q
*)
      apply: two_p2_implies_not_coprime.
      Check (2 * q ^ 2)%N = (p ^ 2)%N.
(**
``2 * q^2 = p^2`` なら p q は互いに素ではないので、それを証明する。
*)      
      apply/eqP.
      rewrite -(eqr_nat R) natrM.
      apply/eqP.
      rewrite -(@sqr_sqrtr R 2).
      
      Check Num.sqrt 2 ^+ 2 * (q ^ 2)%:R = (p ^ 2)%:R.
      - rewrite Hrt.
        field.
        rewrite (eqr_nat R q 0).
        lia.
        
      Check 0 <= 2.
      - auto.
      (*
      - move/eqP in Hq.
        rewrite -(eqr_nat R) in Hq.
        apply/negP.
        done.
       *)
    Qed.
    
  End Real.
End Root2.

(* END *)
