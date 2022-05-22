(**
コンピュータの数学 6.6 p.267 整数のフィボナッチ数
=====

2022_05_21 @suharahiromichi
*)
(**
# はじめに

フィボナッチ数の定義を負数に拡張する。自然数 ``n`` に対して、

```F_(-n) = (-1)^(n - 1)・F_n```

とします。たとえば、

```
F_4 = 3
F_3 = 2
F_2 = 1
F_1 = 1
F_0 = 0
F_(-1) = 1
F_(-2) = -1
F_(-3) = 2
F_(-4) = -3
```

これがフィボナッチ数の定義を満たすことを証明することが主題です。

```F_i + F_(i + 1) = F_(i + 2)```

MathComp のalgebraパッケージを使って、全部で250行あります。
 *)
From mathcomp Require Import all_ssreflect.
From mathcomp Require Import all_algebra.

Import GRing.Theory.         (* mulrA などを使えるようにする。 *)
Import Num.Theory.           (* unitf_gt0 などを使えるようにする。 *)
Import intZmod.              (* addz など *)
Import intRing.              (* mulz など *)
Open Scope ring_scope.       (* 環の四則演算を使えるようにする。 *)

Section INTFIB.
(**
# フィボナッチ数

- 自然数のフィボナッチ数の定義
*)
  Fixpoint fibn (n : nat) : nat :=
    match n with
    | 0 => 0
    | 1 => 1
    | (m.+1 as pn).+1 => fibn m + fibn pn (* fibn n.-2 + fibn n.-1 *)
    end.

(**
- 整数に拡張したフィボナッチ数の式

これが今回の証明の対象となる式です。
*)  
  Definition fibz (i : int) : int :=
    let n := `|i|%N in
    if 0 <= i then (fibn n)%:Z
    else (-1)^n.-1 * (fibn n)%:Z.
  
(**
別な式。使っていません。
*)
  Definition fibz' (i : int) : int :=
    match i with
    | Posz n => fibn n
    | Negz n => (-1)^n * (fibn n.+1)%:Z
    end.

(**
# 整数引数のフィボナッチ数と自然数引数のフィボナッチ数の関係

```
F_n  =   F_n     ただし n は正
F_-n = - F_n     ただし n は偶数
F_-n =   F_n     ただし n は奇数
```
 *)
  
(**
``-1`` の累乗についての補題を証明しておきます。
*)
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

(**
## ``n`` が正数の場合

``n`` が0以上の正数の場合は、
整数引数のフィボナッチ数と自然数引数のフィボナッチ数は同じである。
 *)
  Lemma fibz_pos_n (n : nat) : fibz n%:Z = fibn n.
  Proof.
    done.
  Qed.

(**
## ``-2n`` 負の偶数の場合

``n`` が ``0`` 以上の負の偶数の場合は、
整数引数のフィボナッチ数は、絶対値のフィボナッチ数にマイナスを掛けたものである。

まず、``n = 2(n + 1)`` として証明します。
 *)
  Lemma fibz_neg_even' (n : nat) : fibz (- n.*2.+2%:Z) = - (fibn n.*2.+2)%:Z.
  Proof.
    rewrite /fibz.
    have -> : 0 <= - n.*2.+2%:Z = false by done.
    have -> : `|- n.*2.+2%:Z|%N.-1 = n.*2.+1 by done.
    rewrite expr_1_odd mulN1r.
    done.
  Qed.
  
(**
``n = 0`` と ``n = n + 1`` に場合わけして証明します。``n = 0`` は自明です。
*)
  Lemma fibz_neg_even (n : nat) : fibz (- n.*2%:Z) = - (fibn n.*2)%:Z.
  Proof.
    case: n => // n.                        (* n = 0 の場合 *)
    have -> : n.+1.*2 = n.*2.+2 by done.
    by rewrite fibz_neg_even'.
  Qed.
  
(**
## ``-(2n + 1)`` 負の奇数の場合

``n`` が ``0`` 以上の負の奇数の場合は、
整数引数のフィボナッチ数は、絶対値のフィボナッチ数と同じである。
 *)
  Lemma fibz_neg_odd (n : nat) : fibz (- n.*2.+1%:Z) = fibn n.*2.+1.
  Proof.
    rewrite /fibz.
    have -> : 0 <= - n.*2.+1%:Z = false by done.
    have -> : `|- n.*2.+1%:Z|%N = n.*2.+1 by done.
    rewrite -pred_Sn.
    rewrite expr_1_even mul1r.
    done.
  Qed.
  
(**
# 場合分けのための補題

- 整数と正数と負数に分けられる。
*)
  Lemma absz_total (i : int) : (i = `| i |%N%:Z) \/ (i = - `| i |%N%:Z).
  Proof.
    case: i => n.
    - by left.
    - rewrite /absz.
      right.
      by case: n.
  Qed.

(**
- 自然数は偶数と奇数に分けられる。
*)
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
# いくつかの補題
*)
(**
- 定数の足し算
*)
  Lemma addzn1 (m : nat) : m%:Z + 1  = m.+1.
  Proof.
    rewrite -[in RHS]addn1.
    done.
  Qed.
  
  Lemma addzn2 (m : nat) : m%:Z + 2  = m.+2.
  Proof.
    rewrite -[in RHS]addn2.
    done.
  Qed.
  
  (* これは成り立たない。m = 0 なら -1 = 0 *)
  Lemma subzn1 (m : nat) : m%:Z - 1  = m.-1%:Z.
  Proof.
  Abort.
  
(**
- 移項する補題
*)
  Lemma transpos (a b c : int) : a = c + b -> a - b = c.
  Proof.
    move/eqP => H.
    apply/eqP.
    by rewrite subr_eq.
  Qed.
  
(**
# 証明の本題
*)
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

        (* 上書きしないように、右から書き換える。 *)
        (* -2n *)
        have -> : - n.+1.*2%:Z + 2 = - n.*2%:Z
          by rewrite doubleS addrC -opprB -addzn2;
          congr (- _); apply: transpos.
        (* -(2n + 1) *)
        have -> : - n.+1.*2%:Z + 1 = - n.*2.+1%:Z
          by rewrite -addzn1;                          (* 右辺 *)
          rewrite doubleS addrC -opprB -addzn2 -addrA. (* 左辺 *)
        (* -(2n + 2) *)
        
        (* fibz (- n+1.*2) + fibz (- n.*2.+1) = fibz (- n.*2) *)
        rewrite 2!fibz_neg_even.
        rewrite fibz_neg_odd.
        (* - fibn (n.+1).*2 + fibn n.*2.+1 = - fibn n.*2 *)
        have -> : n.+1.*2 = n.*2.+2 by done.
      
        (* - fibn n.*2.+2 + fibn n.*2.+1 = - fibn n.*2 *)
        apply/eqP.
        rewrite -addr_eq0 -addrA -addrC subr_eq add0r addrC.
        (* fibn n.*2 + fibn n.*2.+1 = fibn n.*2.+2 *)
        done.
        
      + pose n := `|i|./2.
        rewrite -/n.
        (* fibz (- n.*2.+1) + fibz (- n.*2.+1 + 1) = fibz (- n.*2.+1 + 2) *)

        (* case がないと、-(2n + 1), - (2n), -(2n - 1) になってしまう。
           n.*2 しているので、n.+1 になると、ふたつずれる。 *)
        case: n => //= n.
        (* fibz (- (n.+1).*2.+1) + fibz (- (n.+1).*2.+1 + 1) = fibz (- (n.+1).*2.+1 + 2) *)
        
        (* 上書きしないように、右から書き換える。 *)
        (* -(2n + 1) *)
        have -> : - n.+1.*2.+1%:Z + 2 = - n.*2.+1%:Z
          by rewrite doubleS addrC -opprB.
        (* -(2n + 2) *)
        have -> : - n.+1.*2.+1%:Z + 1 = - n.+1.*2%:Z
          by rewrite doubleS addrC -opprB.
        (* -(2n + 3) *)
        
        rewrite fibz_neg_even.
        rewrite 2!fibz_neg_odd.
        have -> : n.+1.*2.+1 = n.*2.+3 by done.
        have -> : n.+1.*2 = n.*2.+2 by done.
        
        (* fibn n.*2.+3 - fibn n.*2.+2 = fibn n.*2.+1 *)
        apply/eqP.
        rewrite subr_eq.
        (* fibn n.*2.+3 == fibn n.*2.+1 + fibn n.*2.+2 *)
        done.
  Qed.
  
End INTFIB.

(**
# 使わなかった補題
*)

Section OPTION.

(**
## 整数引数のフィボナッチ数の関係
*)  
  Lemma fibz_neg_odd_z (n : nat) : fibz (- n.*2.+1%:Z) = fibz n.*2.+1%:Z.
  Proof.
    rewrite fibz_neg_odd.
    rewrite /fibz.
    have -> : 0 <= n.*2.+1%:Z = true by done.
    have -> : `|n.*2.+1|%N = n.*2.+1 by done.
    done.
  Qed.
  
  Lemma fibz_neg_even_z (n : nat) : fibz (- n.*2%:Z) = - (fibz n.*2).
  Proof.
    rewrite fibz_neg_even.
    rewrite /fibz.
    have -> : 0 <= n.*2%:Z = true by done.
    have -> : `|n.*2%:Z|%N = n.*2 by done.
    done.
  Qed.

(**
## ``-(2n - 1)`` 負の奇数の場合
*)
  Lemma fibz_neg_odd' (n : nat) : fibz (- n.*2.-1%:Z) = fibn n.*2.-1.
  Proof.
    case: n => // n.                        (* n = 0 の場合 *)
    have -> : - n.+1.*2.-1%:Z = - n.*2.+1%:Z by done.
    have -> : n.+1.*2.-1 = n.*2.+1 by done.
    rewrite fibz_neg_odd.
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

End OPTION.

Check eqz_nat : forall m n : nat, (m == n :> int) = (m == n).
Check addr_eq0 : forall [V : zmodType] (x y : V), (x + y == 0) = (x == - y).
Check subr_eq0 : forall (V : zmodType) (x y : V), (x - y == 0) = (x == y).
Check subr_eq : forall (V : zmodType) (x y z : V), (x - z == y) = (x == y + z).


(* END *)
