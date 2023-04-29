(**
フィボナッチ数の一般項
========================

@suharahiromichi

2020/07/14

2023/04/30 algebra tactics を使用する。
*)

From mathcomp Require Import all_ssreflect.
From mathcomp Require Import all_algebra.
From mathcomp Require Import ring.          (* field, ring *)
Require Import Recdef.                      (* Function コマンド *)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(**
# はじめに

フィボナッチ ffibonacci 数列の一般項を証明します。フィボナッチ数列の一般項は、

$$ F_n = \frac{1}{\sqrt 5}\left[
\left(\frac{1 + \sqrt 5}{2}\right)^n -
\left(\frac{1 - \sqrt 5}{2}\right)^n
\right] $$

で知られていますが、

$ x^2 - x - 1 = 0 $ の2解を φとψとした場合、次の様に書くことができます。

$$ F_n = \frac{\phi^n - \psi^n}{\phi - \psi} $$

これは、xが上記の方程式の解のとき、$ x^2 = x + 1 $ なので、

$$ x^{n+2} = x^{n+1} + x^n $$

から、nを数列のインデックスとすると、
フィボナッチ数の主な定義である「直前のふたつの数の和」という性質を満たします。

この性質は、2解の線形和 $ a \phi^n + b \psi^n $ でも保たれるので、
漸化式の基底の部分の $ F_0 = 0 $ と $ F_1 = 1 $ を満たすように a と b を選ぶと、

$$ a = - b = \frac{1}{\phi - \psi} $$ になるからです。

$ F_0 = 0 = a + b $ から $ a = - b $ また、
$ F_1 = 1 = a \phi + b \psi $ から $ a = \frac{1}{\phi - \psi} $ です。


φとψおよび、それで定義されたフィボナッチ数の一般項の型は実数になりますが、
ここでは、それを抽象的な体、正確には ``F : fieldType`` である ``F`` 型であるとします。

そうすることで、実数という具体的な型を定義せずに、
フィボナッチ数の一般項と、漸化式で定義されたフィボナッチ数とが、
一致することを証明したいと思います。
*)

(**
# 諸設定
*)
Import GRing.Theory.         (* mulrA などを使えるようにする。 *)
Import Num.Theory.           (* unitf_gt0 などを使えるようにする。 *)
Import intZmod.              (* addz など *)
Import intRing.              (* mulz など *)
Open Scope ring_scope.       (* %R を省略時解釈とする。 *)

(**
# 漸化式の定義

最初に、フィボナッチ数列の漸化式を再帰関数として定義します。
のちの証明で、functional induction コマンドを使って、
フィボナッチ数の定義に基づく帰納法（カスタムインダクション）を使いたいので、
Fixpoint コマンドではなく Function コマンドを使って定義します。これにより、
そのカスタムインダクションのための帰納法の原理 ``fibn_ind`` が生成されます。


上記の設定の ``ring_scope``で、四則演算子の省略時解釈を環にしているので、
この定義の全体を自然数で計算するように、``(・)%N`` で囲みます。
そうしないと、``fibn_ind`` が生成されないようです。
 *)
Section DEFN.
  Function fibn (n : nat) : nat :=
    (match n with
    | 0 => 0
    | 1 => 1
    | (m.+1 as pn).+1 => fibn m + fibn pn   (* fib n.-2 + fib n.-1 *)
    end)%N.
  
  Check fibn_ind.   (* フィボナッチ数の定義に基づく帰納法が成り立つ。 *)
End DEFN.

(**
# 一般項の定義

最初に説明したように、φとψを以下のように定義します。φは黄金数です。

- 可換体の性質をもつ（ジェネリックな）型 Fを定義する。

- φとψ は、F型とする。

- $ x^2 - x - 1 = 0 $ の2解（重解ではない）を φとψとする。


ついで、φとψを使って、フィボナッチ数の一般項を定義します。これもF型となります。
なお、フィボナッチ数列のインデックスは、これまでとおり自然数です。
 *)
Section DEFR.
  Variable F : fieldType.
  Variable g h : F.
  
  Axiom g2__g_1 : g^2 = g + 1.        (* x^2 - x - 1 = 0 の解である。 *)
  Axiom h2__h_1 : h^2 = h + 1.        (* x^2 - x - 1 = 0 の解である。 *)
  Axiom neq_gh : g != h.              (* 重解ではない。 *)

  Definition fibf (n : nat) : F := (g^n - h^n) / (g - h).
  
(**
# 補題

公理 ``g != h`` から、分母に出現する ``g - h != 0`` を求めておきます。
 *)
  Lemma g_h__n0 : g - h != 0.
  Proof.
    apply/eqP.
    Check subr0_eq : forall (V : zmodType) (x y : V), x - y = 0 -> x = y.
    move/subr0_eq/eqP.
    apply/negP.
    by rewrite neq_gh.
  Qed.
  
(**
# 定理

functional induction コマンドを使って、(fibn n) についての帰納法をおこないす。

左辺は自然数、右辺は体なので、左辺を ring_scope に変換します。
 *)
  Lemma fibn_fibf (n : nat) : (fibn n)%:R = fibf n.
  Proof.
    rewrite /fibf.
    functional induction (fibn n).
    (* 0%:R = (g ^ 0 - h ^ 0) / (g - h) *)
    - field.
      by rewrite g_h__n0.
    (* 1%:R = (g ^ 1 - h ^ 1) / (g - h) *)
    - field.
      by rewrite g_h__n0.
      
    (* 
  IHn0 : (fibn m)%:R = (g ^ m - h ^ m) / (g - h)
  IHn1 : (fibn m.+1)%:R = (g ^ m.+1 - h ^ m.+1) / (g - h)
  ============================
  (fibn m + fibn m.+1)%:R = (g ^ m.+2 - h ^ m.+2) / (g - h)
     *)
    (* 左辺の分母を m乗 と m+1乗の 項からなる式にします。 *)
    - have -> : g ^ m.+2 - h ^ m.+2 = g ^ m.+1 + g ^ m - h ^ m.+1 - h ^ m.
      rewrite -add2n 2!exprzD_nat g2__g_1 h2__h_1.
      rewrite 2![(_ + 1) * _ ^ m]mulrDl.
      rewrite 2!mul1r.
      rewrite -2![_ * _ ^ m]exprSz.
      ring.
      
      (* (fibn m + fibn m.+1)%:R = (g ^ m.+1 + g ^ m - h ^ m.+1 - h ^ m) / (g - h) *)
      (* 右辺の分母を移項します。 *)
      have -> : g ^ m.+1 + g ^ m - h ^ m.+1 - h ^ m = g ^ m - h ^ m + (g ^ m.+1 - h ^ m.+1).
      ring.
      
      (* (fibn m + fibn m.+1)%:R = ((g ^ m - h ^ m) + (g ^ m.+1 - h ^ m.+1)) / (g - h) *)
      rewrite mulrDl.                       (* 割算を分配する。 *)
      rewrite -IHn0 -IHn1.
      by field.
  Qed.
End DEFR.

(* END *)
