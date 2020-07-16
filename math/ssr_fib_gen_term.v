(**
フィボナッチ数の一般項
========================

@suharahiromichi

2020/07/14
*)

From mathcomp Require Import all_ssreflect.
From mathcomp Require Import all_algebra.
Require Import ssromega.                    (* ssromega タクティク *)
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
*)


(**
# 漸化式の定義
 *)
Section DEFN.
  Function fibn (n : nat) : nat :=
    match n with
    | 0 => 0
    | 1 => 1
    | (m.+1 as pn).+1 => fibn m + fibn pn (* fibn n.-2 + fibn n.-1 *)
    end.
  Check fibn_ind.
End DEFN.

(**
# 一般項の定義
 *)
Import GRing.Theory.         (* mulrA などを使えるようにする。 *)
Import Num.Theory.           (* unitf_gt0 などを使えるようにする。 *)
Import intZmod.              (* addz など *)
Import intRing.              (* mulz など *)
Open Scope ring_scope.       (* 環の四則演算を使えるようにする。 *)

Section DEFR.
  Variable R : fieldType.                   (* unitRingType. *)
  Variable g h : R.

  Definition fibr (n : nat) := (g^n - h^n) / (g - h).
  Check fibr.
  
  Axiom sol_g : g^2 = g + 1.        (* x^2 - x - 1 = 0 の解である。 *)
  Axiom sol_h : h^2 = h + 1.        (* x^2 - x - 1 = 0 の解である。 *)
  Axiom neq_gh : g != h.            (* 重解ではない。 *)

(**
# 補題
 *)
  Lemma test2 : (g - h) / (g - h) = 1.
  Proof.
    Check divff : forall (F : fieldType) (x : F), x != 0 -> x / x = 1.
    (* ここで、g - h が体でなければなならい。 *)
    rewrite divff.
    - done.                                 (* 1 = 1 *)
    - apply/eqP.
      Check (@subr0_eq R g h).
      move/subr0_eq.
        by apply/eqP/neq_gh.
  Qed.
  
  Lemma test (n : int) : n - n = 0%:Z.      (* notu *)
  Proof.
    apply/eqP.
    rewrite subr_eq0.
    done.
  Qed.
  
(**
# 定理
 *)
  Lemma fibn_fibr (n : nat) : (fibn n)%:R = fibr n.
  Proof.
    rewrite /fibr.
    functional induction (fibn n).
    - rewrite 2!expr0z.
      rewrite addrN.
        by rewrite mul0r.                   (* 割り算は掛け算 *)

    - rewrite 2!expr1z.
      rewrite divrr; first done.
        by rewrite unitrE test2.
      
    - rewrite -add2n 2!exprzD_nat sol_g sol_h.
      rewrite 2![(_ + 1) * _ ^ m]mulrDl.
      rewrite 2!mul1r.
      rewrite -2![_ * _ ^ m]exprSz.
      rewrite opprD addrA.
      
      rewrite ?addrA.
      rewrite [_ + (- h ^ m.+1)]addrC.
      rewrite ?addrA.
      rewrite [(- h ^ m.+1) + g ^ m.+1]addrC.
      rewrite -addrA addrC.
      
      rewrite mulrDl.
      rewrite -IHn0 -IHn1.
      rewrite -natrD.
      done.
  Qed.
End DEFR.

(* END *)

