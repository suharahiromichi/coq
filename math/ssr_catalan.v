(**
(Coqで)カタラン数を語らん
========================

@suharahiromichi

2020/06/28
*)

(**
# はじめに

Coq/MathComp には binomial.v というパッケージがあって、
二項係数（順列・組合せの「組合せ」）の定義と
基本的ないくつかの補題が証明されています。これを使ってなにか証明してみましょう。

二項係数を使って定義される、カタラン数 (Catalan Number) というものがあるります
（文献[1]）。
nが自然数のとき、以下で定義されます。

```math

c_n =
\frac{1}{n + 1}\dbinom{2 n}{n}
```

これの意味については、「カタラン数を語らん」としているサイト（文献[2]）に譲ります。

ここでは、n番めのカタラン数について、

```math

c_n = \dbinom{2 n}{n} - \dbinom{2 n}{n - 1}、ただし 0 \lt n
```

が成り立つことを証明したい思います。実際には、上記ふたつの式を整理した、

```math

n \dbinom{2 n}{n} = (n + 1) \dbinom{2 n}{n - 1}、ただし 0 \lt n

```

を証明します。
*)

(**
以下では、``n``、``m`` を（0以上の）自然数とします。また、MathCompの表記にあわせて、
二項係数 $\dbinom{n}{m}$ を ``C(n, m)`` で、また、
「m は n で割り切れる」を``n | m`` で示します（除数のほうが前）。
*)

From mathcomp Require Import all_ssreflect.
Require Import ssromega.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(**
# 補題
*)
Section LEMMAS.

(**
## ``n! = n * (n - 1)!`` 、ただし ``0 < n``

階乗の定義から自明ですが、MathComp では ``(n + 1) = (n + 1) * n!``
でしか証明されていないので、証明しておきます。
*)  
  Lemma fact_pred n : 0 < n -> n`! = n * n.-1`!.
  Proof.
    move=> Hn.
    have H := factS n.-1.
    rewrite prednK in H; last done.
    done.
  Qed.
  
(**
## ``n! * m! | (n + m)!``

階乗の剰余についての補題を証明します。
ちょっと直観に反する補題ですが、二項係数の定義から導くことができます。
また、便利です。
*)  
  Lemma divn_fact_mul_add_fact (n m p : nat) : n + m = p -> n`! * m`! %| p`!.
  Proof.
    move=> <-.
    have H : 'C(n + m, m) * (n`! * m`!) = (n + m)`!.
    - rewrite -(@bin_fact (n + m) m); last by rewrite leq_addl.
      rewrite -[n + m - m]addnBA; last by rewrite leqnn.
        by rewrite subnn addn0 [m`! * n`!]mulnC.
    - rewrite -H.
      rewrite -{1}[n`! * m`!]mul1n.
        by apply: dvdn_mul.
  Qed.  

(**
次のふたつは、階乗の剰余の応用ですが、少し長くなるので、別に証明しておきます。
*)
  Lemma divn_n2_l n : 0 < n -> (n * n.-1`! * n`!) %| n.*2`!.
  Proof.
    move=> H.
    rewrite -[n * n.-1`!]fact_pred; last done.
    apply: divn_fact_mul_add_fact.
    rewrite -addnn.
    done.
  Qed.

  Lemma divn_n2_r n : 0 < n -> n.+1 * n`! * n.-1`! %| n.*2`!.
  Proof.
    move=> H.
    rewrite -[n.+1 * n`!]fact_pred; last done.
    apply: divn_fact_mul_add_fact.
    rewrite -addnn.
      by ssromega.
  Qed.

End LEMMAS.
  
Section TH.
(**
# 定理

証明の概略を示します。

(1) ``C(n, m) = n! / (m! * (n - m)!)`` を使って、二項係数を階乗の式に変換する。
すこし整理すると、

```math

n \frac{(2 n)!}{n (n-1)! n!} = (n+1) \frac{(2 n)!}{(n+1) n! (n-1)!}
```

が得られる。


(2) 補題``muln_divA``を使い、左辺は ``(n * □) / (n * ■)`` に変換する。また、
右辺は ``(n.+1 * ○) / (n.+1 * ●)`` に変換する。


```math

\frac{n (2 n)!}{n (n-1)! n!} = \frac{(n+1)(2 n)!}{(n+1) n! (n-1)!}
```

(3) 補題``divnMl``を使い、左辺から ``n``、右辺から ``n+1``を消す。

```math

\frac{(2 n)!}{(n-1)! n!} = \frac{(2 n)!}{n! (n-1)!}
```
*)
  Check muln_divA : forall d m n : nat, d %| n -> m * (n %/ d) = (m * n) %/ d.
  Check divnMl : forall p m d : nat, 0 < p -> (p * m) %/ (p * d) = m %/ d.

  Theorem catalan_rel n : 0 < n -> n * 'C(n.*2, n) = n.+1 * 'C(n.*2, n.+1).
  Proof.
    move=> Hn.
    
    (* LHS *)
    (* (1) *)
    rewrite bin_factd; last by rewrite double_gt0.
    have -> : n.*2 - n = n by rewrite -addnn; ssromega.
    rewrite {1}[in n`! * n`!]fact_pred; last done.
    (* (2) *)
    rewrite muln_divA; last by rewrite divn_n2_l.
    rewrite -mulnA divnMl; last done.
    rewrite [(n.-1)`! * n`!]mulnC.
    
    (* RHS *)
    (* (1) *)
    rewrite bin_factd; last by rewrite double_gt0.
    have -> : n.*2 - n.+1 = n.-1 by rewrite -addnn; ssromega.
    rewrite [n.+1`!]factS.
    (* (2) *)
    rewrite muln_divA; last by rewrite divn_n2_r.
    rewrite -mulnA divnMl; last done.
    
    done.
  Qed.

End TH.

(**
# おまけ

カタラン数には、漸化式を使った表現もあります。これが一致することを証明できるでしょうか。
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

(**
# 文献

[1] https://ja.wikipedia.org/wiki/カタラン数


[2] https://www.google.com/search?&q=カタラン数を語らん
*)

(* END *)
