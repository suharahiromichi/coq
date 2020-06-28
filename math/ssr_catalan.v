(**
カタラン数をCoqで語らん
========================

@suharahiromichi

2020/06/28
*)

(**
# はじめに

Coq/MathComp には binomial.v というパッケージがあって、
二項係数（順列・組合せの「組合せ」）の定義と
基本的ないくつかの補題が証明されています。これを使ってなにか証明してみましょう。

二項係数を使って定義される、カタラン数 (Catalan Number) というものがあるります。
nが自然数のとき、以下で定義されます。

```math

c_n =
\frac{1}{n + 1}\dbinom{2 n}{n}
```

これの意味については、「カタラン数を語らん」としているサイト（文献[1]）に譲ります。

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
二項係数 $\dbinom{n}{m}$ を ``C(n, m)`` で、
``n | m`` で「m は n で割り切れる」を示す（除数のほうが前）ことにします。
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
# ``n! = n * (n - 1)!`` 、ただし ``0 < n``

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

さらに、階乗についての補題を証明します。
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

  Lemma test5 n : 0 < n -> (n * n.-1`! * n`!) %| n.*2`!.
  Proof.
    move=> H.
    rewrite -fact_pred; last done.
    rewrite divn_fact_mul_add_fact; first done.
      (* n + n = n.*2 *)
      by rewrite -addnn.
  Qed.

  Lemma test6 n : 0 < n -> n.+1 * n`! * n.-1`! %| n.*2`!.
  Proof.
    move=> H.
    rewrite -[n.+1 * n`!]fact_pred; last done.
    apply: divn_fact_mul_add_fact.
    (* n.+1 + n.-1 = n.*2 *)
    have -> : n.+1 + n.-1 = n + n by ssromega.
    by rewrite -addnn.
(*
    rewrite -subn1.
    rewrite addnBA; last done.
    rewrite -addn1.
    rewrite -addnAC.
    rewrite addn1.
    rewrite subn1.
    Search _.+1.-1.
    rewrite -[(n + n).+1.-1]pred_Sn.
  *)
    done.
  Qed.

(**
カタラン数の定義 : ``c_n = (1 / (n + 1)) * 'C(2*n, n)`` に対して、
   
```c_n = 'C(2*n, n) - 'C(2*n, n - 1)```

が成り立つ。ここで 'C(n, m) は二項係数 nCm。

```(1/(n+1)) * 'C(2*n, n) = 'C(2*n, n) - 'C(2*n, n - 1)```

を変形した、

```n * 'C(n*2, n) = (n+1) * 'C(n*2, n+1)```

を証明する。
*)  

  
(**
方針
左辺と右辺それぞれに、
*)
  Check muln_divA : forall d m n : nat, d %| n -> m * (n %/ d) = (m * n) %/ d.
(**
で、(N * X) %/ (N * Y) のかたちにする。
*)    
  Check divnMl : forall p m d : nat, 0 < p -> (p * m) %/ (p * d) = m %/ d.
(**
で、それを消す。
*)    

 Theorem catalan_rel n : 0 < n -> n * 'C(n.*2, n) = n.+1 * 'C(n.*2, n.+1).
  Proof.
    move=> Hn.
    
    (* LHS *)
    rewrite bin_factd; last by rewrite double_gt0.
    have -> : n.*2 - n = n by rewrite -addnn; ssromega.
    rewrite {1}[in n`! * n`!]fact_pred; last done.
    (* (n * X) %/ (n * Y) にする。 *)
    rewrite muln_divA; last by rewrite test5.
    rewrite -mulnA divnMl; last done.
    rewrite [(n.-1)`! * n`!]mulnC.
    
    (* RHS *)
    rewrite bin_factd; last by rewrite double_gt0.
    have -> : n.*2 - n.+1 = n.-1 by rewrite -addnn; ssromega.
    rewrite factS.
    (* (n.+1 * X) %/ (n.+1 * Y) にする。 *)
    rewrite muln_divA; last by rewrite test6.
    rewrite -mulnA divnMl; last done.
    done.
  Qed.

End LEMMAS.

(**
# 文献

[1] カタラン数を語らん、https://www.google.com/search?&q="カタラン数を語らん"
*)
  
(**
# おまけ

Catalan Number カタラン数
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

(* END *)
