(*
このファイルは削除予定です。

gkp_2_6_finite_calculus.v
gkp_2_6_fincal_ffact_rfact.v

をみてください。
*)

(**
下降階乗冪 と 上昇階乗冪（Pochhammer 記号）の差分、原始関数

2022_08_27 @suharahiromichi
*)
From mathcomp Require Import all_ssreflect.
From common Require Import ssromega.
Open Scope nat_scope.

(**
# 連続系

連続系において ``x^m`` は ``m * x^(m.-1)`` の原始関数である。
```
D(x^n) = n * x^(m-1)
```
*)

(**
# 離散系の差分

## 下降階乗冪の差分

``n^_m`` は ``m * n^_(m.-1)`` の原始関数である。

```
diff (fun x => x^_m) =1 fun x => m * x^_(m.-1)
```
*)
Locate "_ ^_ _".
Print falling_factorial.

Definition diff f := fun x => f x.+1 - f x.

Check ffactSS : forall n m : nat, n.+1 ^_ m.+1 = n.+1 * n ^_ m.
Check ffactnSr : forall n m : nat, n ^_ m.+1 = n ^_ m * (n - m).

Lemma diff_ffact' n m : m <= n ->
                        diff (fun x => x^_m.+1) n = m.+1 * n^_m.
                        (* (n.+1)^_(m.+1) - n^_(m.+1) = m.+1 * n^_m. *)

Proof.
  move=> H.
(**
左辺
= (n.+1)^_(m.+1)           - n^_(m.+1)
= n.+1 * n^_m              - n^_m * (n - m)
= n * n^_m  +   n^_m       - n^_m * n  +  n^_m * m
=               n^_m                   +  n^_m * m
=               n^_m  * (1 + m)
= (m.+1)*(n^_m)
= 右辺
*)
  rewrite /diff.
  rewrite ffactSS ffactnSr.
  rewrite mulSn mulnBr.
  rewrite subnBA.
  - rewrite [n ^_ m * n]mulnC.
    rewrite addnAC.
    rewrite -addnBA // subnn addn0.
    rewrite -mulnS mulnC.
    done.
  - by apply: leq_mul.
Qed.

Lemma diff_ffact n m : m <= n ->
                       diff (falling_factorial ^~ m) n = m * n^_m.-1.
(* diff (fun x => ffact_rec x m) n = m * n^_m.-1. *)
(* diff (fun x => x^_m) n = m * n^_m.-1. *)
(* (n.+1)^_m - n^_m = m * n^_(m.-1). *)
Proof.
(**
左辺
= (n.+1)^_m                - n^_m
= n.+1 * n^_(m.-1)         - n^_(m.-1) * (n - m + 1)
= n * n^_(m.-1) + n^(m.-1) - n^_(m.-1) * n + n^_(m.-1) * m + n^_(m.-1) * n
=                                            n^_(m.-1) * m
= m * n^_(m.-1)
= 右辺
*)
  case: m => //= m H.
  apply: diff_ffact'.
  by ssromega.
Qed.

(**
## 上昇階乗冪の差分

``n^^m`` は ``m * (n.+1)^^(m.-1)`` の原始関数である。

```
diff n^^m =  m * (n.+1)^^(m.-1)
```
*)
Fixpoint rfact_rec n m := if m is m'.+1 then n * rfact_rec n.+1 m' else 1.
Definition rising_factorial := nosimpl rfact_rec.

Notation "n ^^ m" := (rising_factorial n m)
(at level 30, right associativity).


Section LEMMAS1.
  Lemma rfactn0 n : n ^^ 0 = 1. Proof. by []. Qed.

  Lemma rfact0n m : 0 ^^ m = (m == 0). Proof. by case: m. Qed.

  Lemma rfactnS n m : n ^^ m.+1 = n * n.+1 ^^ m. Proof. by []. Qed.

  Lemma rfactn1 n : n ^^ 1 = n. Proof. exact: muln1. Qed.

  Lemma rfactSS n m : n.+1 ^^ m.+1 = n.+1 ^^ m * (n + m.+1).
  Proof.
  Admitted.

  Lemma rfactnSr n m : n ^^ m.+1 = n * n.+1 ^^m.
  Proof.
  Admitted.
End LEMMAS1.


Lemma diff_rfact' m n : m <= n ->
                        diff (fun x => x^^m.+1) n = m.+1 * (n.+1)^^m.
Proof.
  rewrite /diff.
  move=> H.
(**
左辺
= (n.+1)^^(m.+1)                            - n^^(m.+1)
= (n.+1)^^m * (n + m.+1)                    - n * (n.+1)^^m
= (n.+1)^^m * n + (n.+1)^^m * m.+1          - n * (n.+1)^^m
=                 (n.+1)^^m * m.+1
= 右辺
*)  
  rewrite rfactSS rfactnSr.
  rewrite mulnDr.
  rewrite addnC.
  rewrite -subnBA.
  - rewrite [n.+1 ^^ m * n]mulnC.
    rewrite subnn subn0.
    rewrite mulnC.
    done.
  - by ssromega.
Qed.

Lemma diff_rfact m n : m <= n ->
                       diff (fun x => x^^m) n = m * (n.+1)^^(m.-1).
Proof.
  rewrite /diff.
  case: m => //= m H.
  Check diff_rfact'.
  apply: diff_rfact'.
  by ssromega.
Qed.


(**
# 差分・和分の基本公式 : 微積分の基本公式のアナロジー

 Σ a を計算することは a n = b n+1 - b n となる数列 b が既知であれば,
 b の差を求めることである

 積分計算とのアナロジーで b を a の原始関数と言ってもよいでしょう ...
 F'(x) = f(x) のとき ∫ f(x)dx = F(x_max) - F(x_min)
 総和の場合は
 b n+1 - b n = a n のとき Σ a = b n+1 - b 0
 *)

(* b はモノトーンである。 *)
Lemma test' b n : b n <= b n.+1.
Proof.
Admitted.

Lemma test2' b m n : m <= n -> b m <= b n.
Proof.
Admitted.

Theorem sum_diff' (a b : nat -> nat) (n : nat) :
  diff b =1 a ->                       (* b は a の原始関数である。 *)
  \sum_(0 <= i < n.+1) a i = b n.+1 - b O.
Proof.
  rewrite /diff.
  elim: n => [|n IHn] Hsub.
  - rewrite big_nat1.
    by rewrite Hsub.
  - rewrite big_nat_recr //.
    Check IHn Hsub.
    rewrite (IHn Hsub) -Hsub /=.
    rewrite addnBA; try apply: test'.
    rewrite [b n.+1 - b 0 + b n.+2]addnC -subnBA; try apply: leq_subr.
    f_equal.
    rewrite subKn //.
    by apply: test2'.
Qed.

Lemma test b n : b n <= b n.+1.
Proof.
Admitted.

Lemma test2 (b : nat -> nat -> nat) n1 n2 m : n1 <= n2 -> b n1 m <= b n2 m.
Proof.
Admitted.


Theorem sum_diff'' (a b : nat -> nat -> nat) (n m : nat) :
  diff (b ^~ m) n = a n m ->           (* b は a の原始関数である。 *)
  \sum_(0 <= i < n.+1) a i m = b n.+1 m - b O m.
Proof.
  rewrite /diff.
  elim: n m => [|n IHn] m Hsub.
  - rewrite big_nat1.
    by rewrite Hsub.
  - rewrite big_nat_recr //=.
    rewrite (IHn m).
    + rewrite -Hsub /=.
      rewrite addnBA; try apply: test2 => //=.
      rewrite [b n.+1 m - b 0 m + b n.+2 m]addnC -subnBA; try apply: leq_subr.
      f_equal.
      rewrite subKn //.
      by apply: test2.
    + 
Admitted.

(*
diff (b ^~ m) =1 a ^~ m -> とすると証明できるが、使った先で、
nとmの範囲が指定できなくなる。
*)
Theorem sum_diff (a b : nat -> nat -> nat) (n m : nat) :
  diff (b ^~ m) n = a n m ->           (* b は a の原始関数である。 *)
  \sum_(0 <= i < n.+1) a i m = b n.+1 m - b O m.
Proof.
  rewrite /diff.
  elim: m {-2}m (leqnn m).
  - move=> m Hm H.
    rewrite leqn0 in Hm.
    move/eqP in Hm.
    subst.
    admit.
  - move=> n' IHm m H1 H2.
    rewrite IHm //=.
Admitted.

Lemma sum_ffact'' m n : m <= n -> \sum_(0 <= i < n.+1) m * i^_m.-1 = n.+1^_m - 0^_m.
Proof.
  rewrite /diff.
  move=> H.
  Check sum_diff'' (fun i m => m * i ^_ m.-1) falling_factorial n m.
  apply: (sum_diff'' (fun i m => m * i ^_ m.-1) falling_factorial n m).
  by rewrite -diff_ffact //=.
Qed.

(* END *)

(*
Theorem sum_diff (a b : nat -> nat -> nat) (n m : nat) :
  (* diff (b ^~ m) n = a n m ->           (* b は a の原始関数である。 *) *)
  diff (b ^~ m) =1 a ^~ m ->           (* b は a の原始関数である。 *)
  \sum_(0 <= i < n.+1) a i m = b n.+1 m - b O m.
Proof.
  rewrite /diff.
  elim: n m => [|n IHn] m Hsub.
  - rewrite big_nat1.
    by rewrite Hsub.
  - rewrite big_nat_recr //=.
    rewrite (IHn m Hsub) -Hsub /=.
    rewrite addnBA; try apply: test2 => //=.
    rewrite [b n.+1 m - b 0 m + b n.+2 m]addnC -subnBA; try apply: leq_subr.
    f_equal.
    rewrite subKn //.
    by apply: test2.
Qed.

Lemma sum_ffact m n : m <= n -> \sum_(0 <= i < n.+1) m * i^_m.-1 = n.+1^_m - 0^_m.
Proof.
  rewrite /diff.
  move=> H.
  Check sum_diff (fun i m => m * i ^_ m.-1) falling_factorial n m.
  apply: (sum_diff (fun i m => m * i ^_ m.-1) falling_factorial n m).
  move=> n'.
  apply: diff_ffact.
Admitted.

*)
