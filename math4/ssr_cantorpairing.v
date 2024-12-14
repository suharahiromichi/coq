(**
Cantor の対関数とその全単射性

# Lean

- https://lean-ja.github.io/lean-by-example/Tutorial/Exercise/CantorPairing.html


# MathComp
 *)
From mathcomp Require Import all_ssreflect.

(**
## sum 関数
*)
(** `0` から `n` までの自然数の和 *)
Fixpoint sum (n : nat) : nat :=
  match n with
  | 0 => 0
  | n.+1 => n.+1 + sum n
  end.

(** `sum n = 0` となることと `n = 0` は同値 *)
Lemma sum_zero_iff_zero {n : nat} : sum n = 0 <-> n = 0.
Proof.
  split.
  - by case: n.
  - by move=> ->.
Qed.

(**
## 対関数とその逆関数
 *)
(** Cantor の対関数 *)
Definition pair (x : nat * nat) : nat :=
  let (m, n) := x in sum (m + n) + m.

Lemma pair_zero (n : nat) : pair (0, 0) = 0.
Proof.
  done.
Qed.

(** カントールの対関数の逆関数 *)

Fixpoint unpair (x : nat) : nat * nat :=
  match x with
  | 0 => (0, 0)
  | x.+1 => let: (m, n) := unpair x in 
            if n == 0 then (0, m.+1) else (m.+1, n.-1)
  end.

Lemma unpair_zero : unpair 0 = (0, 0).
Proof.
  done.
Qed.

(**
## pair の全射性
*)
Lemma pair_unpair_eq_id (x : nat) : pair (unpair x) = x.
  (** `x` に対する帰納法を使う *)
  elim: x => //= x IHx.                  (** `x = 0` の場合は明らか *)
  (** `x` まで成り立つと仮定して `x + 1` でも成り立つことを示そう。 *)
  
  (** まず `unpair` の定義を展開する。 *)
  
  (** 見やすさのために `(m, n) := unpair x` とおく． *)
  pose m := (unpair x).1.
  pose n := (unpair x).2.
  rewrite (surjective_pairing (unpair x)).  
  rewrite -/m -/n.

  case: ifP.                                (* split_ifs *)
  (** `n = 0` の場合 *)
  - move/eqP => H.
    (* show pair (0, m + 1) = x + 1 *)

    (** `pair (0, m + 1) = x + 1` を示せばよい。 *)
    
    (** `pair` の定義を展開して、示すべきことを `sum` を使って書き直すと *)
    rewrite /pair /= addn0.
    (** `sum (m + 1) = x + 1` を示せば良いことが分かる。 *)
    suff : sum m.+1 = x.+1 by have -> : m.+1 + sum m = sum m.+1 by done.
    
    (** 帰納法の仮定の主張に対しても、 *)
    (** `pair` から `sum` に書き換えることができて、 *)

    rewrite /pair in IHx.
    rewrite (surjective_pairing (unpair x)) in IHx.
    rewrite -/m -/n in IHx.
    rewrite H in IHx.
    rewrite addn0 in IHx.
    have <- : m.+1 + sum m = sum m.+1 by done.
    rewrite addSn addnC.
    rewrite IHx.
    
    (** `sum m + m = x` であることが分かる。 *)
    done.
    
    (** `n ≠ 0` の場合 *)
    (** `pair (m + 1, n - 1) = x + 1` を示せばよい。 *)
  - have H : pair (m.+1, n.-1) = x.+1.
    {
    (** `pair` の定義を展開して、示すべきことを `sum` を使って書き直すと *)
      rewrite /pair /=.
      (** `sum (m + n) + m = x` を示せば良いことが分かる。 *)
      have H2 : sum (m + n) + m = x by admit.
      
      (** 帰納法の仮定の主張に対しても、 *)
      (** `pair` から `sum` に書き換えることができて、 *)
      (** `sum (m + n) + m = x` が成り立つことが分かる。 *)

      

      replace ih : sum (m + n) + m = x := by
        sorry

          (** 従って示すべきことが言えた。 *)
      assumption
