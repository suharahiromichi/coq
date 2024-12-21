(**
Cantor の対関数とその全単射性

- https://zenn.dev/leanja/articles/cantor_pairing

- https://lean-ja.github.io/lean-by-example/Tutorial/Exercise/CantorPairing.html
 *)

From mathcomp Require Import all_ssreflect.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(**
# ありそうで無い補題
*)
Lemma addn1_to_neq0 (m n : nat) : m = n.+1 -> m != 0.
Proof.
  rewrite -lt0n.
  move=> ->.
  by rewrite ltn0Sn.
Qed.

(**
# 対関数とその逆関数

## sum 関数

`0` から `n` までの自然数の和
 *)
Fixpoint sum (n : nat) : nat :=
  match n with
  | 0 => 0
  | n.+1 => n.+1 + sum n
  end.

(**
## 補題 `sum n = 0` となることと `n = 0` は同値
 *)
Lemma sum_zero_iff_zero {n : nat} : sum n = 0 <-> n = 0.
Proof.
  split.
  - by case: n.
  - by move=> ->.
Qed.

Lemma sum_zero_iff_zeroE {n : nat} : (sum n == 0) = (n == 0).
Proof.
  apply/idP/idP; move/eqP.
  - by case: n.
  - by move=> ->.
Qed.

(**
## Cantor の対関数 pair
 *)
Definition pair (x : nat * nat) : nat :=
  let (m, n) := x in sum (m + n) + m.

(*
Lemma pair_zero : pair (0, 0) = 0.
Proof. done. Qed.  
*)

Lemma pair_zero (m n : nat) : pair (m, n) = 0 <-> (m = 0 /\ n = 0).
Proof.
  split.
(*
  - rewrite /pair => /eqP.
    rewrite addn_eq0.
    case/andP => /eqP /sum_zero_iff_zero Hmn /eqP Hm.
    move: Hmn.
    by rewrite Hm add0n => ->.
*)
  - elim: m => //=.
    elim: n => //=.
  - by case=> -> ->.
Qed.

(**
## Cantor の対関数の逆関数 unpair
 *)
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

Lemma unpair_rec_m0 m x : 0 < m -> unpair x = (m.-1, 0) -> unpair x.+1 = (0, m).
Proof.
  move=> Hm.
  rewrite /unpair => ->.
  by rewrite prednK.
Qed.

Lemma unpair_rec m n x : unpair x = (m, n.+1) -> unpair x.+1 = (m.+1, n).
Proof.
  by rewrite /unpair => ->.
Qed.

(**
# 対関数 pair の全射性
*)
Theorem pair_unpair_eq_id (x : nat) : pair (unpair x) = x.
Proof.
  (** `x` に対する帰納法を使う *)
  elim: x => //= x IHx.                  (** `x = 0` の場合は明らか *)
  
  (** 見やすさのために `(m, n) := unpair x` とおく． *)
  pose m := (unpair x).1.
  pose n := (unpair x).2.
  
  (** `x` まで成り立つと仮定して `x + 1` でも成り立つことを示そう。 *)
  (** まず `unpair` の定義を展開する。 *)
  rewrite (surjective_pairing (unpair x)) -/m -/n.
  (* IHx も同時に書き換えてもよいが、Lean版にあわせて、あとにする。 *)
  
  case: ifP.                                (* split_ifs *)
  (** `n = 0` の場合 *)
  - move/eqP => H.
    Check pair (0, m.+1) = x.+1.
    (** `pair` の定義を展開して、示すべきことを `sum` を使って書き直すと *)
    rewrite /pair /= addn0.
    (** `sum (m + 1) = x + 1` を示せば良いことが分かる。 *)
    suff : sum m.+1 = x.+1 by have -> : m.+1 + sum m = sum m.+1 by done.
    
    (* 帰納法の仮定の主張に対しても、
      `pair` から `sum` に書き換えることができて、
      `sum m + m = x` であることが分かる。 *)
    have <- : m.+1 + sum m = sum m.+1 by done.
    rewrite /pair (surjective_pairing (unpair x)) -/m -/n H addn0 in IHx.
    by rewrite addSn addnC IHx.
    
  (** `n ≠ 0` の場合 *)
  Check pair (m.+1, n.-1) = x.+1.
  (* `pair` の定義を展開して、示すべきことを `sum` を使って書き直すと *)
  - rewrite /pair => H.
    (* `sum (m + n) + m = x` を示せば良いことが分かる。 *)
    suff : sum (m + n) + m = x.
    {
      rewrite addSnnS prednK.
      + by rewrite addnS => ->.
      + by apply: neq0_lt0n.
    }.
    (* 帰納法の仮定の主張に対しても、
       `pair` から `sum` に書き換えることができて、
       `sum (m + n) + m = x` が成り立つことが分かる。 *)
    rewrite /pair (surjective_pairing (unpair x)) -/m -/n in IHx.
    (** 従って示すべきことが言えた。 *)
    done.
Qed.

(**
# 対関数 pair の単射性

最後に pair が単射であることを示してみましょう。
unpair ∘ pair = id が成り立つことを示せば十分です。
*)

(** `unpair ∘ pair = id` が成り立つ。特に `pair` は単射。*)
Lemma unpair_pair_eq_id' (m n x : nat) : pair (m, n) = x -> unpair x = (m, n).
Proof.
  (** `x = pair (m, n)` として `x` に対する帰納法を利用する *)
  (* induction' h : pair (m, n) with x ih generalizing m n *)
  elim: x m n => [| x IHx] m n.
  (** `pair (m, n) = 0` のときは `pair` の定義から明らか。 *)
  - case/pair_zero => -> ->.
    by rewrite unpair_zero.
    
  (** `pair (m, n) = x + 1` のとき *)
  (** `m` がゼロかそうでないかで場合分けする *)
  - case: m => [| m'].
    (** `m = 0` のとき *)
    (** `pair (0, n) = x + 1` により `n > 0` が成り立つ。 *)
    + move=> H2.
      have npos : n > 0.
      {
        move: H2.
        rewrite /pair add0n addn0.
        move=> H.
        have : sum n != 0 by apply: (@addn1_to_neq0 (sum n) x).
        rewrite sum_zero_iff_zeroE.
        rewrite lt0n.
        done.
      }.
      
      (** よって `sum n = sum (n - 1) + n` と書くことができて、 *)
      have lem : sum n = sum n.-1 + n.
      {
        have: n.-1.+1 + sum n.-1 = sum n.-1.+1 by done.
        rewrite prednK => //=.
        rewrite addnC.
        by move=> ->.
      }.
      
      (** `pair (n - 1, 0) = x` が結論できる。 *)
      have : pair (n.-1, 0) = x.
      {
        rewrite /pair addn0.
        rewrite -{2}subn1.
        Search (_ + (_ - _)).
        rewrite addnBA //=.
        rewrite -lem.
        move: H2.
        rewrite /pair addn0 add0n.
        move=> ->.
        rewrite subn1.
        done.
      }.
      (** 後は帰納法の仮定から従う。 *)
      move=> H3.
      (* 対関数の繰り上がり。 *)
      apply: unpair_rec_m0 => //=.
      apply: IHx.
      by apply: H3.
      
      (** `m = m' + 1` のとき *)
      (** `pair` の定義から `pair (m', n + 1) = x` が成り立つ。 *)
    + move=> H3.
      have H2 : pair (m', n.+1) = x .
      {
        move: H3.
        rewrite /pair addSn.
        rewrite [in sum (m' + n.+1)]addnS.
        rewrite [LHS]addnS.
        Search (_.+1 = _.+1).
        move/eq_add_S.
        done.
      }.
      (** 後は帰納法の仮定から従う。 *)
      move/IHx in H2.
      by apply: unpair_rec.
Qed.

(**
証明したかったもの。
*)
Theorem unpair_pair_eq_id (m n : nat) : unpair (pair (m, n)) = (m, n).
Proof.
  by apply: unpair_pair_eq_id'.
Qed.

(**
# Coqでは行き詰まる例。
*)
Theorem unpair_pair_eq_id_ng (m n : nat) : unpair (pair (m, n)) = (m, n).
Proof.
  (** `x = pair (m, n)` として `x` に対する帰納法を利用する *)
  pose x := pair (m, n).
  have H : pair (m, n) = x by rewrite -/x.
  rewrite -/x.
  elim: x H => [| x IHx].
  (** `pair (m, n) = 0` のときは `pair` の定義から明らか。 *)
  - case/pair_zero => -> ->.
    by rewrite unpair_zero.
    
  - admit.
  (** `pair (m, n) = x + 1` のとき *)
(**
  m, n, x : nat
  IHx : pair (m, n) = x -> unpair x = (m, n)
  ============================
  pair (m, n) = x.+1 -> unpair x.+1 = (m, n)

IHx の m n がジェネラライズ generalizing できないので、これ以上証明が進まない。
CoqはLean のように、あとづけでジェネラライズできないのである。バニラCoqも同じ。

``induction' h : pair (m, n) with x ih generalizing m n``
*)
Admitted.                                   (* OK *)

(**
# 使用しなかった補題
*)
Lemma pair_zero' : pair (0, 0) = 0.
Proof.
  done.
Qed.

Lemma pair_zero'' (m n : nat) : (pair (m, n) == 0) = ((m == 0) && (n == 0)).
Proof.
  rewrite /pair.
  rewrite addn_eq0.
  rewrite sum_zero_iff_zeroE.
  rewrite addn_eq0.
  rewrite andbC.
  rewrite andbA.
  f_equal.
  rewrite Bool.andb_diag.
  done.
Qed.

Lemma unpair_rec_m0' m x : unpair x = (m, 0) -> unpair x.+1 = (0, m.+1).
Proof.
  by rewrite /unpair => ->.
Qed.

Lemma unpair_rec' m n x : 0 < n -> unpair x = (m, n) -> unpair x.+1 = (m.+1, n.-1).
Proof.
  move=> Hn.
  rewrite /unpair => ->.
  move/lt0n_neq0 in Hn.
  case: ifP.
  - move/eqP.
    move/eqP in Hn.
    done.
  - move/negbT.
    done.
Qed.

Lemma l1 n : pair (0, n) = sum n.
Proof.
  rewrite /pair.
  by rewrite add0n addn0.
Qed.

(* END *)
