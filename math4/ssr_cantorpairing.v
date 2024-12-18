(**
Cantor の対関数とその全単射性

# 一般的な解説

- https://www.youtube.com/watch?v=rRpkLoUpvuM


# Lean

- https://lean-ja.github.io/lean-by-example/Tutorial/Exercise/CantorPairing.html


# MathComp
 *)
From mathcomp Require Import all_ssreflect.

(**
sum n = x.+1
->
sum n != 0
*)
Lemma addn1_to_neq0 (X x : nat) : X = x.+1 -> X != 0.
Proof.
  Check ltn0Sn : forall n : nat, 0 < n.+1.
  Check lt0n : forall n : nat, (0 < n) = (n != 0).
  rewrite -lt0n.
  move=> ->.
  by rewrite ltn0Sn.
Qed.

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

Lemma sum_zero_iff_zero'' {n : nat} : (sum n == 0) = (n == 0).
Proof.
  apply/idP/idP; move/eqP.
  - by move/sum_zero_iff_zero => ->.
  - by move=> ->.
Qed.

Lemma sum_not_zero_iff_not_zero'' {n : nat} : (sum n != 0) = (n != 0).
Proof.
  by rewrite sum_zero_iff_zero''.
Qed.

(**
## 対関数とその逆関数
 *)
(** Cantor の対関数 *)
Definition pair (x : nat * nat) : nat :=
  let (m, n) := x in sum (m + n) + m.

Lemma pair_zero : pair (0, 0) = 0.
Proof.
  done.
Qed.

Lemma pair_zero' (m n : nat) : pair (m, n) = 0 <-> (m = 0 /\ n = 0).
Proof.
  split.
  - rewrite /pair.
    move/eqP.
    rewrite addn_eq0.
    case/andP.
    move/eqP.
    move/sum_zero_iff_zero.
    move=> Hmn.
    move/eqP.
    move=> Hm.
    move: Hmn.
    rewrite Hm.
    rewrite add0n.
    move=> -> .
    done.
  - by case=> -> ->.
Qed.

Lemma pair_zero'' (m n : nat) : (pair (m, n) == 0) = ((m == 0) && (n == 0)).
Proof.
  rewrite /pair.
  rewrite addn_eq0.
  rewrite sum_zero_iff_zero''.
  rewrite addn_eq0.
  rewrite andbC.
  rewrite andbA.
  f_equal.
  rewrite Bool.andb_diag.
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

Lemma unpair_rec_m0 m x : unpair x = (m, 0) -> unpair x.+1 = (0, m.+1).
Proof.
  by rewrite /unpair => ->.
Qed.

Lemma unpair_rec_m0' m x : 0 < m -> unpair x = (m.-1, 0) -> unpair x.+1 = (0, m).
Proof.
  move=> Hm.
  rewrite /unpair => ->.
  by rewrite prednK.
Qed.

Lemma unpair_rec m n x : 0 < n -> unpair x = (m, n) -> unpair x.+1 = (m.+1, n.-1).
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

Lemma unpair_rec' m n x : unpair x = (m, n.+1) -> unpair x.+1 = (m.+1, n).
Proof.
  by rewrite /unpair => ->.
Qed.

(**
## pair の全射性
*)
Theorem pair_unpair_eq_id (x : nat) : pair (unpair x) = x.
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
    (** `pair` から `sum` に書き換えることができて``、 *)

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
  - rewrite /pair => H.
  (** `pair` の定義を展開して、示すべきことを `sum` を使って書き直すと *)
  (** `sum (m + n) + m = x` を示せば良いことが分かる。 *)
    suff : sum (m + n) + m = x.
    {
      rewrite addSnnS prednK.
      + by rewrite addnS => ->.
      + by apply: neq0_lt0n.
    }.
    (** 帰納法の仮定の主張に対しても、 *)
    (** `pair` から `sum` に書き換えることができて、 *)
    rewrite /pair in IHx.
    rewrite (surjective_pairing (unpair x)) in IHx.
    rewrite -/m -/n in IHx.
    (** `sum (m + n) + m = x` が成り立つことが分かる。 *)
    (** 従って示すべきことが言えた。 *)
    done.
Qed.

(** 問3: 対関数の単射性 *)
(**
最後に pair が単射であることを示してみましょう。
unpair ∘ pair = id が成り立つことを示せば十分です。
*)

Lemma l0 m : m.+1 + sum m = sum m.+1.
Proof.
  done.
Qed.

Lemma l1 n : pair (0, n) = sum n.
Proof.
  rewrite /pair.
  by rewrite add0n addn0.
Qed.

(** `unpair ∘ pair = id` が成り立つ。特に `pair` は単射。*)
Lemma unpair_pair_eq_id' (m n x : nat) : pair (m, n) = x -> unpair x = (m, n).
Proof.
  (** `x = pair (m, n)` として `x` に対する帰納法を利用する *)
  (* induction' h : pair (m, n) with x ih generalizing m n *)
  elim: x m n => [| x IHx] m n.
  (** `pair (m, n) = 0` のときは `pair` の定義から明らか。 *)
  - case/pair_zero' => -> ->.
    by rewrite unpair_zero.

  (** `pair (m, n) = x + 1` のとき *)
(*
x : ℕ
ih : ∀ (m n : ℕ), pair (m, n) = x → unpair x = (m, n)
m n : ℕ
h : pair (m, n) = x + 1
⊢ unpair (x + 1) = (m, n)
*)
  (** `m` がゼロかそうでないかで場合分けする *)
  - case: m => [| m'].
    (*
x : ℕ
ih : ∀ (m n : ℕ), pair (m, n) = x → unpair x = (m, n)
m n : ℕ
h : pair (m, n) = x + 1
⊢ unpair (x + 1) = (m, n)
*)

    (** `m = 0` のとき *)
    (** `pair (0, n) = x + 1` により `n > 0` が成り立つ。 *)
    + move=> H2.
      have npos : n > 0.
      {
        move: H2.
        rewrite /pair add0n addn0.
        move=> H.
        have : sum n != 0 by apply: (@addn1_to_neq0 (sum n) x).
        rewrite sum_zero_iff_zero''.
        rewrite lt0n.
        done.
      }.
      
      (** よって `sum n = sum (n - 1) + n` と書くことができて、 *)
      have lem : sum n = sum n.-1 + n.
      {
        Check l0 n.-1 : n.-1.+1 + sum n.-1 = sum n.-1.+1.
        Check prednK : forall n : nat, 0 < n -> n.-1.+1 = n.
        move : (l0 n.-1).
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
      (* Lean の振る舞いとは一致している。 *)
      (*
x : ℕ
ih : ∀ (m n : ℕ), pair (m, n) = x → unpair x = (m, n)

h : pair (0, n) = x + 1
npos : n > 0
lem : sum n = sum (n - 1) + n
this : pair (n - 1, 0) = x
⊢ unpair (x + 1) = (0, n)
*)

      move=> H3.
      (* 対関数の繰り上がり。 *)
      apply: unpair_rec_m0' => //=.
      apply: IHx.
      by apply: H3.

    (* ************************************* *)
      (** `m = m' + 1` のとき *)
(*
x : ℕ
ih : ∀ (m n : ℕ), pair (m, n) = x → unpair x = (m, n)
m n : ℕ
h : pair (m, n) = x + 1
⊢ unpair (x + 1) = (m, n)
*)
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
        
        (* Lean の振る舞いとは一致している。 *)
        (*
x : ℕ
ih : ∀ (m n : ℕ), pair (m, n) = x → unpair x = (m, n)
m n m' : ℕ
h : pair (m' + 1, n) = x + 1
this : pair (m', n + 1) = x
⊢ unpair (x + 1) = (m' + 1, n)
*)
        move/IHx in H2.
        by apply: unpair_rec'.
Qed.


Theorem unpair_pair_eq_id (m n : nat) : unpair (pair (m, n)) = (m, n).
Proof.
  by apply: unpair_pair_eq_id'.
Qed.

(* ********************* *)
(* Coqでは行き詰まる例。 *)
(* ********************* *)
(** `unpair ∘ pair = id` が成り立つ。特に `pair` は単射。*)
Theorem unpair_pair_eq_id_ng (m n : nat) : unpair (pair (m, n)) = (m, n).
Proof.
  (** `x = pair (m, n)` として `x` に対する帰納法を利用する *)
  (* induction' h : pair (m, n) with x ih generalizing m n *)
  pose x := pair (m, n).
  have H : pair (m, n) = x by rewrite -/x.
  rewrite -/x.
  elim: x H => [| x IHx].
  (** `pair (m, n) = 0` のときは `pair` の定義から明らか。 *)
  - case/pair_zero' => -> ->.
    by rewrite unpair_zero.

  (** `pair (m, n) = x + 1` のとき *)
(*
x : ℕ
ih : ∀ (m n : ℕ), pair (m, n) = x → unpair x = (m, n)
m n : ℕ
h : pair (m, n) = x + 1
⊢ unpair (x + 1) = (m, n)
*)
  (** `m` がゼロかそうでないかで場合分けする *)
  - case H : m IHx => IHx.

    (*
x : ℕ
ih : ∀ (m n : ℕ), pair (m, n) = x → unpair x = (m, n)
m n : ℕ
h : pair (m, n) = x + 1
⊢ unpair (x + 1) = (m, n)

x : ℕ
ih : ∀ (m n : ℕ), pair (m, n) = x → unpair x = (m, n)
m n : ℕ
h : pair (m, n) = x + 1
⊢ unpair (x + 1) = (m, n)
*)
Admitted.                                   (* OK *)

(* END *)
