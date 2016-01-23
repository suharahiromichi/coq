Inductive bin :=
| o : bin -> bin
| i : bin -> bin
| z : bin.

Check (i (i (o z))).

Fixpoint binnat (b : bin) : nat :=          (* f *)
  match b with
  | z => O
  | o b => 2 * (binnat b)
  | i b => 2 * (binnat b) + 1
  end.

Compute binnat (o (i (i (o (o z))))).

Fixpoint bininc (b : bin) : bin :=
  match b with
  | i b => o (bininc b)
  | o b => i b
  | z => i z
  end.

Compute bininc (o (i (i (o (o z))))).
Compute bininc (i (i (i (o (o z))))).
Compute bininc (o (i (i z))).
Compute bininc (i (i (i z))).

Fixpoint natbin (n : nat) : bin :=          (* g *)
  match n with
  | O => z
  | S n => bininc (natbin n)
  end.

(* 直接的な正規化 *)
Fixpoint normalize (b : bin) : bin :=
  match b with
  | o b =>
    match (binnat b) with
    | O => z
    | _ => o (normalize b)
    end
  | i b => i (normalize b)
  | z => z
  end.

Compute normalize (o (i (i (o (o z))))).
Compute natbin (binnat (o (i (i (o (o z)))))).

Lemma hodai1 n :
  natbin (S n + S n) = o (natbin (S n)).
Proof.
  simpl.
  admit.
Qed.

Lemma hodai2 n :
  natbin (S n + S n + 1) = i (natbin (S n)).
Proof.
  simpl.
  admit.
Qed.

(* natを経由する正規化と、直接的な正規化が、同じ結果になることを証明する。 *)
Goal forall (b : bin),
    natbin (binnat b) = normalize b.
Proof.
  induction b.
  - simpl.
    rewrite <- IHb.
    case (binnat b).
    + simpl.
      reflexivity.
    + intros n.
      induction n.
      * simpl.
        reflexivity.
      * rewrite plus_0_r.
        rewrite hodai1.
        reflexivity.
  - simpl.      
    rewrite <- IHb.
    case (binnat b).
    + simpl.
      reflexivity.
    + intros n.
      induction n.
      * simpl.
        reflexivity.
      * rewrite plus_0_r.
        rewrite hodai2.
        reflexivity.
  - simpl.
    reflexivity.
Qed.
