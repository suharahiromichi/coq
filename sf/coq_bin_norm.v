From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Inductive bin :=
| o : bin -> bin
| i : bin -> bin
| z : bin.

Check (i (i (o z))).

Fixpoint binnat (b : bin) : nat :=          (* f *)
  match b with
  | z => 0
  | o b => (binnat b).*2
  | i b => (binnat b).*2 + 1
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
  | 0 => z
  | n.+1 => bininc (natbin n)
  end.

(* 直接的な正規化 *)
Fixpoint normalize (b : bin) : bin :=
  match b with
  | o b =>
    match (binnat b) with
    | 0 => z
    | _ => o (normalize b)
    end
  | i b => i (normalize b)
  | z => z
  end.

Compute normalize (o (i (i (o (o z))))).
Compute natbin (binnat (o (i (i (o (o z)))))).

Lemma hodai1 n :
  natbin n.+1.*2 = o (natbin n.+1).
Proof.
  elim: n.
  - by [].
  - move=> /= n' H /=.
    by rewrite H /=.
Qed.
(*
natbin n.*2 = o (natbin n) を証明するには、
z = o z を認める必要がある。
つまり、一般的過ぎて証明できない。
 *)

Lemma hodai2 n :
  natbin (n.*2 + 1) = i (natbin n).
Proof.
  elim: n.
  - by [].
  - move=> /= n' H /=.
    by rewrite H /=.
Qed.

(* natを経由する正規化と、直接的な正規化が、同じ結果になることを証明する。 *)
Goal forall (b : bin),
    natbin (binnat b) = normalize b.
Proof.
  elim=> [b IHb|b IHb|] /=.
  - rewrite -IHb.
    case: (binnat b).
    + by [].
    + elim.
      * by [].
      * move=> n H.
          by apply hodai1.
  - rewrite -IHb.
    case: (binnat b).
    + by [].
    + elim.
      * by [].
      * move=> n H.
          by apply hodai2.
  - by [].
Qed.

(* ******** *)
(* **別解** *)
(* ******** *)

(* 再帰関数の、関数呼び出しに関する帰納法をできるようにする。
 * パターンマッチが入れ子になったりしている複雑な再帰関数のときに便利
 * https://gist.github.com/yoshihiro503/fc51fef8b94c3a42c3ca
 *)
Functional Scheme normalize_ind := Induction for normalize Sort Prop.
Goal forall (b : bin),
    natbin (binnat b) = normalize b.
Proof.
  move=> b.
  functional induction (normalize b) => /=.
  (* natbin (binnat b0).*2 = z *)
  - by rewrite e0 /=.
  (* natbin (binnat b0).*2 = o (normalize b0) *)
  - by rewrite -IHb0 e0 hodai1 /=.
  (* natbin ((binnat b0).*2 + 1) = i (normalize b0) *)
  - by rewrite -IHb0 hodai2 /=.
  (* z = z *)
  - by [].
Qed.

(* END *)
