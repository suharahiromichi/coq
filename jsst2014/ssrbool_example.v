Require Import ssreflect ssrfun ssrbool eqtype ssrnat.

Lemma boolP_example : forall n : nat, n * n - 1 < n ^ n.
Proof.
move=> n.
case: (boolP (n == O)).
  move/eqP.
  move=> ->.
  rewrite expn0.
  rewrite mul0n.
  by rewrite sub0n.
move=> n0.
case: (boolP (n == 1)).
  move/eqP.
  move=> ->.
  rewrite expn1.
  rewrite muln1.
  by rewrite subnn.
move=> n1.
have [m Hm] : exists m, n = m.+2.
  case: n n0 n1 => //.
  case=> // n _ _.
  by exists n.
rewrite Hm.
rewrite expnS.  
rewrite expnS.
rewrite mulnA.
rewrite subn1.
rewrite prednK; last first.
  by rewrite muln_gt0.
rewrite leq_pmulr //.
by rewrite expn_gt0.
Qed.

(* from ssrbool.v:

Predicate family to reflect excluded middle in bool.
CoInductive alt_spec (P : Prop) (b : bool) : bool -> Type :=
  AltTrue : P -> alt_spec P b true 
| AltFalse : ~~ b -> alt_spec P b false

boolP : forall b1 : bool, alt_spec b1 b1 b1
*)

Lemma ifP_example : forall n : nat, odd (if odd n then n else n.+1).
Proof.
move=> n.
case: ifP.
  done.
move=> Hn.
rewrite -addn1.
rewrite odd_add.
by rewrite Hn.
Qed.

(* from ssrbool.v:

CoInductive if_spec (A : Type) (b : bool) (vT vF : A) (not_b : Prop) : bool -> A -> Set :=
  IfSpecTrue : b -> if_spec b vT vF not_b true vT
| IfSpecFalse : not_b -> if_spec b vT vF not_b false vF

ifP : forall (A : Type) (b : bool) (vT vF : A),
  if_spec b vT vF (b = false) b (if b then vT else vF)
*)


