From elpi Require Import elpi.
From HB Require Import structures.
From mathcomp Require Import all_ssreflect.
From mathcomp Require Import all_algebra.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Num.Def.
Import Num.Theory.
Import GRing.Theory.

Local Open Scope ring_scope.

Variable R : semiRingType.
Variable a b c x y z : R.

Definition neq0_last s := last 1 s != 0 :> R.
Check oner_neq0 : forall s : semiRingType, 1 != 0.

(* 0 の多項式を作る。 *)
Check @Polynomial R [::] (oner_neq0 R) : polynomial R.
Print poly_nil.
Check @poly_nil R.

(* a X^2 + b X + c の多項式を作る。 *)
Definition tsts : seq R := [:: c; b; a].
Axiom neqa0 : a != 0 :> R.

Lemma neq0_last_s : neq0_last tsts.
Proof.
  by rewrite /neq0_last /tsts /= neqa0.
Qed.

Check @Polynomial R tsts neq0_last_s.
Check Polynomial neq0_last_s.

Definition tstp1 := Polynomial neq0_last_s.
Check tstp1 : polynomial R.
Check tstp1 : {poly R}. (* もう polynomial R の短縮形と思ってよい？ *)

(* 係数を取り出す。 *)
Compute tstp1`_2.                           (* a *)
Compute tstp1`_1.                           (* b *)
Compute tstp1`_0.                           (* c *)

(* poly から seq を取り出す関数 *)
Print polyseq.
Check [eta polyseq] : {poly R} -> seq R.
(* polyseq は単射である。 *)
Check @poly_inj R : forall p1 p2, polyseq p1 = polyseq p2 :> seq R -> p1 = p2 :> {poly R}.

(* サブタイプの値からベースタイプの値を取り出す。 *)
Check val tstp1 : seq R.                    (* polyseq とおなじ。 *)

(* サブタイプの値を作る。 *)
Check @insubd (seq R) neq0_last (polynomial R) (poly_nil R) tsts.
Check insubd (poly_nil R) tsts.
Definition tstp2 := insubd (poly_nil R) tsts.
Check tstp2 : {poly R}.

(* 最高次数の係数を取り出す。 *)
Compute lead_coef tstp1.                    (* a *)
Compute tstp1`_(size tstp1).-1.             (* a *)
Check lead_coefE : forall (R : semiRingType) (p : {poly R}), lead_coef p = p`_(size p).-1.

(* 定数多項式を作る *)
Check insubd (poly_nil R) [:: c] : {poly R}.
Check polyC c  : {poly R}.
Definition tstp_c := polyC c.

(* 引数に 0 が与えられる場合を考慮すると、[:: c] ではだめで、insubd で定義する必要がある。 *)
Check polyC 0  : {poly R}.
Definition tstp_c0 := @polyC R 0.

(* 定数多項式についての補題 *)
Compute nseq (42%N != 0) 42%N.              (* [:: 42] *)
Compute nseq  (0%N != 0) 0%N.               (* [::] *)

Lemma l_neq_false (x : R) : (x != x) = false.
Proof.
  by apply/eqP.
Qed.

(* 定数多項式からseqを取り出したものは、cが非零ならシングルトン、cが零なら空リスト *)
Check polyseqC c : c%:P = nseq (c != 0) c :> seq R.
(* これは、cが非0でも、0でも成り立つ。ただし、場合分けが要る。 *)
Goal c != 0 -> c%:P = [:: c] :> seq R.
Proof.
  rewrite polyseqC.
  move=> ->.
  done.
Qed.

Goal 0%:P = [::] :> seq R.
Proof.
  rewrite polyseqC l_neq_false.
  done.
Qed.


(* 定数多項式のサイズは、cが非零なら1、cが零なら0 *)
Check size_polyC : forall (R : semiRingType) (c : R), size c%:P = (c != 0).
(* これは、cが非0でも、0でも成り立つ。ただし、場合分けが要る。 *)
Goal c != 0 -> size c%:P = 1.
Proof.
  rewrite size_polyC.
  move=> ->.
  done.
Qed.

Goal @size R 0%:P = 0.
Proof.
  rewrite size_polyC l_neq_false.
  done.
Qed.

(* 定数多項式の0次の係数が定数、1次の係数は0である。 *)
Check coefC : forall (R : semiRingType) (c : R) (i : nat), c%:P`_i = (if i == 0 then c else 0).
(* これは、cが非0でも、0でも成り立つ。ただし、場合分けも不要。 *)
Goal c%:P`_0 = c.
Proof.
  rewrite coefC /=.
  done.
Qed.

Goal c%:P`_1 = 0.
Proof.
  rewrite coefC /=.
  done.
Qed.

(* 定数多項式を作る関数と0次の係数を求める関数は、キャンセルの関係である。 *)
Check polyCK : cancel polyC (coefp 0).
Check [eta polyCK] c : coefp 0 c%:P = c.

(* 定数多項式をつくる関数 polyC は単射である。 *)
Check [eta polyC_inj] : forall x1 x2 : R, x1%:P = x2%:P :> {poly R} -> x1 = x2 :> R.

(* 定数多項式の最高次数の係数は、定数である。 *)
Check lead_coefC c : lead_coef c%:P = c.
(* 定数多項式を作る関数と最高次数の係数を求める関数は、キャンセルの関係である。 *)
Goal cancel polyC (@lead_coef R).
Proof.
  move=> c.
  by rewrite lead_coefC.
Qed.

(* 以上 *)













Definition p1 := Poly [:: c; b; a].
Check p1 : {poly R}.

Fixpoint f (n : nat) :=
  match n with
  | 0 => c
  | 1 => b
  | _ => a
  end.
Definition p2 := \poly_(i < 3) f i.
Check p2 : {poly R}.

Check polyC c : {poly R}.
Check c%:P : {poly R}.
Check 'X : {poly R}.
Definition p3 := a%:P * 'X^2 + b%:P * 'X + c%:P * 'X^0.
Check p3 : {poly R}.

Goal forall i, p2`_i = f i.
Proof.
Admitted.

Goal forall i, coefp i p2 = f i.
Proof.
Admitted.





Goal 'X^1 = Poly [:: 0; 1] :> {poly R}.
Proof.
  rewrite unlock.
  rewrite /polyX_def.
  done.
Qed.

Goal 'X = [:: 0; 1] :> seq R.
Proof.
  by rewrite polyseqX.
Qed.

Goal 'X^2 = [:: 0; 0; 1] :> seq R.
Proof.
  by rewrite polyseqXn.
Qed.

Goal 'X^3 = [:: 0; 0; 0; 1] :> seq R.
Proof.
  by rewrite polyseqXn.
Qed.

Goal size ('X : {poly R}) = 2%N.
Proof.
  by rewrite size_polyX.
Qed.

Goal 1%:P = 1 :> {poly R}.
Proof.
  by rewrite polyC1.
Qed.

Check 'X          : {poly R} : lmodType R.
Check x *: 'X     : {poly R} : lmodType R.

Check lead_coef ('X : {poly R}).
Compute lead_coef ('X : {poly R}) = x.

Implicit Types (a b c x y z : R) (p q r d : {poly R}).

Local Notation "c %:P" := (polyC c).

Local Notation "\poly_ ( i < n ) E" := (poly n (fun i : nat => E)).

Open Scope unity_root_scope.

Theorem factor_theorem p a : reflect (exists q, p = q * ('X - a%:P)) (root p a).
Proof.
apply: (iffP eqP) => [pa0 | [q ->]]; last first.
rewrite hornerM_comm /comm_poly hornerXsubC subrr ?simp.

exists (\poly_(i < size p) horner_rec (drop i.+1 p) a).
apply/polyP=> i; rewrite mulrBr coefB coefMX coefMC !coef_poly.
apply: canRL (addrK _) _; rewrite addrC; have [le_p_i | lt_i_p] := leqP.
  rewrite nth_default // !simp drop_oversize ?if_same //.
  exact: leq_trans (leqSpred _).
case: i => [|i] in lt_i_p *; last by rewrite ltnW // (drop_nth 0 lt_i_p).
by rewrite drop1 /= -{}pa0 /horner; case: (p : seq R) lt_i_p.
Qed.


