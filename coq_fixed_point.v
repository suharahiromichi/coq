(*
   固定小数点演算の検証
   その、はじめの一歩
   *)


Require Import ZArith.
Open Scope Z_scope.


Inductive FP (n:nat) :=
| mkFP : Z -> FP n.


Check mkFP 2 7.
Eval cbv in mkFP 2 7.


Definition FP_body (n : nat) : FP n -> Z.
Proof.
  intros.
  inversion H.
  exact H0.
Defined.
Check FP_body.
Implicit Arguments FP_body.
Eval cbv in FP_body (mkFP 2 7).


Definition FP_add (n : nat) : FP n -> FP n -> FP n.
Proof.
  intros n H1 H2.
  inversion H1 as [H11].
  inversion H2 as [H12].
  apply (mkFP n (H11 + H12)).
Defined.
Implicit Arguments FP_add.
Check FP_add.
Eval cbv in FP_add (mkFP 2 7) (mkFP 2 7).


Definition FP_mult_2 (n : nat) : FP n -> FP n.
Proof.
  intros n H1.
  inversion H1 as [H11].
  apply (mkFP n (2 * H11)).
Defined.
Implicit Arguments FP_mult_2.
Check FP_mult_2.
Eval cbv in FP_mult_2 (mkFP 2 7).


Lemma eq_FP : forall x y n, x = y -> mkFP n x = mkFP n y.
Proof.
  intros.
  rewrite H.
  reflexivity.
Qed.


Lemma add_mult_FP : forall n (x : FP n), FP_add x x = FP_mult_2 x.
Proof.
  intros n x.
  inversion x.
  case x.
  intros z.
  unfold FP_add.
  unfold FP_mult_2.
  apply eq_FP.
  ring.
Qed.


(* END *)