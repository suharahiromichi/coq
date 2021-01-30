(**
Coq/SSReflect/MathComp による定理証明

6.1 テーマ1 整数がその加法で可換群になること

(Canonical 宣言を使わない例)

======
2018_04_21 @suharahiromichi
 *)

From mathcomp Require Import all_ssreflect.
From mathcomp Require Import ssralg.
Require Import ZArith.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Set Print All.

(**
# 可換群の定義
*)
Section ZtoRing.
  
  Lemma Zeq_boolP : Equality.axiom Zeq_bool.
  Proof.
    move=> x y.
      by apply: (iffP idP); rewrite Zeq_is_eq_bool.
  Qed.

  Definition Z_eqMixin := EqMixin Zeq_boolP.
  Definition Z_eqType := Eval hnf in EqType Z Z_eqMixin.
  (* Canonical Z_eqType. *)
  (* 右辺で、カノニカル [Z <- Equality.sort Z_eqType] になる。 *)
  Compute Equality.sort Z_eqType.           (* Z *)
  
  Definition Z_pickle (z : Z) : nat :=
    if (0 <=? z)%Z then
      (Z.abs_nat z).*2
    else
      (Z.abs_nat (- z)).*2.+1.
  
  Definition Z_unpickle (n : nat) : option Z :=
    if odd n then
      Some (- (Z.of_nat n.-1./2))%Z
    else
      Some (Z.of_nat n./2).
  
  Lemma Z_pickleK : pcancel Z_pickle Z_unpickle.
  Proof.
    move=> z; rewrite /Z_pickle.
    case: ifP => z0;
    rewrite /Z_unpickle /= odd_double
            (half_bit_double _ false)
            Zabs2Nat.id_abs Z.abs_eq ?Z.opp_nonneg_nonpos
            ?Z.opp_involutive //.
    + by apply: Zle_bool_imp_le.
    + move/Z.leb_nle : z0.
        by move/Znot_le_gt /Z.gt_lt /Z.lt_le_incl.
  Qed.
  
  Definition Z_choiceMixin := PcanChoiceMixin Z_pickleK.
  (* 右辺で、カノニカル [Z <- Equality.sort Z_eqType] を使う。 *)

  Definition Z_choiceType := ChoiceType (Equality.sort Z_eqType) Z_choiceMixin.
  (* Canonical Z_choiceType. *)
  Compute Choice.sort Z_choiceType.         (* Z *)
  (* 左辺で、カノニカル [Z <- Choice.sort Z_choiceType] になる。 *)
  
  Definition Z_countMixin := PcanCountMixin Z_pickleK.
  (* 右辺で、カノニカル [Z <- Choice.sort Z_choiceType] を使う。 *)  

  Definition Z_countType := CountType (Choice.sort Z_choiceType) Z_countMixin.  
  (* Canonical Z_modType. *)
  Compute Countable.sort Z_countType.       (* Z *)
  (* 左辺で、カノニカル [Z <- Count.sort Z_countType] になる。 *)
  
  Definition Z_modMixin :=
    ZmodMixin Z.add_assoc Z.add_comm Z.add_0_l Z.add_opp_diag_l.
  (* 右辺で、カノニカル [Z <- Choice.sort Z_choiceType] を使う。 *)    

  Definition Z_modType := Eval hnf in ZmodType (Choice.sort Z_choiceType) Z_modMixin.
  (* Canonical Z_modType. *)
  Compute GRing.Zmodule.sort Z_modType.     (* Z *)
  (* 左辺で、カノニカル [Z <- GRing.Zmodule.sort Z_modType] になる。 *)
  
End ZtoRing.

(**
# Ringの演算子 [*+] を使えるようにする。
*)

Open Scope ring_scope.

(**
# Canonical Z_modType の必要性の説明
*)
Section TEST.
  
  Locate "_ *+ _".               (* GRing.natmul x n   : ring_scope *)
  Check Z_modType : zmodType.
  Compute GRing.Zmodule.sort Z_modType.     (* Z *)
  
  Variable x : GRing.Zmodule.sort Z_modType.
  
  Check x *+ 2.
  Check GRing.mulr2n x : x *+ 2 = x + x.
  Check @GRing.natmul : forall V : zmodType, (* sort のコアーションを明示する。 *)
      GRing.Zmodule.sort V -> nat -> GRing.Zmodule.sort V.
  Check @GRing.mulr2n Z_modType x : x *+ 2 = x + x.
  
  Check @GRing.natmul : forall V : zmodType, (* sort のコアーションを明示する。 *)
      GRing.Zmodule.sort V -> nat -> GRing.Zmodule.sort V.
  Check @GRing.natmul Z_modType :           (* 型の引数を与える。 *)
    GRing.Zmodule.sort Z_modType -> nat -> GRing.Zmodule.sort Z_modType.
  Check @GRing.natmul Z_modType :           (* sort Z_modType = Z を反映する。 *)
    Z -> nat -> Z.
  
End TEST.

(**
# [x *+ 2 = 2 * z] の証明
*)

Goal forall x : GRing.Zmodule.sort Z_modType, x *+ 2 = (2 * x)%Z.
Proof.
  case=> // x; rewrite GRing.mulr2n Z.mul_comm.
    by rewrite -(Zred_factor1 (Z.pos x)).
    by rewrite -(Zred_factor1 (Z.neg x)).
Qed.

(** END *)
