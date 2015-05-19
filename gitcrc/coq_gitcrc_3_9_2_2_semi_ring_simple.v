(**
Monoid & SemiRing
2015_5_17

@suharahiromichi

モノイドと半環
ProofCafe での説明用に、Eqivalence を省いた、説明用の簡易版

A Gentle Introduction to Type Classes and Relations in Coq
の
Chapter 3.9.2 Operational Type Classes の後半の抜粋・改変

typeclassestut.pdf
typeclassesTut/Monoid_op_classes.v
*)

Set Implicit Arguments.
Unset Printing Implicit Defensive.
Set Print All.

Require Import ZArith.                      (* 整数 *)
Require Import Mat.                         (* 2x2行列 *)
(* 同じディレクトリに置いて、coqc Mat.v を実行しておく。 *)

(****************)
(*** モノイド ***)
(****************)
(*
Operational Type Classe
monoid_op はコンストラクタではなく、単に monoid_op f が f に簡約される。
 *)
Class monoid_binop (A : Type) := monoid_op : A -> A -> A.

Section Monoid.
  Local Infix "*" := monoid_op.
  
  Class Monoid (A : Type) (M_dot : monoid_binop A) (M_one : A) :=
    {
      M_dot_assoc : forall x y z : A, x * (y * z) = x * y * z;
      M_one_left  : forall x : A, M_one * x = x;
      M_one_right : forall x : A, x * M_one = x
    }.
End Monoid.

(************)
(*** 半環 ***)
(************)
Module SemiRing.
  Generalizable Variables A B.
  
  Class RingOne A := ring_one : A.            (* Operational Type Classe *)
  Class RingZero A := ring_zero : A.          (* Operational Type Classe *)
  Class RingPlus A := ring_plus :> monoid_binop A. (* Operational Type Classe *)
  Class RingMult A := ring_mult :> monoid_binop A. (* Operational Type Classe *)
  Infix "+" := ring_plus.
  Infix "*" := ring_mult.
  Notation "0" := ring_zero.
  Notation "1" := ring_one.
  
  (* Typeclasses Transparent RingPlus RingMult RingOne RingZero. *)
  (* 以下のヒントと同じ。 *)
  Hint Transparent RingPlus RingMult RingOne RingZero : typeclass_instances.
  (* typeclass_instance として 。。。 を導出の過程で透明（δ変換して同じ) と扱う。 *)
  (* 例： R_plus と ring_plus ： 要補足 *)
  
  Class Distribute {A : Type} (f g: A -> A -> A): Prop :=
    {
      distribute_l a b c: f a (g b c) = g (f a b) (f a c);
      distribute_r a b c: f (g a b) c = g (f a c) (f b c)
    }.
  
  Class Commutative {A B : Type} (m : A -> A -> B): Prop := 
    commutativity x y : m x y = m y x.
  
  Class Absorb {A : Type} (m: A -> A -> A) (x : A) : Prop := 
    {
      absorb_l c : m x c = x;
      absorb_r c : m c x = x
    }.
  
  Class CommutativeMonoid {A : Type} (M_dot : monoid_binop A) (M_one : A) :=
    {
      e_commmonoid_monoid :> Monoid M_dot M_one;
      e_commmonoid_commutative :> Commutative M_dot
    }.
  
  Class SemiRing (A:Type)
        (R_plus : RingPlus A)
        (R_zero : RingZero A)
        (R_mult : RingMult A)
        (R_one : RingOne A) :=
    {
      add_monoid :> CommutativeMonoid ring_plus ring_zero;
      mul_monoid :> Monoid ring_mult ring_one;
      ring_dist :> Distribute ring_mult ring_plus;
      ring_0_mult :> Absorb ring_mult 0
    }.
  
  (***********************)
  (*** 半環の簡単な補題 ***)
  (***********************)
  Section SemiRingTheory.
    Context `{M : SemiRing A}.              (* Aは、Generalizable Variable *)
    
    (* テスト *)
    Check 0 * (1 + 1) : A.
    Check 0 * (1 + 1) = 0 : Prop.
    
    Definition ringtwo := 1 + 1.
    Lemma ringtwomult : forall x : A, ringtwo * x = x + x.
    Proof.
      intros.
      unfold ringtwo.
      rewrite distribute_r.                   (* ring_dist の :> が効く。 *)
      rewrite (M_one_left x).               (* add_monoid と mul_monoid の :> が効く。 *)
      reflexivity.
    Qed.
  End SemiRingTheory.
  
  (***********************)
  (* 具体的な半環を作る。 *)
  (***********************)
  (* 整数を要素とする2x2行列 *)
  Section M2Z_Ring.
    (* + *)
    Instance M2Z_plus_op : monoid_binop (M2 Z) := M2_plus Zplus. (* Mat.v *)
    Instance m2z_plus : RingPlus (M2 Z) := M2Z_plus_op.
    
    (* 0 *)
    Instance m2z_zero : RingZero (M2 Z) := Zero2 0%Z. (* Mat.v *)
    
    (* * *)
    Instance M2Z_mult_op : monoid_binop (M2 Z) := M2_mult Zplus Zmult. (* Mat.v *)
    Instance m2z_mult : RingMult (M2 Z) := M2Z_mult_op.

    (* 1 *)
    Instance m2z_one : RingOne (M2 Z) := Id2 0%Z 1%Z. (* Mat.v *)
    (* Section mat の Vaiables (zero one : A) の順番を守ること。 *)
    
    (* テスト *)
    Check 0 * (1 + 1) : M2 Z.
    
    Instance M2Z_Commutative : Commutative m2z_plus.
    Proof.
      unfold Commutative.
      intros x y.
      unfold m2z_plus, M2Z_plus_op, M2_plus.
      f_equal;
      apply Zplus_comm;
      reflexivity.
    Qed.
    
    Program Instance M2Z_Monoid_plus : Monoid m2z_plus m2z_zero.
    Next Obligation.
      unfold monoid_op, m2z_plus, M2Z_plus_op, M2_plus.
      simpl; f_equal; apply Zplus_assoc;
      reflexivity.
    Qed.
    Next Obligation.
      destruct x.                           (* 要素に分ける。 *)
      unfold monoid_op, m2z_plus, M2Z_plus_op, M2_plus.
      unfold m2z_zero, Zero2.
      reflexivity.
    Qed.
    Next Obligation.
      destruct x.                           (* 要素に分ける。 *)
      unfold monoid_op, m2z_plus, M2Z_plus_op, M2_plus.
      unfold m2z_zero, Zero2.
      simpl.
      repeat rewrite Z.add_0_r.
      reflexivity.
    Qed.

    Program Instance M2Z_CommutativeMonoid : CommutativeMonoid m2z_plus m2z_zero.
    (* No Obligation *)
    
    Program Instance M2Z_Monoid_mult : Monoid m2z_mult m2z_one.
    Next Obligation.
      unfold monoid_op, m2z_mult, M2Z_mult_op, M2_mult.
      simpl; f_equal;
      repeat rewrite Z.mul_add_distr_l, Z.mul_add_distr_r;
      repeat rewrite Z.mul_assoc;
      repeat rewrite Z.mul_assoc;
      repeat rewrite Z.add_assoc;
      f_equal;
      repeat rewrite <- Z.add_assoc;
      f_equal;
      rewrite Z.add_comm;
      reflexivity.
    Qed.
    Next Obligation.
      unfold monoid_op, m2z_mult, M2Z_mult_op, M2_mult.
      unfold m2z_one, Id2.
      destruct x.
      repeat rewrite Z.add_0_r.
      simpl.
      case c00; case c01; case c10; case c11;
      reflexivity.
    Qed.
    Next Obligation.
      unfold monoid_op, m2z_mult, M2Z_mult_op, M2_mult.
      unfold m2z_one, Id2.
      destruct x.
      repeat rewrite Z.mul_0_r.
      repeat rewrite Z.add_0_l.
      repeat rewrite Z.add_0_r.
      repeat rewrite Z.mul_1_r.
      simpl.
      reflexivity.
    Qed.
    
    Program Instance M2Z_Distribute : Distribute m2z_mult m2z_plus.
    Next Obligation.
    Proof.
      unfold monoid_op, m2z_mult, M2Z_mult_op, M2_mult.
      unfold m2z_plus, M2Z_plus_op, M2_plus.
      simpl; f_equal;
      repeat rewrite Z.mul_add_distr_l;
      repeat rewrite Zplus_assoc;
      f_equal;
      repeat rewrite <- Zplus_assoc;
      f_equal;
      rewrite Z.add_comm;
      reflexivity.
    Qed.
    Next Obligation.
    Proof.
      unfold monoid_op, m2z_mult, M2Z_mult_op, M2_mult.
      unfold m2z_plus, M2Z_plus_op, M2_plus.
      simpl; f_equal;
      repeat rewrite Z.mul_add_distr_r;
      repeat rewrite Zplus_assoc;
      f_equal;
      repeat rewrite <- Zplus_assoc;
      f_equal;
      rewrite Z.add_comm;
      reflexivity.
    Qed.
    
    Program Instance M2Z_Absb : Absorb m2z_mult m2z_zero.
    Next Obligation.
    Proof.
      unfold monoid_op, m2z_mult, M2Z_mult_op, M2_mult.
      unfold m2z_zero, Zero2.
      simpl.
      repeat rewrite Z.mul_0_r.
      repeat rewrite Z.add_0_r.
      reflexivity.
    Qed.
    
    Program Instance M2Z_SemiRing : SemiRing m2z_plus m2z_zero m2z_mult m2z_one.
    (* No Obligation *)
  End M2Z_Ring.
  
  (* 任意の半環な型を要素とする2x2行列 *)
  Section M2A_Ring.
    Context `{M : SemiRing A}.              (* Aは、Generalizable Variable *)
    (* A が、行列の要素の型 *)
    
    (* + *)
    Instance M2A_plus_op : monoid_binop (M2 A) := M2_plus R_plus. (* Mat.v *)
    Instance m2a_plus : RingPlus (M2 A) := M2A_plus_op.
    
    (* 0 *)
    Instance m2a_zero : RingZero (M2 A) := Zero2 R_zero. (* Mat.v *)
    
    (* * *)
    Instance M2A_mult_op : monoid_binop (M2 A) := M2_mult R_plus R_mult. (* Mat.v *)
    Instance m2a_mult : RingMult (M2 A) := M2A_mult_op.
    
    (* 1 *)
    Instance m2a_one : RingOne (M2 A) := Id2 R_zero R_one. (* Mat.v *)
    (* Section mat の Vaiables (zero one : A) の順番を守ること。 *)
    
    (* テスト *)
    Check 0 * (1 + 1) : M2 A.
    Check 0 * (1 + 1) = 0 : Prop.
    
    Instance M2A_Commutative : Commutative m2a_plus.
    Proof.
      unfold Commutative.
      intros x y.
      unfold m2a_plus, M2A_plus_op, M2_plus.
      f_equal; apply (@commutativity A A ring_plus _). (* Hintの無い場合 *)
      Undo.
      f_equal; apply commutativity.         (* Hintがあるなら *)
    Qed.
    Print M2A_Commutative.
    
    Program Instance M2A_Monoid_plus : Monoid m2a_plus m2a_zero.
    Next Obligation.
      unfold monoid_op, m2a_plus, M2A_plus_op, M2_plus.
      simpl; f_equal; apply M_dot_assoc.
    Qed.
    Next Obligation.
      destruct x.                           (* M2の要素に分ける。 *)
      unfold monoid_op, m2a_plus, M2A_plus_op, M2_plus.
      unfold m2a_zero, Zero2.
      simpl; f_equal; apply M_one_left.
    Qed.
    Next Obligation.
      destruct x.                           (* M2の要素に分ける。 *)
      unfold monoid_op, m2a_plus, M2A_plus_op, M2_plus.
      unfold m2a_zero, Zero2.
      simpl; f_equal; apply M_one_right.
    Qed.
    
    Program Instance M2A_CommutativeMonoid : CommutativeMonoid m2a_plus m2a_zero.
    (* No Obligation *)
    
    (* 以下、工事中 *)
    Program Instance M2A_Monoid_mult : Monoid m2a_mult m2a_one.
    Next Obligation.
    Admitted.
    Next Obligation.
    Admitted.
    Next Obligation.
    Admitted.
    
    Program Instance M2A_Distribute : Distribute m2a_mult m2a_plus.
    Next Obligation.
    Proof.
    Admitted.
    Next Obligation.
    Proof.
    Admitted.
    
    Program Instance M2A_Absb : Absorb m2a_mult m2a_zero.
    Next Obligation.
    Proof.
    Admitted.
    Next Obligation.
    Proof.
    Admitted.
    
    Program Instance M2A_SemiRing : SemiRing m2a_plus m2a_zero m2a_mult m2a_one.
    (* No Obligation *)
    
  End M2A_Ring.
  (* ** M2A Ring 終わり ** *)
End SemiRing.

(* END *)
