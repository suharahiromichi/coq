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
  
  Typeclasses Transparent RingPlus RingMult RingOne RingZero. (* !!! *)
  
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
    Context `{M : SemiRing A}.              (* Aは、Generalizable Variables *)
    
    (* テスト *)
    Check 0 * (1 + 1) : A.
    Check 0 * (1 + 1) = 0 : Prop.
    
    Definition ringtwo := 1 + 1.
    Lemma ringtwomult : forall x : A, ringtwo * x = x + x.
    Proof.
      intros.
      unfold ringtwo.
      rewrite distribute_r.                   (* ring_dist の :> が効く。 *)
      now rewrite (M_one_left x).             (* add_monoid と mul_monoid の :> が効く。 *)
    Qed.
  End SemiRingTheory.
  
  (***********************)
  (* 具体的な半環を作る。 *)
  (***********************)
  (* 任意の半環な型を要素とする2x2行列 *)
  Section M2A_Ring.
    Context `{M : SemiRing A}.              (* Aは、Generalizable Variables *)
    (* A が、行列の要素の型 *)
    
    (* + *)
    Instance M2A_plus_op : monoid_binop (M2 A) := (@M2_plus A R_plus).
    Instance m2a_plus : RingPlus (M2 A) := M2A_plus_op.
    
    (* 0 *)
    Instance m2a_zero : RingZero (M2 A) := Zero2 R_zero. (* Mat.v *)
    
    (* * *)
    Instance M2A_mult_op : monoid_binop (M2 A) := (@M2_mult A R_plus R_mult). (* Mat.v *)
    Instance m2a_mult : RingMult (M2 A) := M2A_mult_op.
    
    (* 1 *)
    Instance m2a_one : RingOne (M2 A) := Id2 R_one R_zero.
    
    (* テスト *)
    Check 0 * (1 + 1) : M2 A.
    Check 0 * (1 + 1) = 0 : Prop.
    
    Instance M2A_Commutative : Commutative m2a_plus.
    Proof.
      unfold Commutative.
      intros x y.
      unfold m2a_plus, M2A_plus_op, M2_plus.
      f_equal; apply commutativity.
    Qed.
    
    Program Instance M2A_EMonoid_plus : Monoid m2a_plus m2a_zero.
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
