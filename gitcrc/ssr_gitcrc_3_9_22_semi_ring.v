(**
Monoid & SemiRing, SSReflect版

2015_6_16

@suharahiromichi

モノイドと半環
ProofCafe での説明用に、Eqivalence を省いた、説明用の簡易版

A Gentle Introduction to Type Classes and Relations in Coq
の
Chapter 3.9.2 Operational Type Classes の後半の抜粋・改変

typeclassestut.pdf
typeclassesTut/Monoid_op_classes.v
*)

Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq.

Set Implicit Arguments.
Unset Printing Implicit Defensive.
(* Set Print All. *)

(* ************* *)
(* ** 2x2行列 ** *)
(* ************* *)
Section mat.                                (* matrices. *)
  Variables (A : Type)
            (zero one : A) 
            (plus mult minus : A -> A -> A)
            (sym : A -> A).
  
  Notation "0" := zero.
  Notation "1" := one.
  Notation "x + y" := (plus x y).  
  Notation "x * y " := (mult x y).
  
  Structure M2 : Type :=
    {
      c00 : A; c01 : A;
      c10 : A; c11 : A
    }.
  
  Definition Zero2 : M2 := Build_M2 0 0 0 0.
  Definition Id2 : M2 := Build_M2 1 0 0 1.
  
  Definition M2_mult (m m':M2) : M2 :=
(*
  Build_M2 (c00 m * c00 m' + c01 m * c10 m')
           (c00 m * c01 m' + c01 m * c11 m')
           (c10 m * c00 m' + c11 m * c10 m')
           (c10 m * c01 m' + c11 m * c11 m').
*)
    {|
      c00 := c00 m * c00 m' + c01 m * c10 m';
      c01 := c00 m * c01 m' + c01 m * c11 m';
      c10 := c10 m * c00 m' + c11 m * c10 m';
      c11 := c10 m * c01 m' + c11 m * c11 m'
    |}.
  
  Definition M2_plus (m m' : M2) : M2 :=
    {|
      c00 := c00 m + c00 m';
      c01 := c01 m + c01 m';
      c10 := c10 m + c10 m';
      c11 := c11 m + c11 m'
    |}.
  
  Lemma M2_eq_intros :
    forall m m' : M2,
      c00 m = c00 m' -> c01 m = c01 m' ->
      c10 m = c10 m' -> c11 m = c11 m' ->
      m = m'.
  Proof.
    elim=> m00 m01 m10 m11 /=.
    elim=> m'00 m'01 m'10 m'11 /=.
    move=> H H1 H2 H3.
    by rewrite H H1 H2 H3.
  Qed.
End mat.                                    (* matrices. *)

(****************)
(*** モノイド ***)
(****************)
(*
Operational Type Classe
monoid_op はコンストラクタではなく、単に monoid_op f が f に簡約される。
 *)
Section Monoid.
  Class monoid_binop (A : Type) := monoid_op : A -> A -> A.
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
Section SemiRing.
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
  
  Class Distribute {A : Type} (f g : A -> A -> A): Prop :=
    {
      distribute_l a b c: f a (g b c) = g (f a b) (f a c);
      distribute_r a b c: f (g a b) c = g (f a c) (f b c)
    }.
  
  Class Commutative {A B : Type} (m : A -> A -> B): Prop := 
    commutativity x y : m x y = m y x.
  
  Class Absorb {A : Type} (m : A -> A -> A) (x : A) : Prop := 
    {
      absorb_l c : m x c = x;
      absorb_r c : m c x = x
    }.
  
  Class CommutativeMonoid {A : Type} (M_dot : monoid_binop A) (M_one : A) :=
    {
      commmonoid_monoid :> Monoid M_dot M_one;
      commmonoid_commutative :> Commutative M_dot
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
    Context `{SA : SemiRing A}.             (* Aは、Generalizable Variable *)
    
    (* テスト *)
    Check 0 * (1 + 1) : A.
    Check 0 * (1 + 1) = 0 : Prop.
    
    Definition ringtwo := 1 + 1.
    Lemma ringtwomult : forall x : A, ringtwo * x = x + x.
    Proof.
      move=> x.
      rewrite distribute_r.                 (* ring_dist の :> が効く。 *)
      by rewrite [1 * x]M_one_left.         (* add_monoid と mul_monoid の :> が効く。 *)
    Qed.
    
    Lemma eq_abcd_acbd (a b c d : A) :      (* 後で使う。 *)
      (a + b) + (c + d) = (a + c) + (b + d).
    Proof.
      rewrite -[(a + b) + (c + d)]M_dot_assoc. (* hit が有効 *)
      rewrite -[(a + c) + (b + d)]M_dot_assoc.
      rewrite /monoid_op.
      rewrite [(R_plus b (R_plus c d))]M_dot_assoc.
      rewrite [(R_plus c (R_plus b d))]M_dot_assoc.
      rewrite /monoid_op.
      by rewrite [(R_plus b c)]commutativity.
    Qed.
  End SemiRingTheory.
  
  (***********************)
  (* 具体的な半環を作る。 *)
  (***********************)
  (* 自然数 *)
  Section NatSemiRing.
    (* + *)
    Instance Nat_plus_op : monoid_binop nat := addn.
    Instance nat_plus : RingPlus nat := Nat_plus_op.
    
    (* 0 *)
    Instance nat_zero : RingZero nat := 0%nat.
    
    (* * *)
    Instance Nat_mult_op : monoid_binop nat := muln.
    Instance nat_mult : RingMult nat := Nat_mult_op.
    
    (* 1 *)
    Instance nat_one : RingOne nat := 1%nat.
    (* Section mat の Vaiables (zero one : A) の順番を守ること。 *)
    
    (* テスト *)
    Check 0 * (1 + 1) : nat.
    
    Program Instance Nat_Commutative : Commutative nat_plus.
    Next Obligation.
    Proof.
      rewrite /nat_plus /Nat_plus_op. 
      by rewrite addnC.                     (* ring でもよい。 *)
    Qed.
    
    Program Instance Nat_Monoid_plus : Monoid nat_plus nat_zero.
    Next Obligation.
    Proof.
      rewrite /monoid_op /nat_plus /Nat_plus_op. 
      by rewrite addnA.                     (* ring *)
    Qed.
    
    Program Instance Nat_CommutativeMonoid : CommutativeMonoid nat_plus nat_zero.
    (* No Obligations *)
    
    Program Instance Nat_Monoid_mult : Monoid nat_mult nat_one.
    Next Obligation.
      rewrite /monoid_op /nat_mult /Nat_mult_op.
      by rewrite mulnA.                     (* ring *)
    Qed.
    Next Obligation.
      rewrite /monoid_op /nat_one /nat_mult /Nat_mult_op.
      by rewrite mul1n.                     (* ring *)
    Qed.
    Next Obligation.
      rewrite /monoid_op /nat_one /nat_mult /Nat_mult_op.
      by rewrite muln1.                     (* ring *)
    Qed.
    
    Program Instance Nat_Distribute : Distribute nat_mult nat_plus.
    Next Obligation.
    Proof.
      rewrite /monoid_op /nat_mult /Nat_mult_op /nat_plus /Nat_plus_op.
      by rewrite mulnDr.                    (* ring *)
    Qed.
    Next Obligation.
    Proof.
      rewrite /monoid_op /nat_mult /Nat_mult_op /nat_plus /Nat_plus_op.
      by rewrite mulnDl.                    (* ring *)
    Qed.
    
    Program Instance Nat_Absorb : Absorb nat_mult nat_zero.
    (* No Obligations *)
    
    Program Instance Nat_SemiRing : SemiRing nat_plus nat_zero nat_mult nat_one.
    (* No Obligations *)
  End NatSemiRing.

  (* 任意の半環な型を要素とする2x2行列 *)
  Section M2ASemiRing.
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
    
    Program Instance M2A_Commutative : Commutative m2a_plus.
    Next Obligation.
    Proof.
      rewrite /m2a_plus /M2A_plus_op /M2_plus.
      f_equal; apply: (@commutativity A A ring_plus _). (* Hintの無い場合 *)
      Undo.
      f_equal; apply: commutativity.        (* Hintがあるなら *)
      Undo.
      f_equal; rewrite [R_plus _ _]commutativity; by []. (* Hint が要る。 *)
    Qed.
    
    Program Instance M2A_Monoid_plus : Monoid m2a_plus m2a_zero.
    Next Obligation.
      rewrite /monoid_op /m2a_plus /M2A_plus_op /M2_plus /=.
      by f_equal; apply: M_dot_assoc.
    Qed.
    Next Obligation.
      elim: x=> x00 x01 x10 x11.            (* M2の要素に分ける。 *)
      rewrite /monoid_op /m2a_plus /M2A_plus_op /M2_plus.
      rewrite /m2a_zero /Zero2 /=.
      f_equal; apply: M_one_left.
    Qed.
    Next Obligation.
      elim: x=> x00 x01 x10 x11.            (* M2の要素に分ける。 *)
      rewrite /monoid_op /m2a_plus /M2A_plus_op /M2_plus.
      rewrite /m2a_zero /Zero2 /=.
      f_equal; apply: M_one_right.
    Qed.
    
    Program Instance M2A_CommutativeMonoid : CommutativeMonoid m2a_plus m2a_zero.
    (* No Obligations *)
    
    Program Instance M2A_Monoid_mult : Monoid m2a_mult m2a_one.
    Next Obligation.
    Proof.
      (* monoid_op x (monoid_op y z) = monoid_op (monoid_op x y) z *)
      rewrite /monoid_op /m2a_mult /M2A_mult_op /M2_mult /=.
      f_equal;
      rewrite 2![(R_mult (_ x) (R_plus (R_mult (_ y) (_ z)) (R_mult (_ y) (_ z))))]
              distribute_l;
      rewrite 2![(R_mult (R_plus (R_mult (_ x) (_ y)) (R_mult (_ x) (_ y))) (_ z))]
              distribute_r;
      rewrite [R_plus (R_plus _ _) (R_plus _ _)]eq_abcd_acbd;
      rewrite /ring_plus; f_equal;
      rewrite -2![(R_mult (R_mult (_ x) (_ y)) (_ z))]M_dot_assoc;
      by rewrite /monoid_op.
    Qed.
    Next Obligation.
    Proof.
      (* monoid_op m2a_one x = x *)
      rewrite /monoid_op /m2a_mult /M2A_mult_op /M2_mult /=.
      rewrite 4![R_mult R_one _]M_one_left.
      rewrite 4![R_mult R_zero _]absorb_l.
      rewrite 2![R_plus _ R_zero]M_one_right.
      rewrite 2![R_plus R_zero _]M_one_left.
      by apply M2_eq_intros.
    Qed.
    Next Obligation.
    Proof.
      (* monoid_op x m2a_one = x *)
      rewrite /monoid_op /m2a_mult /M2A_mult_op /M2_mult /=.
      rewrite 4![R_mult _ R_one]M_one_right.
      rewrite 4![R_mult _ R_zero]absorb_r.
      rewrite 2![R_plus R_zero _]M_one_left.
      rewrite 2![R_plus _ R_zero]M_one_right.
      by apply M2_eq_intros.
    Qed.
    
    Program Instance M2A_Distribute : Distribute m2a_mult m2a_plus.
    Next Obligation.
    Proof.
      (* m2a_mult a (m2a_plus b c) = m2a_plus (m2a_mult a b) (m2a_mult a c) *)
      rewrite /m2a_mult /M2A_mult_op /M2_mult /=.
      rewrite /m2a_plus /M2A_plus_op /M2_plus /=.
      f_equal;
      rewrite 2!distribute_l;
      by rewrite [R_plus (R_plus _ _) (R_plus _ _)]eq_abcd_acbd; rewrite /ring_plus.
    Qed.
    Next Obligation.
    Proof.
      (* m2a_mult (m2a_plus a b) c = m2a_plus (m2a_mult a c) (m2a_mult b c) *)
      rewrite /m2a_mult /M2A_mult_op /M2_mult /=.
      rewrite /m2a_plus /M2A_plus_op /M2_plus /=.
      f_equal;
      rewrite 2!distribute_r;
      by rewrite [R_plus (R_plus _ _) (R_plus _ _)]eq_abcd_acbd; rewrite /ring_plus.
    Qed.
    
    Program Instance M2A_Absorb : Absorb m2a_mult m2a_zero.
    Next Obligation.
    Proof.
      rewrite /monoid_op /m2a_mult /M2A_mult_op /M2_mult.
      rewrite /m2a_plus /M2A_plus_op /M2_plus.
      rewrite /m2a_zero /Zero2 /=.
      by f_equal;
      rewrite 2![R_mult R_zero _]absorb_l;
      rewrite [R_plus R_zero R_zero]M_one_left.
    Qed.
    Next Obligation.
    Proof.
      rewrite /monoid_op /m2a_mult /M2A_mult_op /M2_mult.
      rewrite /m2a_plus /M2A_plus_op /M2_plus.
      rewrite /m2a_zero /Zero2 /=.
      by f_equal;
      rewrite 2![R_mult _ R_zero]absorb_r;
      rewrite [R_plus R_zero R_zero]M_one_left.
    Qed.
    
    Program Instance M2A_SemiRing : SemiRing m2a_plus m2a_zero m2a_mult m2a_one.
    (* No Obligations *)

  End M2ASemiRing.
  
  Section M2NatSemiRing.
    (* 自然数を要素とする2x2行列 *)

    (* + *)
    Definition M2nat_plus_op : monoid_binop (M2 nat) := @M2A_plus_op nat Nat_plus_op.
    Definition m2nat_plus : RingPlus (M2 nat) := @m2a_plus nat nat_plus.

    (* 0 *)
    Definition m2nat_zero : RingZero (M2 nat) := @m2a_zero nat nat_zero.

    (* * *)
    Definition M2nat_mult_op : monoid_binop (M2 nat) := @M2A_mult_op nat Nat_plus_op Nat_mult_op.
    Definition m2nat_mult : RingMult (M2 nat) := @m2a_plus nat nat_mult.
    
    (* 1 *)
    Definition m2nat_one : RingOne (M2 nat) := @m2a_one nat nat_zero nat_one.
    
    (* テスト *)
    Check {| c00 := 0; c01 := 0; c10 := 0; c11 := 0 |} *
    {| c00 := 1; c01 := 0; c10 := 0; c11 := 1 |} +
    {| c00 := 1; c01 := 0; c10 := 0; c11 := 1 |} : M2 nat.
    
    Program Instance M2Nat_Commutative : Commutative m2nat_plus.
    Next Obligation.
    Proof.
      rewrite /m2nat_plus /m2a_plus /M2A_plus_op /M2_plus /nat_plus /Nat_plus_op /=.
      apply M2_eq_intros; rewrite /=; ring.
    Qed.
    
    Program Instance M2Nat_Monoid_plus : Monoid m2nat_plus m2nat_zero.
    Next Obligation.
    Proof.
      rewrite /monoid_op /m2nat_plus /m2a_plus /M2A_plus_op /M2_plus /nat_plus /Nat_plus_op /=.
      apply M2_eq_intros; rewrite /=; ring.
    Qed.
    Next Obligation.
      rewrite /monoid_op /m2nat_zero /m2a_zero /nat_zero /Zero2
              /m2nat_plus /m2a_plus /M2A_plus_op /M2_plus /nat_plus /Nat_plus_op.
      apply M2_eq_intros; rewrite /=; ring.
    Qed.
    Next Obligation.
      rewrite /monoid_op /m2nat_zero /m2a_zero /nat_zero /Zero2
              /m2nat_plus /m2a_plus /M2A_plus_op /M2_plus /nat_plus /Nat_plus_op.
      apply M2_eq_intros; rewrite /=; ring.
    Qed.
    
    Program Instance M2Nat_SemiRing : SemiRing m2nat_plus m2nat_zero m2nat_mult m2nat_one.
    Next Obligation.
    Proof.
      admit.
    Qed.
    Next Obligation.
    Proof.
      admit.
    Qed.
    Next Obligation.
    Proof.
      admit.
    Qed.
    Next Obligation.
    Proof.
      admit.
    Qed.
(*
    このように、M2Nat_Seiming の証明は、m2nat の要素(nat)に分解すれば、証明できるだろう。
    しかし、M2A_SemiRing と Nat_Semiring から、M2Nat_Semiring を合成することができないのだろうか。

    これはうまくいかない：

    Definition M2Nat_SemiRing : SemiRing m2nat_plus m2nat_zero m2nat_mult m2nat_one :=
      @M2A_SemiRing nat nat_plus nat_zero nat_mult nat_one Nat_SemiRing.
*)
    (* これはうまくいくが、型が行列を要素とする行列 *)
    Definition M2M2Nat_SemiRing : SemiRing m2a_plus m2a_zero m2a_mult m2a_one :=
      @M2A_SemiRing (M2 nat) m2nat_plus m2nat_zero m2nat_mult m2nat_one M2Nat_SemiRing.
    
    End M2NatSemiRing.
End SemiRing.

(* END *)
