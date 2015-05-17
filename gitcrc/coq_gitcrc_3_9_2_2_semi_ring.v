(**
A Gentle Introduction to Type Classes and Relations in Coq
の
Chapter 3.9.2 Operational Type Classes の後半抄訳

typeclassestut.pdf
typeclassesTut/Monoid_op_classes.v
*)

Set Implicit Arguments.
Unset Printing Implicit Defensive.
Set Print All.

Require Import ZArith.                      (* 整数 *)
Require Import Relations.
Require Import Mat.                         (* coq_gitcrc_2_Monoid.v 参照 *)
Require Import Coq.Setoids.Setoid.          (* relation *)
Require Import Morphisms.                   (* Proper *)

(****************************************)
(*** Monoids with equivalence : EMonoid *)
(****************************************)
(*
If we want to consider monoids w.r.t. some equivalence relation, it is possible to
associate an operational type class to the considered relation:

モノイドを同値関係として考えるとき、operational type class としてまとめることが可能である。
*)
Class Equiv (A : Type) := equiv : relation A. (* Operational Type Classes *)
Infix "==" := equiv (at level 70) : type_scope.

Class monoid_binop (A : Type) := monoid_op : A -> A -> A.
(* Unlike multi-field class types, monoid_op is not a constructor, but a transparent
constant such that monoid_op f can be δβ-reduced into f.

monoid_op はコンストラクタではなく、単に monoid_op f が f に簡約される。
 *)

Section EMonoid.
  Local Infix "*" := monoid_op: M_scope.
  Local Open Scope M_scope.
  
  Class EMonoid (A : Type) (E_eq : Equiv A) (E_dot : monoid_binop A) (E_one : A) :=
    {
      E_rel :> Equivalence equiv; 
      dot_proper :> Proper (equiv ==> equiv ==> equiv) monoid_op; 
      (* x == y -> n == p -> monoid_op x n == monoid_op y p *)
      E_dot_assoc : forall x y z : A, x * (y * z) == x * y * z;
      E_one_left  : forall x : A, E_one * x == x;
      E_one_right : forall x : A, x * E_one == x
    }.
  Locate Proper.                              (* Constant Coq.Classes.Morphisms.Proper *)
  Locate "_ ==> _".                           (* respectful R R' : signature_scope *)
  
  (* E_rel は、EMonoid _ _ _ _ から Equivalence _ へのコアーションである。
EMonoid が 同値関係を持つ（Equivalenceから継承する）ことを示す。 *)
  
  Check Equivalence equiv : Prop.
  (* 
The overloaded == notation will refer to the appropriate equivalence relation on the
type of the arguments.
オーバーロードされた「==」は、引数の型に応じて適切な同値関係を参照するであろう。

One can develop in this fashion a hierarchy of structures. In the
following we define the structure of semirings starting from a refinement of EMonoid.
   *)
End EMonoid.

Module SemiRing.
  Generalizable Variables A B.
  
  (* Overloaded notations *)
  Class RingOne A := ring_one : A.            (* Operational Type Classes *)
  Class RingZero A := ring_zero : A.          (* Operational Type Classes *)
  Class RingPlus A := ring_plus :> monoid_binop A. (* Operational Type Classes *)
  Class RingMult A := ring_mult :> monoid_binop A. (* Operational Type Classes *)
  Infix "+" := ring_plus.
  Infix "*" := ring_mult.
  Notation "0" := ring_zero.
  Notation "1" := ring_one.
  
  Typeclasses Transparent RingPlus RingMult RingOne RingZero.
  
  Class Distribute `{Equiv A} (f g: A -> A -> A): Prop :=
    {
      distribute_l a b c: f a (g b c) == g (f a b) (f a c);
      distribute_r a b c: f (g a b) c == g (f a c) (f b c)
    }.
  
  Class Commutative {A B} `{Equiv B} (m: A -> A -> B): Prop := 
    commutativity x y : m x y == m y x.
  
  Class Absorb {A} `{Equiv A} (m: A -> A -> A) (x : A) : Prop := 
    {
      absorb_l c : m x c == x;
      absorb_r c : m c x == x
    }.
  
  Class ECommutativeMonoid `(Equiv A) (E_dot : monoid_binop A) (E_one : A) :=
    {
      e_commmonoid_monoid :> EMonoid equiv E_dot E_one;
      e_commmonoid_commutative :> Commutative E_dot
    }.
  
  Class ESemiRing (A:Type)
        (E_eq : Equiv A)
        (E_plus : RingPlus A)
        (E_zero : RingZero A)
        (E_mult : RingMult A)
        (E_one : RingOne A) :=
    {
      add_monoid :> ECommutativeMonoid equiv ring_plus ring_zero;
      mul_monoid :> EMonoid equiv ring_mult ring_one;
      ering_dist :> Distribute ring_mult ring_plus;
      ering_0_mult :> Absorb ring_mult 0
    }.
  Print Distribute.                           (* 分配則 *)
  Print Absorb.                               (* 零元 *)
  About absorb_l.                             (* 右側の零元 *)
  (* 
Note that we use a kind of multiple inheritance here, as a semiring contains two monoids,
半環がふたつのモノイドを含むために、一種の多重継承を使うことに注意せよ。

one for addition and one for multiplication, that are related by distributivity and absorbtion laws.
ひとつは加算でひとつは積算で、これらは分配則と吸収則(absorbtion laws)に関係する。

To distinguish between the corresponding monoid operations, we introduce the new operational type classes Ring*.
対応したモノイドの操作を区別するために、新しい operational type classes である Ringなんとか を導入する。

These classes are declared Transparent for typeclass resolution, so that their expansion
to monoid_binop can be used freely during conversion: they are just abbreviations used for
overloading notations.
それでこれらのmonoid_binopへの拡張は変換を通じて公平に使われるように、
これらのクラスは、typeclass resolution の透明性を宣言される。
これらは、オーバーローディング記法のための短縮形が使われる。

We also introduce classes for the standard properties of operations like commutativity,
distributivity etc... to be able to refer to them generically.
可換性や分配性などのためにも、またクラスを導入する。

We can now develop some generic theory on semirings using the overloaded lemmas about
distributivity or the constituent monoids. Resolution automatically goes through the
ESemiRing structure to find proofs regarding the underlying monoids.
   *)
  
  Section SemiRingTheory.
    Context `{M : ESemiRing A}.
    
    (* テスト *)
    Check 0 * (1 + 1) : A.
    Check 0 * (1 + 1) == 0 : Prop.
    
    Instance Test_Proper :                  (* `(M : ESemiRing A) *)
      Proper (equiv ==> equiv ==> equiv) monoid_op.
    Proof.
      intros x y Hxy z u Hzu.
      now rewrite Hxy, Hzu.
    Qed.

    Instance Test_Proper' :
      Proper (equiv ==> equiv ==> equiv) ring_plus.
    Proof.
      intros x y Hxy z u Hzu.
      rewrite Hxy.
      (*
      rewrite Hzu.
      reflexivity. *)
      admit.
    Qed.
    
    Locate "_ + _".
    Goal forall a b c d : A, a == b -> c == d -> a + c == b + d.
    intros a b c d H1 H2.
    rewrite H1.
    (*
    rewrite H2.
    reflexivity.
     *)
    admit.
    Qed.
    
    Definition ringtwo := 1 + 1.
    Lemma ringtwomult : forall x : A, ringtwo * x == x + x.
    Proof.
      intros.
      unfold ringtwo.
      rewrite distribute_r.                   (* ering_dist の :> が効く。 *)
      (* EMonoid の E_rel の :> も効く。 *)
      now rewrite (E_one_left x).             (* add_monoid と mul_monoid の :> が効く。 *)
    Qed.
  End SemiRingTheory.
  
  (* ************** *)
  (* ***補足******* *)
  (* ************** *)
  (* ** M2Z Ring ** *)
  (* 整数を要素とする2x2行列 *)
  Section M2Z_Ring.
    
    (* == *)
    Instance m2z_eq : Equiv (M2 Z) := eq.
    
    (* + *)
    Instance M2Z_plus_op : monoid_binop (M2 Z) := (@M2_plus Z Zplus). (* Mat.v *)
    Instance m2z_plus : RingPlus (M2 Z) := M2Z_plus_op.
    
    (* 0 *)
    Instance m2z_zero : RingZero (M2 Z) := Zero2 0%Z. (* Mat.v *)
    
    (* * *)
    Instance M2Z_mult_op : monoid_binop (M2 Z) := (@M2_mult Z Zplus Zmult). (* Mat.v *)
    Instance m2z_mult : RingMult (M2 Z) := M2Z_mult_op.

    (* 1 *)
    Instance m2z_one : RingOne (M2 Z) := Id2 1%Z 0%Z.
    
    (* テスト *)
    Check 0 * (1 + 1) : M2 Z.
    Check 0 * (1 + 1) == 0 : Prop.

    Goal forall a b : M2 Z, a == b -> b + a == a + b.
    intros a b H.
    rewrite H.
    reflexivity.
    Qed.

    (* --------------------------- *)
    (* Semi Ring の定理を証明する。 *)
    (* --------------------------- *)    
    Instance M2Z_Commutative : Commutative m2z_plus.
    Proof.
      unfold Commutative.
      intros x y.
      unfold m2z_plus, M2Z_plus_op, M2_plus, equiv, m2z_eq.
      f_equal;
      apply Zplus_comm.
    Qed.
    
    Program Instance M2Z_EMonoid_plus : EMonoid m2z_eq m2z_plus m2z_zero.
    Next Obligation.
      unfold monoid_op, m2z_plus, M2Z_plus_op, M2_plus, equiv, m2z_eq.
      now simpl; f_equal; apply Zplus_assoc.
    Qed.
    Next Obligation.
      destruct x.                           (* 要素に分ける。 *)
      unfold monoid_op, m2z_plus, M2Z_plus_op, M2_plus.
      unfold m2z_zero, Zero2.
      unfold equiv, m2z_eq.
      now simpl.
    Qed.
    Next Obligation.
      destruct x.                           (* M2の要素に分ける。 *)
      unfold monoid_op, m2z_plus, M2Z_plus_op, M2_plus.
      unfold m2z_zero, Zero2.
      unfold equiv, m2z_eq.
      simpl.
      rewrite Z.add_0_r.
      rewrite Z.add_0_r.
      rewrite Z.add_0_r.
      rewrite Z.add_0_r.
      reflexivity.
    Qed.
    
    Program Instance M2Z_ECommutativeMonoid : ECommutativeMonoid m2z_eq m2z_plus m2z_zero.
    (* No Obligation *)
    
    Program Instance M2Z_EMonoid_mult : EMonoid m2z_eq m2z_mult m2z_one.
    Next Obligation.
      unfold monoid_op, m2z_mult, M2Z_mult_op, M2_mult, equiv, m2z_eq.
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
      unfold equiv, m2z_eq.
      admit.
    Qed.
    Next Obligation.
      case x; admit.
    Qed.
    
    Program Instance M2Z_Distribute : Distribute m2z_mult m2z_plus.
    Next Obligation.
    Proof.
      unfold monoid_op, m2z_mult, M2Z_mult_op, M2_mult.
      unfold m2z_plus, M2Z_plus_op, M2_plus.
      unfold equiv, m2z_eq.
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
      unfold equiv, m2z_eq.
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
      reflexivity.
    Qed.
    Next Obligation.
    Proof.
      unfold monoid_op, m2z_mult, M2Z_mult_op, M2_mult.
      unfold m2z_zero, Zero2.
      simpl.
      repeat rewrite <- Zmult_0_r_reverse.
      reflexivity.
    Qed.
    
    Program Instance M2Z_SemiRing : ESemiRing m2z_eq m2z_plus m2z_zero m2z_mult m2z_one.
    (* No Obligation *)
    
  End M2Z_Ring.
  (* ** M2Z Ring 終わり ** *)
  
  (* ** M2A Ring ** *)
  (* 任意のSemiRringな型を要素とする2x2行列 *)
  Section M2A_Ring.
    (* Aは、Generalizable Variables *)
    Context `{M2A : ESemiRing A}.
    
    (* == *)
    Definition M2_equal (m m' : M2 A) : Prop := eq m m'.
    Instance m2a_eq : Equiv (M2 A) := M2_equal.
    
    (* + *)
    Instance M2A_plus_op : monoid_binop (M2 A) := (@M2_plus A E_plus).
    Instance m2a_plus : RingPlus (M2 A) := M2A_plus_op.

    (* 0 *)
    Instance m2a_zero : RingZero (M2 A) := Zero2 E_zero. (* Mat.v *)
    
    (* * *)
    Instance M2A_mult_op : monoid_binop (M2 A) := (@M2_mult A E_plus E_mult). (* Mat.v *)
    Instance m2a_mult : RingMult (M2 A) := M2A_mult_op.
    
    (* 1 *)
    Instance m2a_one : RingOne (M2 A) := Id2 E_one E_zero.
    
    (* テスト *)
    Check 0 * (1 + 1) : M2 A.
    Check 0 * (1 + 1) == 0 : Prop.

    Goal forall a b : M2 A, a == b -> b + a == a + b.
    intros a b H.
    rewrite H.
    reflexivity.
    Qed.
    
    Lemma test x00 x01 x10 x11 y00 y01 y10 y11 :
      x00 == y00 ->
      x01 == y01 ->
      x10 == y10 ->
      x11 == y11 -> 
      {| c00 := x00;
         c01 := x01;
         c10 := x10;
         c11 := x11 |} ==
      {| c00 := y00;
         c01 := y01;
         c10 := y10;
         c11 := y11 |}.
    Proof.
      intros H00 H01 H10 H11.
    Admitted.
    
    (* --------------------------- *)
    (* Semi Ring の定理を証明する。 *)
    (* --------------------------- *)    
    Instance M2A_Commutative : Commutative m2a_plus.
    Proof.
      unfold Commutative.
      intros x y.
      unfold m2a_plus, M2A_plus_op, M2_plus.
      apply test; apply commutativity.
    Qed.
    (* M2 A の場合は、f_equall で要素毎(型A)の「=」に分解すると、先が続かなくなる。 *)
    
    Program Instance M2A_EMonoid_plus : EMonoid m2a_eq m2a_plus m2a_zero.
    Next Obligation.
      unfold monoid_op, m2a_plus, M2A_plus_op, M2_plus.
      simpl; apply test; apply E_dot_assoc.
    Qed.
    Next Obligation.
      destruct x.                           (* 要素に分ける。 *)
      unfold monoid_op, m2a_plus, M2A_plus_op, M2_plus.
      unfold m2a_zero, Zero2.
      simpl; apply test; apply E_one_left.
    Qed.
    Next Obligation.
      destruct x.                           (* M2の要素に分ける。 *)
      unfold monoid_op, m2a_plus, M2A_plus_op, M2_plus.
      unfold m2a_zero, Zero2.
      simpl; apply test; apply E_one_right.
    Qed.
    
    Program Instance M2A_ECommutativeMonoid : ECommutativeMonoid m2a_eq m2a_plus m2a_zero.
    (* No Obligation *)
    
    Program Instance M2A_EMonoid_mult : EMonoid m2a_eq m2a_mult m2a_one.
    Next Obligation.
      unfold monoid_op, m2z_mult, M2Z_mult_op, M2_mult.
      apply test; simpl.
      rewrite commutativity.
      rewrite (@commutativity _ _ _ E_mult).
      rewrite commutativity.
      rewrite (@commutativity _ _ _ E_mult).
    Admitted.
    Next Obligation.
      destruct x.
      unfold monoid_op, m2z_mult, M2Z_mult_op, M2_mult.
      unfold m2a_one, Id2.
      apply test; simpl.
      rewrite absorb_l.
    Admitted.
    Next Obligation.
    Admitted.
    
    Program Instance M2A_Distribute : Distribute m2a_mult m2a_plus.
    Next Obligation.
    Proof.
      unfold monoid_op, m2a_mult, M2A_mult_op, M2_mult.
      unfold m2a_plus, M2A_plus_op, M2_plus.
      apply test; simpl.
      rewrite distribute_l.
      (* rewrite distribute_l. *)
      Admitted.
    Next Obligation.
    Proof.
      unfold monoid_op, m2a_mult, M2A_mult_op, M2_mult.
      unfold m2a_plus, M2A_plus_op, M2_plus.
      apply test; simpl.
      rewrite distribute_r.
      (* rewrite distribute_l. *)
      Admitted.
    
    Program Instance M2A_Absb : Absorb m2a_mult m2a_zero.
    Next Obligation.
    Proof.
      unfold monoid_op, m2a_mult, M2A_mult_op, M2_mult.
      unfold m2a_zero, Zero2.
      apply test; simpl.
      rewrite absorb_l.
    Admitted.
    Next Obligation.
    Proof.
      unfold monoid_op, m2a_mult, M2A_mult_op, M2_mult.
      unfold m2a_zero, Zero2.
      apply test; simpl.
      rewrite absorb_r.
    Admitted.
    
    Program Instance M2A_SemiRing : ESemiRing m2a_eq m2a_plus m2a_zero m2a_mult m2a_one.
    (* No Obligation *)

  End M2A_Ring.
  (* ** M2A Ring 終わり ** *)
  
(* ******************** *)
(* ***補足 終わり******* *)
(* ******************** *)
  
End SemiRing.

(* END *)
