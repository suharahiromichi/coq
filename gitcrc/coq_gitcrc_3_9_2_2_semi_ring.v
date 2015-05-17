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
Class Equiv A := equiv : relation A.        (* Operational Type Classes *)
Infix "==" := equiv (at level 70) : type_scope.

Class monoid_binop (A:Type) := monoid_op : A -> A -> A.
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
    Context `{ESemiRing A}.
    
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
  (* ** M2 Ring ** *)
  Section M2Z_Ring.

    (* == *)
    (* = と == が同じ意味になる。 *)
    Instance m2_eq : Equiv (M2 Z) := eq.
    
    (* + *)
    Instance M2Z_plus_op : monoid_binop (M2 Z) := (@M2_plus Z Zplus). (* Mat.v *)
    Instance m2_plus : RingPlus (M2 Z) := M2Z_plus_op.
    
    (* 0 *)
    Instance m2_zero : RingZero (M2 Z) := Zero2 0%Z. (* Mat.v *)
    
    (* * *)
    Instance M2Z_mult_op  : monoid_binop (M2 Z) := (@M2_mult Z Zplus Zmult). (* Mat.v *)
    Instance m2_mult : RingMult (M2 Z) := @M2Z_mult_op.

    (* 1 *)
    Instance m2_one : RingOne (M2 Z) := Id2 1%Z 0%Z.
    
    Check 0 * (1 + 1) : M2 Z.
    Check 0 * (1 + 1) == 0 : Prop.
    
    (* --------------------------- *)
    (* Semi Ring の定理を証明する。 *)
    (* --------------------------- *)    
    Instance M2Z_Commutative : Commutative m2_plus.
    Proof.
      unfold Commutative.
      intros x y.
      unfold m2_plus, M2Z_plus_op, M2_plus, equiv, m2_eq.
      f_equal; apply Zplus_comm.
    Qed.
    
    Program Instance M2Z_EMonoid_plus : EMonoid m2_eq m2_plus m2_zero.
    Next Obligation.
      unfold monoid_op, m2_plus, M2Z_plus_op, M2_plus, equiv, m2_eq.
      now simpl; f_equal; apply Zplus_assoc.
    Qed.
    Next Obligation.
      destruct x.                           (* 要素に分ける。 *)
      unfold monoid_op, m2_plus, M2Z_plus_op, M2_plus.
      unfold m2_zero, Zero2.
      unfold equiv, m2_eq.
      now simpl.
    Qed.
    Next Obligation.
      destruct x.                           (* M2の要素に分ける。 *)
      unfold monoid_op, m2_plus, M2Z_plus_op, M2_plus.
      unfold m2_zero, Zero2.
      unfold equiv, m2_eq.
      simpl.
      rewrite Z.add_0_r.
      rewrite Z.add_0_r.
      rewrite Z.add_0_r.
      rewrite Z.add_0_r.
      reflexivity.
    Qed.
    
    Program Instance M2Z_ECommutativeMonoid : ECommutativeMonoid m2_eq m2_plus m2_zero.
    (* No Obligation *)
    
    Program Instance M2Z_EMonoid_mult : EMonoid m2_eq m2_mult m2_one.
    Next Obligation.
      unfold monoid_op, m2_mult, M2Z_mult_op, M2_mult, equiv, m2_eq.
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
      unfold monoid_op, m2_mult, M2Z_mult_op, M2_mult.
      unfold m2_one, Id2.
      destruct x.
      unfold equiv, m2_eq.
      admit.
    Qed.
    Next Obligation.
      case x; admit.
    Qed.
    
    Program Instance M2Z_Distribute : Distribute m2_mult m2_plus.
    Next Obligation.
    Proof.
      unfold monoid_op, m2_mult, M2Z_mult_op, M2_mult.
      unfold m2_plus, M2Z_plus_op, M2_plus.
      unfold equiv, m2_eq.
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
      unfold monoid_op, m2_mult, M2Z_mult_op, M2_mult.
      unfold m2_plus, M2Z_plus_op, M2_plus.
      unfold equiv, m2_eq.
      simpl; f_equal;
      repeat rewrite Z.mul_add_distr_r;
      repeat rewrite Zplus_assoc;
      f_equal;
      repeat rewrite <- Zplus_assoc;
      f_equal;
      rewrite Z.add_comm;
      reflexivity.
    Qed.
    
    Program Instance M2Z_Absb : Absorb m2_mult m2_zero.
    Next Obligation.
    Proof.
      unfold monoid_op, m2_mult, M2Z_mult_op, M2_mult.
      unfold m2_zero, Zero2.
      simpl.
      reflexivity.
    Qed.
    Next Obligation.
    Proof.
      unfold monoid_op, m2_mult, M2Z_mult_op, M2_mult.
      unfold m2_zero, Zero2.
      simpl.
      repeat rewrite <- Zmult_0_r_reverse.
      reflexivity.
    Qed.
    
    Program Instance M2Z_SemiRing : ESemiRing m2_eq m2_plus m2_zero m2_mult m2_one.
    (* No Obligation *)
    
  End M2Z_Ring.
(* ** M2 Ring 終わり ** *)



(* ******************** *)
(* ***補足 終わり******* *)
(* ******************** *)
  
End SemiRing.

(* END *)
