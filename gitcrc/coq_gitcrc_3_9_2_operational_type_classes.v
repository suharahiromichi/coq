(**
A Gentle Introduction to Type Classes and Relations in Coq
の
Chapter 3.9.2 Operational Type Classes の抄訳

typeclassestut.pdf
typeclassesTut/Monoid_op_classes.v
*)

(* Examples of type classes and Setoids *)
(* Version with operational classes *)
(* Some comments by Matthieu *)

Set Implicit Arguments.
Require Import ZArith.
Require Import Div2.
Require Import Recdef.
Require Import Mat.                         (* coq_gitcrc_2_Monoid.v 参照 *)

(* Operational Type Classes:  *)
Class monoid_binop (A:Type) := monoid_op : A -> A -> A.
Delimit Scope M_scope with M.
(* Unlike multi-field class types, monoid_op is not a constructor, but a transparent
constant such that monoid_op f can be δβ-reduced into f.

monoid_op はコンストラクタではなく、単に monoid_op f が f に簡約される。
 *)
Infix "*" := monoid_op: M_scope.

Open Scope M_scope.
Class Monoid (A:Type) (dot : monoid_binop  A) (one : A) : Prop :=
  {
    dot_assoc : forall x y z:A, x * (y * z)=  x * y * z;
    one_left : forall x, one * x = x;
    one_right : forall x,  x * one = x
  }.

About one_right.
(*
one_right :
forall (A : Type) (dot : monoid_binop A) (one : A),
Monoid dot one -> forall x : A, x * one = x
*)

Require Import ZArith.
Open Scope Z_scope.

Print monoid_op.
Compute (@monoid_op _ Zmult 5 6).           (* 30 : Z *)

(* 整数の掛け算のモノイド *)
(* opとモノイドのふたつを組で定義する。 *)
Instance Zmult_op : monoid_binop Z | 17 := Zmult. (* monoid_binop の優先順位 17 *)
Check 2 * 5.                            (* 2 * 5 : Z *)
Compute 2 * 5.                          (* 10 : Z *)
Set Printing All.
Check 2 * 5.                            (* Z.mul (Zpos (xO xH)) (Zpos (xI (xO xH))) : Z *)
Compute 2 * 5.                          (* Zpos (xO (xI (xO xH))) : Z *)
Unset Printing All.
Instance ZMult : Monoid Zmult_op  1 | 22.   (* Monoid の優先順位 22 *)
Proof.
  split; intros; unfold Zmult_op, monoid_op; ring. 
Defined.                                    (* Qedでもよい。 *)

(* 任意の型Aの2x2行列の掛け算のモノイド *)
Require Import Ring.
Section matrices.
  Variables (A : Type)                      (* 任意の型 *)
            (zero one : A) 
            (plus mult minus : A -> A -> A)
            (sym : A -> A).
  Notation "0" := zero.
  Notation "1" := one.
  Notation "x + y" := (plus x y).  
  Notation "x * y " := (mult x y).
 
  Variable rt : ring_theory  zero one plus mult minus sym (@eq A).
  Add Ring Aring : rt.

  (* 組で定義する。 *)
  Global Instance M2_mult_op : monoid_binop (M2 A) := (M2_mult plus mult ) . 
  Global Instance M2_Monoid' : Monoid  M2_mult_op (Id2 0 1).
  Proof.
    split.
    destruct x; destruct y; destruct z; unfold monoid_op; simpl;
    unfold M2_mult; apply M2_eq_intros; simpl; ring.
    destruct x; simpl; unfold M2_mult_op, monoid_op; 
    unfold M2_mult;  apply M2_eq_intros; simpl; ring.
    destruct x; simpl; unfold M2_mult_op, monoid_op; 
    unfold M2_mult; apply M2_eq_intros; simpl; ring. 
  Defined.
  (* Program コマンドを使う。 *)
  Global Program Instance M2_Monoid : Monoid  M2_mult_op (Id2 0 1).
  Next Obligation.                          (* (x * (y * z))%M = (x * y * z)%M *)
  Proof.
    destruct x; destruct y; destruct z; unfold monoid_op; simpl.
    unfold M2_mult; apply M2_eq_intros; simpl; ring.
  Qed.
  Next Obligation.                          (* (Id2 0 1 * x)%M = x *)
  Proof.
    destruct x; simpl; unfold M2_mult_op, monoid_op.
    unfold M2_mult;  apply M2_eq_intros; simpl; ring.
  Qed.
  Next Obligation.                          (* (x * Id2 0 1)%M = x *)
    destruct x; simpl; unfold M2_mult_op, monoid_op.
    unfold M2_mult; apply M2_eq_intros; simpl; ring.
  Qed.
End matrices.

Generalizable Variables A dot one.          (* コンテキストで決まる変数 *)

(* 整数型の2x2行列の掛け算のモノイド *)
Instance M2_Z_op : monoid_binop (M2 Z) := M2_mult Zplus Zmult . 
Instance M2_mono_Z : Monoid (M2_mult_op _ _)  (Id2 _ _) := M2_Monoid Zth.

Compute ((Build_M2 1 1 1 0)*(Build_M2 1 1 1 0))%M.
(* {| c00 := 2; c01 := 1; c10 := 1; c11 := 1 |} : M2 Z *)
Compute ((Id2 0 1)*(Id2 0 1))%M.
(* {| c00 := 2; c01 := 1; c10 := 1; c11 := 1 |} : M2 Z *)

Fixpoint power `{M : @Monoid A dot one} (a : A) (n : nat) := (* Generalizable Variables を使う。 *)
  match n with
    | 0%nat => one
    | S p => (a * power a p)%M
  end.

Infix "**" := power (at level 30, no associativity) : M_scope.
Compute  (2 ** 5) ** 2.                     (* 1024 : Z *)
Unset Printing Implicit.
About M2_mult.

About M2_Monoid .
Check M2_Monoid Zth.

Compute (Build_M2  1 1 1  0) ** 40. 
(* {| c00 := 165580141; c01 := 102334155; c10 := 102334155; c11 := 63245986 |} : M2 Z *)
Compute (2 ** 5)%M.                         (* 32 : Z *)

(* ****************************** *)
(* power の計算の正しさを証明する。 *)
(* ****************************** *)
(* A tail recursive linear function、普通の定義 *)
Fixpoint power_mult `{M : Monoid } (acc x : A) (n : nat) : A
(* acc * (x ** n) *) :=
  (* A は、Monoid からジェネリックに決まる型 *)
  match n with
    | 0%nat => acc
    | S p => power_mult (acc * x)%M x p
  end.
Check power_mult.                     (* M2 Z -> M2 Z -> nat -> M2 Z これは、まやかし！ *)
About power_mult.
(* forall (A : Type) (dot : monoid_binop A) (one : A), Monoid dot one -> A -> A -> nat -> A *)

Definition tail_recursive_power  `{M : Monoid} (x : A) (n : nat) :=
  power_mult one x n.

Require Import Recdef.
Require Import Div2.

Function binary_power_mult (A : Type) (dot : monoid_binop A) (one : A) 
         (M: @Monoid A dot one) (acc x : A) (n : nat) {measure (fun i=>i) n} : A 
  (* acc * (x ** n) *) :=
  match n with
    | 0%nat => acc
    | _ => 
      match Even.even_odd_dec n with
        |  left H0 => binary_power_mult _ acc (dot x x) (div2 n)
        | right H1 => binary_power_mult _ (acc * x)%M ( x * x)%M (div2 n)
      end
  end.
Proof.
  intros; apply lt_div2; auto with arith.
  intros; apply lt_div2; auto with arith.
Defined.

Definition binary_power `{M : Monoid} (x : A) (n : nat) := 
  binary_power_mult M one x n.                                     (* Monoidの定義の変数が使われる *)
Definition binary_power' `{M : @Monoid A dot one} (x:A) (n:nat) := (* Generalizable Variables を使う。 *)
  binary_power_mult M one x n.
(* 補足説明：クラスの引数を指定する場合は、Generalizable Variables でなければならない。
クラスの引数を指定しない場合は、クラス定義で使われた変数が自動的に使われる。
上記では、両者の変数がが同じなのだが、その場合でも、そういうことになっているようだ。 *)

Compute 2 ** 5.
Compute binary_power 2 5.                   (* 32 : Z *)

Compute (Build_M2 1 1 1 0) ** 10.           (* {| c00 := 89; c01 := 55; c10 := 55; c11 := 34 |} : M2 Z *)
Compute binary_power (Build_M2 1 1 1 0) 10.

Compute (Build_M2 1 1 1 0) ** 20.
Compute binary_power (Build_M2 1 1 1 0) 20. (* {| c00 := 10946; c01 := 6765; c10 := 6765; c11 := 4181 |} : M2 Z *)

(*
All the techniques we used in Sect. 2.3.1 can be applied with operational type
classes. The main section of this proof is as follows:

2.3.1で使ったすべての手法は、operational type classes に適用できる。この証明の主題は以下である：
*)

Section About_power.
  Fail Check A.
  Context `(M : Monoid).                    (* モノイド定義の変数が使われる。 *)
(*  Context `(M : @Monoid A dot one). (* コンテキストが決まる（Generalizable Variables が埋まる）。 *) *)
  Check A.                                  (* A : Type, Monoid の A *)
  Check dot.                                (* dot : monoid_binop A *)
  Check one.                                (* one : A *)
  Check M.                                  (* M : Monoid dot one *)
  Open Scope M_scope.                       (* "*" や "**" が使えるようになる。 *)

  Ltac monoid_rw :=
    rewrite one_left || rewrite one_right || rewrite dot_assoc.

  Ltac monoid_simpl := repeat monoid_rw.
  
  Lemma power_x_plus :
    forall (x : A) (n p : nat), (x ** (n + p) = x ** n * x ** p).
  Proof.
    induction n; simpl. 
    intros; monoid_simpl; trivial.
    intro p; rewrite (IHn p); monoid_simpl; trivial.
  Qed.
  
  Ltac power_simpl := repeat (monoid_rw || rewrite <- power_x_plus).

  Lemma power_commute :
    forall x n p, x ** n * x ** p = x ** p * x ** n. 
  Proof.
    intros x n p; power_simpl; rewrite (plus_comm n p); trivial.
 Qed.

  Lemma power_commute_with_x :
    forall x n, x * x ** n = x ** n * x.
  Proof.
    induction n; simpl; power_simpl; trivial.
    repeat rewrite <- dot_assoc; rewrite IHn; trivial.
  Qed.

  Lemma power_of_power :
    forall x n p,  (x ** n) ** p = x ** (p * n).
  Proof.
    induction p; simpl; [| rewrite power_x_plus; rewrite IHp]; trivial.
  Qed.

  Lemma power_S :
    forall x n, x *  x ** n = x ** S n.
  Proof.
    intros; simpl; auto.
  Qed.

  Lemma sqr : forall x, x ** 2 =  x * x.
  Proof.
    simpl; intros; monoid_simpl; trivial.
  Qed.

  Ltac factorize := repeat (
                rewrite <- power_commute_with_x ||
                rewrite <- power_x_plus  ||
                rewrite <- sqr ||
                rewrite power_S ||
                rewrite power_of_power).

  Lemma power_of_square :
    forall x n, (x * x) ** n = x ** n * x ** n.
    induction n; simpl; monoid_simpl; trivial.
    repeat rewrite dot_assoc; rewrite IHn;
    repeat rewrite dot_assoc.
    factorize; simpl; trivial.
 Qed.

  Lemma power_mult_correct : 
    forall n x, tail_recursive_power x n = x ** n.
  Proof.
    intros n x; unfold tail_recursive_power.
    rewrite <- (one_left  (power x n)).
    assert (forall y:A, power_mult y x n =  y * (power x n)); auto.
    generalize n x; intro p; induction p; simpl; intros; monoid_simpl; auto.
  Qed.

  Lemma binary_power_mult_ok :
    forall n a x, binary_power_mult  M a x n = a * x ** n.
  Proof.
    intro n; pattern n;apply lt_wf_ind.
    clear n; intros n Hn; destruct n.
    intros; simpl; rewrite binary_power_mult_equation; monoid_simpl;
    trivial.
    intros;  
      rewrite binary_power_mult_equation; destruct (Even.even_odd_dec (S n)).
    rewrite Hn.  rewrite power_of_square; factorize.
    pattern (S n) at 3; replace (S n) with (div2 (S n) + div2 (S n))%nat; auto.
    generalize (even_double _ e); simpl; auto.
    apply lt_div2;auto with arith.
    rewrite Hn.
    rewrite power_of_square ; factorize.
    pattern (S n) at 3; replace (S n) with (S (div2 (S n) + div2 (S n)))%nat; auto.
    rewrite <- dot_assoc; factorize; auto.
    generalize (odd_double _ o);intro H; auto.
    apply lt_div2; auto with arith.
  Qed.

  Lemma binary_power_ok :
    forall x n, binary_power (x:A) (n:nat) = x ** n.
  Proof.
    intros n x; unfold binary_power; rewrite binary_power_mult_ok;
    monoid_simpl; auto.
  Qed.
End About_power.

Definition fibonacci (n:nat) :=
  c00 (binary_power (Build_M2 1 1 1 0) n).
Compute fibonacci 20.                       (* 10946 : Z *)

(******************)
(* Abelian_Monoid *)
(******************)
Class Abelian_Monoid `(M:Monoid) :=
  {
    dot_comm : forall x y, (x * y = y * x)%M
  }.

Instance ZMult_Abelian : Abelian_Monoid ZMult.
Proof.
  split. 
  exact Zmult_comm.
Defined.

Section Power_of_dot.
  Context `{M: Monoid A} {AM : Abelian_Monoid M}.

 Open Scope M_scope.
 
 Theorem power_of_mult :
   forall n x y, ((x * y) ** n =  x ** n  * y ** n)%M. 
 Proof.
   induction n;simpl.
   rewrite one_left;auto.
   intros; rewrite IHn; repeat rewrite dot_assoc.
   
   About dot_comm.
   rewrite <- (dot_assoc  x y (power x n)); rewrite (dot_comm y (power x n)).
   repeat rewrite dot_assoc;trivial.
 Qed.

End Power_of_dot.

Open Scope M_scope.
About power_of_power.
About power_of_mult.

Goal forall (x y z : Z) (n : nat),
       ((x * (y * z)) ** n = x ** n *  (y ** n  * z ** n))%M.
Proof.
  intros.
  repeat (rewrite power_of_mult); trivial. 
Qed.

(****************************************)
(*** Monoids with equivalence : EMonoid *)
(****************************************)

Require Import Coq.Setoids.Setoid.
Require Import Morphisms.

(*
If we want to consider monoids w.r.t. some equivalence relation, it is possible to
associate an operational type class to the considered relation:

モノイドを同値関係として考えるとき、operational type class としてまとめることが可能である。
*)
Class Equiv A := equiv : relation A.        (* Operational Type Classes *)
Infix "==" := equiv (at level 70) : type_scope.

Open Scope M_scope.
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
Check (Equivalence equiv).                  (* Prop *)
Print equiv.
(* fun (A : Type) (Equiv : Equiv A) => Equiv
     : forall A : Type, Equiv A -> relation A *)
Print Equivalence.
(* Record Equivalence (A : Type) (R : relation A) : Prop := Build_Equivalence
  { Equivalence_Reflexive : Reflexive R;
    Equivalence_Symmetric : Symmetric R;
    Equivalence_Transitive : Transitive R } *)

(* 
The overloaded == notation will refer to the appropriate equivalence relation on the
type of the arguments.
オーバーロードされた「==」は、引数の型に応じて適切な同値関係を参照するであろう。

One can develop in this fashion a hierarchy of structures. In the
following we define the structure of semirings starting from a refinement of EMonoid.
*)

Generalizable Variables E_eq E_dot E_one.

(* --- *)

Lemma E_trans `(M : EMonoid A) : transitive A E_eq.
Proof.
  (* `(M : EMonoid A) によって、コンテキストが決まる（Generalizable Variables が埋まる）。 *)
  Check A.                                  (* Type *)
  Check E_eq.                               (* Equiv A *)
  Check E_dot.                              (* monoid_binop A *)
  Check E_one.                              (* A *)
  Check E_rel.                              (* Equivalence equiv *)
  apply E_rel.
Qed.
(*
The above proofs are equivalent to the overloaded reflexivity, symmetry and transitivity
lemmas, already avalable for every EMonoid. i.e.:

上の証明は、既にEMonoid について証明した reflexivity, symmetry and transitivity の補題の証
明を上書きするものである。すなわち：
*)
Lemma E_refl' `(M : EMonoid A) : reflexive A E_eq.
Proof.
  intro.
  change (equiv x x).
  apply reflexivity.                        (* E_rel の cersion が効く。xの同値性が判断できるようになるため。 *)
(* ただし、dot_Proper は影響しない。 *)
Qed.
Set Printing Cersions.
Print E_refl'.

Fixpoint Epower `{M : EMonoid } (a:A) (n:nat):A :=
  match n with
    | 0%nat => E_one 
    | S p => a * (Epower a p)
  end.
About Epower.


Global Instance Epower_Proper `(M: EMonoid) :
  Proper (equiv ==> Logic.eq ==> equiv) Epower.
  (* x == y -> n = p -> Epower x n == Epower y p *)
Proof.
  intros x y H n p e; subst p; induction n.
  simpl.
  reflexivity.
  simpl.
  apply dot_proper; auto.
Qed.

Instance monoid_op_params : Params (@monoid_op) 2. (* あとででてこない？ *)

Lemma Epower_x_plus `(M: EMonoid) : 
  forall x n p, (Epower x (n + p)) == (Epower x n) * (Epower x p).
Proof.
  induction n; simpl. 
  intros; rewrite E_one_left; reflexivity.
  intro p; rewrite <- E_dot_assoc. 
  now rewrite <- IHn.                       (* dot_proper の cersion が効く。 *)
Qed.

Lemma Epower_x_mult `(M: EMonoid) : 
  forall x n p, (Epower x (n * p)) == Epower (Epower x p) n.
Proof.
  induction n; simpl.
  reflexivity.
  intro p; rewrite Epower_x_plus.
  now rewrite IHn.
Qed.

(************************************** *)
(*** The monoid of function composition *)
(************************************** *)
Section Definitions.
  Variable A : Type.
  
  Definition comp (g f : A -> A): A -> A := fun x :A => g (f x).
  Definition fun_ext (f g: A -> A) := forall x , f x  = g x.
  
  Lemma fun_ext_refl : reflexive (A -> A) fun_ext.
  Proof.
    intros f x; reflexivity.
  Qed.

  Lemma fun_ext_sym : symmetric (A -> A) fun_ext.
  Proof. 
    intros f g H x; rewrite H; reflexivity.
  Qed.

  Lemma fun_ext_trans: transitive (A -> A) fun_ext.
  Proof.
    intros f g h H H0 x; rewrite H; rewrite H0; reflexivity.
  Qed.
  
  (* Global instances are not forgotten at the end of sections and keep their visibility. *)
  (* グローバルインスタンスは、セクションのendででも忘れられず、可視性が保存される。 *)
  Global Instance fun_ext_equiv : Equivalence fun_ext.
  Proof.
    split; [ apply fun_ext_refl| apply fun_ext_sym| apply fun_ext_trans].
  Qed.
End Definitions.

Instance fun_ext_op A : Equiv (A->A) := @fun_ext A.

(* Comp is proper for extensional equality of functions *)
Instance comp_proper A : Proper (equiv ==> equiv ==> equiv) (@comp A).
Proof.
  reduce; unfold comp.
  rewrite H, H0.
  reflexivity.
Qed.

Instance Rels (A:Type) : EMonoid equiv (@comp  A) (@id A).
Proof.
  split.
  apply fun_ext_equiv. apply comp_proper.
  unfold comp; intros f g h x; reflexivity.
  intros f x; reflexivity.
  intros f x; reflexivity.
Defined.

Definition fibonacci_alt (n:nat) :=
   fst (Epower (M:= Rels (Z*Z)) (fun p:Z*Z => let (a,b):= p in (b,a+b)) n (1,1)).

Compute fibonacci_alt 40.                   (* 165580141 : Z *)

Module SemiRing.
About EMonoid.
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
  commutativity x y : m x y = m y x.

Class Absorb {A} `{Equiv A} (m: A -> A -> A) (x : A) : Prop := 
  {
    absorb_l c : m x c = x;
    absorb_r c : m c x = x
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
Print Distribute.
(* 
Record Distribute (A : Type) (H : Equiv A) (f g : A -> A -> A) : Prop
  := Build_Distribute
  { distribute_l : forall a b c : A, f a (g b c) == g (f a b) (f a c);
    distribute_r : forall a b c : A, f (g a b) c == g (f a c) (f b c) }
 *)
Print Absorb.
(*
Record Absorb (A : Type) (H : Equiv A) (m : A -> A -> A) (x : A) : Prop
  := Build_Absorb
  { absorb_l : forall c : A, m x c = x;  absorb_r : forall c : A, m c x = x }
 *)
About absorb_l.
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

Print Absorb.
Section SemiRingTheory.
  
  Context `{ESemiRing A}.
  
  Definition ringtwo := 1 + 1.
  Lemma ringtwomult : forall x : A, ringtwo * x == x + x.
  Proof.
    intros.
    unfold ringtwo.
    rewrite distribute_r.                   (* ering_dist の :> が効く。 *)
    now rewrite (E_one_left x).             (* add_monoid と mul_monoid の :> が効く。 *)
  Qed.

End SemiRingTheory.
End SemiRing.


(* The following stuff has been written after Matthieu's comments *)

(* works only with coq trunk とあるが、Coq8.4で動く。 *)

Section Fun_Comp.
  Variable A : Type.

  Global Instance Comp : monoid_binop (A -> A) := @comp A.
  Global Instance Fun_Mono: Monoid Comp (@id A).
  Proof.
    split.
    unfold monoid_op,comp; reflexivity.
    unfold monoid_op,id; reflexivity.
    unfold monoid_op, id; reflexivity.
  Defined.
End Fun_Comp.

Definition fibonacci_alt' (n:nat) :=
 let F := fun  p : Z * Z => let (a, b) := p in (b, a + b)
 in fst ((binary_power (M:= Fun_Mono (Z*Z)) F n) (1,1)).

Compute fibonacci_alt' 20.

Require Import Coq.Lists.List  Relation_Operators  Operators_Properties.
Section Partial_Com.

  Inductive Act : Set :=
  | a
  | b
  | c.
  
  Inductive transpose : list Act -> list Act -> Prop :=
  | transpose_hd : forall w, transpose(a::b::w) (b::a::w)
  | transpose_tl : forall x w u, transpose  w u -> transpose (x::w) (x::u).
 
  Definition commute := clos_refl_sym_trans _ transpose.
  
  Instance Commute_E : Equivalence commute.
  Proof.
    Search Equivalence.
    split.
    Search Reflexive.
    constructor 2.
    constructor 3; auto.
    econstructor 4; eauto.
  Qed.
  
Instance CE : Equiv (list Act) := commute.  (* == が使えるようになる。 *)

Example ex1 : (c::a::a::b::nil) == (c::b::a::a::nil).
Proof.
  constructor 4 with (c::a::b::a::nil).
  - constructor 1.                          (* 右辺の最初のaとbを入れかえた場合 *)
    constructor 2.
    constructor 2.
    now constructor 1.
  - constructor 1.                          (* 左辺の2番めのaとbを入れ替えた場合 *)
    now right; left.
Qed. 

Print clos_refl_sym_trans.           (* 1:rst_step, 2:rst_refl, 3:rst_sym, 4:rst_trans  *)
Print transpose.                     (* left:1:transpose_hd, right:2:transpose_tl *)

Example ex1' : (c::a::a::b::nil) == (c::b::a::a::nil).
Proof.
  apply rst_trans with (c::a::b::a::nil).   (* clos_refl_sym_trans のコンストラクタ。 *)
  - apply rst_step.
    apply transpose_tl.                     (* tanspose のコンストラクタ。 *)
    apply transpose_tl.
    now apply transpose_hd.
  - apply rst_step.                         (* clos_refl_sym_trans のコンストラクタ。 *)
    apply transpose_tl.                     (* tanspose のコンストラクタ。 *)
    now apply transpose_hd.
Qed.

Instance cons_transpose_Proper (x:Act) :
  Proper (transpose ==> transpose) (cons x).
(* ∀x l l', transpose l l' -> transpose (x :: l) (x :: l') *)
Proof.
 intros l l' H.
 constructor; auto.
Defined.

Instance append_transpose_Proper (l:list Act) :
  Proper (transpose ==> transpose) (app l).
(* ∀l z t, transpose z t -> transpose (l ++ z) (l ++ t) *)
Proof.
 induction l.
 intros z t Ht; simpl; auto.
 intros z t Ht; simpl; constructor; auto.
Qed.

Instance append_transpose_Proper_1 :
  Proper (transpose ==> Logic.eq  ==> transpose) (@app Act).
(* ∀x y z u, transpose x y ->  z = t -> transpose (x ++ z) (y ++ t) *)
Proof.
  intros x y H; induction H; intros z t e; subst t. 
  simpl; constructor. 
  generalize (IHtranspose z z (refl_equal z)).
  simpl; constructor; auto.
Qed.

Instance append_commute_Proper_1 : 
  Proper (Logic.eq ==> commute  ==> commute) (@app Act).
(* ∀x y z t, x = y -> commute z t -> commute (x ++ z) (y ++ t) *)
Proof.
  intros x y e; subst y; intros z t H; elim H.
  constructor 1.                            (* intros; apply rst_step. *)
  apply append_transpose_Proper; auto.
  reflexivity.
  intros.
  constructor 3; auto.                      (* apply rst_sym *)
  intros.
  constructor 4 with (x++y); auto.          (* apply (rst_trans _ _ _ (x ++ y)); auto *)
Qed.

Instance append_commute_Proper_2 :
  Proper (commute ==> Logic.eq   ==> commute) (@app Act).
(* commute x y -> x0 = y0 -> commute (x ++ x0) (y ++ y0) *)
Proof.
  intros x y H; elim H. 
  intros x0 y0 H0  z t e. subst t.
  constructor 1.                            (* apply rst_step. *)
  apply append_transpose_Proper_1; auto.
  intros x0 z t e; subst t; constructor 2; auto.
  intros x0 y0 H0 H1 z t e; subst t.
  constructor 3.
  apply H1; auto.
  intros x0 y0 z0 H1 H2 H3 H4 z t e; subst t.
  transitivity (y0 ++ z).
  apply H2; reflexivity.
  apply H4; reflexivity.
Qed.

Instance append_Proper :
  Proper (commute ==> commute ==> commute) (@app Act).
(* commute x y -> commute z t -> commute (x ++ z) (y ++ t) *)
Proof.
  intros x y H z t H0.
  transitivity (y++z).
  rewrite H.
  reflexivity.
  rewrite H0.
  reflexivity.
Qed.

(* append のモノイド *)
(* 組で定義する。 *)
Instance app_op : monoid_binop (list Act) := @app Act.
Instance PCom : EMonoid commute app_op nil.
Proof.
  split.
  apply Commute_E.
  apply append_Proper.
  unfold monoid_op; induction x; simpl; auto.
  reflexivity.
  intros.
  SearchRewrite (_ ++ _ ++ _).
  simpl; unfold app_op;  rewrite app_assoc; reflexivity.
  unfold monoid_op; simpl; reflexivity. 
  SearchAbout (_ ++ nil).
  unfold monoid_op,app_op; intro; rewrite app_nil_r; reflexivity.
Qed.
About Epower.

Example ex2:
  Epower (c::a::a::b::nil) 10 == Epower (Epower  (c::b::a::a::nil) 5)  2.
Proof.
  rewrite ex1.
  rewrite <- Epower_x_mult.
  reflexivity.
Qed.
End Partial_Com.

(* **************  *)
(* 優先順位について *)
(* **************  *)
Section Z_additive.
Local Instance Z_plus_op : monoid_binop Z | 2 := Zplus. (* monoid_binop の優先順位 2 *)

Require Import ZArithRing.

Instance ZAdd : Monoid Z_plus_op 0 | 2.   (* Monoid の優先順位 2 *)
Proof.
  split; intros; unfold Z_plus_op, monoid_op; simpl; ring.
Defined.

Compute (2 * 5)%M.                          (* 7 : Z *)
Check @monoid_op _ Zplus 2 5.
Check @monoid_op _ Zmult 2 5.

Compute 2 ** 5.                             (* 10 : Z *)

Compute power (M:=ZMult) 2 5.               (* 32 : Z*)

Set Printing Implicit.

Check (fun i:Z => (one_right i)).
Check (fun i:Z => one_right (Monoid:= ZMult) i).
(*
fun i : Z => @one_right Z Zmult 1 ZMult i
     : forall i : Z, i * 1 = i
*)
Unset Printing Implicit.

(* OK, let's remove ZAdd *)
End Z_additive.


Check monoid_binop.
Check monoid_binop Z.
Instance Zplus_op : monoid_binop Z | 7 := Zplus. (* monoid_binop の優先順位 7 *)

Eval vm_compute in (2 * 5)%M.               (* 7 : Z *)
(* The least priority level wins *)
(* 
monoid_binop に関する優先順位に応じて、Zplus_op が使われる。
Zmult_op の優先順位を6にすると、結果が 10 : Z に変わる。
 *)

Instance : Monoid Zplus_op 0 | 1.          (* Monoid の優先順位 1 *)
Proof.
  split; intros; unfold monoid_op, Zplus_op; simpl; ring. 
Defined.

(*
Now the highest priority (lowest cost) instance is selected.
最高の優先順位（最低のコスト）のインスタンスが選択される。
*)

(* END *)
