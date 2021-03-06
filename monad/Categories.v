(* Steve Awodey's book on category theory *)
(******************************************************************************)
(* Chapter 1.3: Categories                                                    *)
(******************************************************************************)
(* @suharahiromichi *)

(*
(1) ベースライン
http://www.megacz.com/berkeley/coq-categories/
これをもとに改変。Instance ... Proper を使うようにした。
 *)

(*
(2) Proper関数の定義
A Gentle Introduction to Type Classes and Relations in Coq
*)

(*
(3) Setoid を使うようにし、Setsと(P,<=)のインスタンスをつくる。
http://www.iij-ii.co.jp/lab/techdoc/category/category1.html
 *)

(* 
できるだけ Generalizable を使う。
 *)

From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq.
From mathcomp Require Import finset fintype.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Import Morphisms.
Require Import Coq.Setoids.Setoid.
Require Import Notations.

(*
Reserved Notation "x ~> y" (at level 51, left associativity).
*)
Reserved Notation "x \\o y" (at level 51, left associativity).
Reserved Notation "x === y" (at level 71, left associativity).

Generalizable Variables a b c d e x.
Generalizable Variables Obj.

(* Calss Setoid (carrier : Type) とするのは難しい。なぜ？ *)
Class Setoid : Type :=
  {
    carrier : Type;
    eqv : carrier -> carrier -> Prop;
    eqv_equivalence : Equivalence eqv
  }.
Coercion carrier : Setoid >-> Sortclass.
Notation "x === y" := (eqv x y).

Class Category `(Hom : Obj -> Obj -> Setoid) : Type :=
  {
    hom := Hom where "a ~> b" := (hom a b);
    obj := Obj;
    id   : forall {a : Obj}, (a ~> a);
    comp : forall {a b c : Obj},
             (b ~> c) -> (a ~> b) -> (a ~> c)
                                       where "f \\o g" := (comp f g);
    comp_respects   : forall {a b c : Obj},
                        Proper (eqv ==> eqv ==> eqv) (@comp a b c);
    left_identity   : forall `{f : a ~> b}, id \\o f === f;
    right_identity  : forall `{f : a ~> b}, f \\o id === f;
    associativity   : forall `{f : c ~> d} `{g : b ~> c} `{h : a ~> b},
                        f \\o g \\o h === f \\o (g \\o h)
}.
Coercion obj : Category >-> Sortclass.

Notation "a ~> b"  := (hom a b).
Notation "f \\o g" := (comp f g).
Notation "a ~~{ C }~~> b" := (@hom _ _ C a b) (at level 100).

(* eqv が、Reflexive と Symmetric と Transitive とを満たす。 *)
Instance category_eqv_Equiv `(C : Category Obj) (a b : Obj) :
  Equivalence (@eqv (a ~> b)).
Proof.
  by apply eqv_equivalence.
Qed.

(* comp は eqv について固有関数である。 *)
Instance category_comp_Proper `(C : Category Obj) (a b c : Obj) :
  Proper (@eqv (b ~> c) ==> @eqv (a ~> b) ==> @eqv (a ~> c)) comp.
Proof.
  by apply comp_respects.
Qed.


(* 可換性についての定理を証明する。 *)
Lemma juggle1 : forall `{C : Category}
                       `(f : d ~> e) `(g : c ~> d) `(h : b ~> c) `(k : a ~> b),
                  f \\o g \\o h \\o k === f \\o (g \\o h) \\o k.
Proof.
  intros.
  rewrite <- associativity.
  reflexivity.
Defined.

Lemma juggle2 : forall `{C : Category}
                       `(f : d ~> e) `(g : c ~> d) `(h : b ~> c) `(k : a ~> b),
                  f \\o (g \\o (h \\o k)) === f \\o (g \\o h) \\o k.
Proof.
  intros.
  do ! rewrite <- associativity.
  reflexivity.
Defined.

Lemma juggle3 : forall `{C : Category}
                       `(f : d ~> e) `(g : c ~> d) `(h : b ~> c) `(k : a ~> b),
                  f \\o g \\o (h \\o k) === f \\o (g \\o h) \\o k.
Proof.
  intros.
  do ! rewrite <- associativity.
  reflexivity.
Defined.

Reserved Notation "x &&& y" (at level 50, left associativity).

(* 直積 *)
Class Product `{C : Category Obj} (Prod : Obj -> Obj -> Obj) : Type :=
  {
    obj' := Obj;
    proj1 : forall {a b : Obj}, (Prod a b) ~> a;
    proj2 : forall {a b : Obj}, (Prod a b) ~> b;
    
    (* 仲介射 *)
    mediating : forall {a b x : Obj},
                  (x ~> a) -> (x ~> b) -> (x ~> (Prod a b))
                                            where "f &&& g" := (mediating f g);
    
    med_commute1 : forall `(f : x ~> a) `(g : x ~> b),
                     proj1 \\o (f &&& g) === f;
    med_commute2 : forall `(f : x ~> a) `(g : x ~> b),
                     proj2 \\o (f &&& g) === g;
    med_unique : forall `(f : x ~> a) `(g : x ~> b) `(h : x ~> (Prod a b)),
                   proj1 \\o h === f ->
                   proj2 \\o h === g ->
                   h === (f &&& g)
  }.
Coercion obj': Product >-> Sortclass.
Notation "x &&& y" := (mediating x y).

Check @proj1 : ∀Obj Hom C Prod _ a b, Prod a b ~> a.
Check @proj2 : ∀Obj Hom C Prod _ a b, Prod a b ~> b.

Set Printing All.
Generalizable Variables Prod.
Definition parallel `{C : Category Obj} {Prod : Obj -> Obj -> Obj} {CP : Product Prod}
           `(f : a ~> b) `(g : c ~> d) : (Prod a c) ~> (Prod b d) :=
  let p1 := @proj1 Obj Hom C Prod CP a c in
  let p2 := @proj2 Obj Hom C Prod CP a c in
  (f \\o p1) &&& (g \\o p2).
Notation "f *** g" := (parallel f g).      (* <f,g> *)

(* **** *)
(* Sets *)
(* **** *)
Instance EquivExt : forall (A B : Set), Equivalence (@eqfun A B) := (* notu *)
  {
    Equivalence_Reflexive := @frefl A B;
    Equivalence_Symmetric := @fsym A B;
    Equivalence_Transitive := @ftrans A B
  }.

Instance EqMor : forall (A B : Set), Setoid :=
  {
    carrier := A -> B;
    eqv := @eqfun B A
  }.
  
Check @Category Set : (Set → Set → Setoid) → Type.
Check @Category Set EqMor : Type.
Check EqMor : Set -> Set -> Setoid.

Program Instance Sets : @Category Set EqMor.
Obligation 3.
Proof.
  rewrite /Sets_obligation_2.
  move=> homab homab' Hhomab hombc hombc' Hhombc.
  move=> x //=.
  rewrite Hhomab.
  rewrite Hhombc.
    by [].
Qed.

Check prod : (Type → Type → Type).
Check @Product Sets EqMor Sets prod.
Check Product prod : Type.

Program Instance SetsProd : @Product Sets EqMor Sets prod :=
  {
    proj1 A B := @fst A B;
    proj2 A B := @snd A B;
    mediating A B X := fun f g x => (f x, g x)
  }.
Obligation 3.
Proof.
  move: H H0.
  rewrite /Sets_obligation_2 => H1 H2 x'.
  rewrite -(H1 x').
  rewrite -(H2 x').
  by apply surjective_pairing.
Qed.

(* **** *)
(* P,<= *)
(* **** *)
Open Scope coq_nat_scope.
Search "_ <= _".
Check 0 <= 0 : Prop.

Definition eq_le m n (p q : m <= n) := True.
  
Instance EquivGeq : forall (m n : nat), Equivalence (@eq_le m n). (* notu *)
Proof.
    by [].
Qed. 
  
Instance EqLe : forall (m n : nat), Setoid :=
  {
    carrier := m <= n;
    eqv := @eq_le m n
  }.

Check @Category nat : (nat → nat → Setoid) → Type.
Check EqLe : nat → nat → Setoid.
Check @Category nat EqLe.

Program Instance P_LE : @Category nat EqLe.
Obligation 2.
Proof.
    by apply (@Le.le_trans a b c).
Defined.
Obligation 3.
Proof.
  rewrite /P_LE_obligation_1.
  rewrite /P_LE_obligation_2.
  move=> homab homab' Hhomab hombc hombc' Hhombc.
  by rewrite /eq_le.
Defined.
Obligation 4.
Proof.
  rewrite /P_LE_obligation_1.
  rewrite /P_LE_obligation_2.
  by rewrite /eq_le.
Defined.
Obligation 5.
Proof.
  rewrite /P_LE_obligation_1.
  rewrite /P_LE_obligation_2.
  by rewrite /eq_le.
Defined.
Obligation 6.
Proof.
  rewrite /P_LE_obligation_2.
  by rewrite /eq_le.
Defined.

Check P_LE.

Check min : nat -> nat -> nat.
Check @Product P_LE EqLe P_LE min.

Program Instance P_LE_Prod : @Product P_LE EqLe P_LE min.
Obligation 1.
Proof.
  Search (min _ _ <= _).
  by apply PeanoNat.Nat.le_min_l.
Defined.
Obligation 2.
  by apply PeanoNat.Nat.le_min_r.
Defined.
Obligation 3.
Proof.
  Search (_ <= min _ _).
  by apply PeanoNat.Nat.min_glb.
Defined.
Obligation 4.
  rewrite /P_LE_obligation_1.
  rewrite /P_LE_obligation_2.
  rewrite /P_LE_obligation_3.
  by rewrite /eq_le.
Defined.
Obligation 5.
  rewrite /P_LE_obligation_1.
  rewrite /P_LE_obligation_2.
  rewrite /P_LE_obligation_3.
  by rewrite /eq_le.
Defined.

Check P_LE_Prod.

(* an application of parallel (***) *)
Check @parallel.
Lemma parallel_min : forall (m n p q : nat),
      m <= n -> p <= q -> min m p <= min n q.
Proof.
  move=> m n p q Hmn Hpq.
  Check @parallel nat EqLe P_LE min P_LE_Prod m n Hmn p q Hpq.
    by apply: (@parallel nat EqLe P_LE min P_LE_Prod m n Hmn p q Hpq).
    Undo 1.
  Check Hmn *** Hpq.
    by apply: (Hmn *** Hpq).
Qed.
Print parallel_min.

(* END *)
