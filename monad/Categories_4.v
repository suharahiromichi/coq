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
台集合を型引数にするようにした。
*)

Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq.
Require Import finset fintype.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Import Notations.
Require Import Morphisms.
Require Import Coq.Setoids.Setoid.

Generalizable Variables Obj Hom Prod.
Generalizable Variables a b c d e.

(*
Reserved Notation "x ~> y" (at level 51, left associativity).
*)
Reserved Notation "x \\o y" (at level 51, left associativity).
Reserved Notation "x === y" (at level 71, left associativity).

Class Setoid (carrier : Type) :=
  {
    car := carrier;
    eqv : carrier -> carrier -> Prop;
    eqv_equivalence : Equivalence eqv
  }.
Coercion car : Setoid >-> Sortclass.
Notation "x === z" := (eqv x z).

Class Category `(Setoid Obj) (Hom : Obj -> Obj -> Setoid Obj) :=
  {
    obj := Obj;
    hom := Hom where "a ~> b" := (hom a b);
    id   : forall {a : Obj}, (a ~> a);
    comp : forall {a b c : Obj},
             (b ~> c) -> (a ~> b) -> (a ~> c)
                                       where "f \\o g" := (comp f g);
    comp_respects   : forall {a b c : Obj},
                        Proper (eqv ==> eqv ==> eqv) (@comp a b c);
    (* Proper (@eqv (b ~> c) ==> @eqv (a ~> b) ==> @eqv (a ~> c)) comp *)
    left_identity   : forall `(f : a ~> b), id \\o f === f;
    right_identity  : forall `(f : a ~> b), f \\o id === f;
    associativity   : forall `(f : c ~> d) `(g : b ~> c) `(h : a ~> b),
                        f \\o g \\o h === f \\o (g \\o h)
}.
Coercion obj : Category >-> Sortclass.
Notation "a ~> b"  := (hom a b).
Notation "f \\o g" := (comp f g).
(* Notation "a ~~{ C }~~> b" := (@hom _ _ C a b). *)

(* eqv が、Reflexive と Symmetric と Transitive とを満たす。 *)
Instance category_eqv_Equiv `(C : Category Obj) :
  Equivalence eqv.
Proof.
  by apply eqv_equivalence.
Qed.

(* comp は eqv について固有関数である。 *)
Instance category_comp_Proper `(C : Category Obj) :
  Proper (eqv ==> eqv ==> eqv) (@comp _ _ _ C a b c).
Proof.
  move=> a b c.
  by apply comp_respects.
Qed.


(* 可換性についての定理を証明する。 *)
Lemma juggle1 : forall `{C : Category}
                       `(f : d ~> e) `(g : c ~> d) `(h : b ~> c) `(k : a ~> b),
                  f \\o g \\o h \\o k === f \\o (g \\o h) \\o k.
Proof.
  intros.
  Check associativity f g h.
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
Class Product `{CP : Category Obj} (Prod : Obj -> Obj -> Obj) :=
  {
    proj1 : forall {a b : Obj}, (Prod a b) ~> a;
    proj2 : forall {a b : Obj}, (Prod a b) ~> b;
    
    (* 仲介射 *)
    mediating : forall {a b x : Obj},
                  (x ~> a) -> (x ~> b) -> (x ~> (Prod a b))
                                            where "f &&& g" := (mediating f g);
    
    med_commute1 : forall (a b x : Obj) (f : x ~> a) (g : x ~> b),
                     proj1 \\o (f &&& g) === f;
    med_commute2 : forall (a b x : Obj) (f : x ~> a) (g : x ~> b),
                     proj2 \\o (f &&& g) === g;
    med_unique : forall (a b x : Obj) (f : x ~> a) (g : x ~> b) (h : x ~> (Prod a b)),
                   proj1 \\o h === f ->
                   proj2 \\o h === g ->
                   h === (f &&& g)
  }.

(* **** *)
(* Sets *)
(* **** *)
Instance EquivExt : forall (A B : Set), Equivalence (@eqfun A B) := (* notu *)
  {
    Equivalence_Reflexive := @frefl A B;
    Equivalence_Symmetric := @fsym A B;
    Equivalence_Transitive := @ftrans A B
  }.

Instance EqObj : forall {A : Set}, Setoid A :=
  {
    eqv := eq
  }.

Instance EqMor : forall (A B : Set), Setoid (A -> B) :=
  {
    eqv := @eqfun B A
  }.
  
Check @EqObj : (forall (A : Set), Setoid A).
Check @EqMor : (forall (A B : Set), Setoid (A → B)).

Check @Category : forall (Obj : Type), Setoid Obj → (Obj → Obj → Setoid Obj) → Type.
(*
Check (fun (A B : Set) => @Category (A -> B) EqObj (@EqMor A B)).
*)
Check Category EqObj EqMor.


Program Instance Sets : Category EqMor.
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
Check @Product Set EqMor Sets prod.

Program Instance SetsProd : @Product Set EqMor Sets prod :=
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
  
Instance EquivGeq : forall m n, Equivalence (@eq_le m n). (* notu *)
Proof.
    by [].
Qed. 
  
Instance EqLe : forall m n, Setoid :=
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

(* END *)
