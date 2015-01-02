(**
私家版：代数的構造とCoq

@suharahiromichi

2015_01_02
*)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Generalizable All Variables.

Require Export Basics Tactics Coq.Setoids.Setoid Morphisms.
Require Import ssreflect ssrbool ssrnat eqtype seq ssrfun.
Require Import div.

(**
# Setoid
 *)
Record Setoid : Type :=
  {
    carrier :> Type;
    equal :
      carrier -> carrier -> Prop;
    prf_Setoid_ref :
      forall x : carrier, equal x x;
    prf_Setoid_sym :
      forall x y : carrier, equal x y -> equal y x;
    prf_Setoid_trn :
      forall x y z : carrier, equal x y -> equal y z -> equal x z
  }.
(**
carrier について：

Setoid 型の値を Type 型の値としても扱えるようにする。
- implicitな場合は、carrier がSetoidを意味することになる。
- explicitな場合は、carrier : Setoid -> Type となる。
  コアーションが自動的に有効になり、「carrier s」が、「s」になる（要補足）。
 *)
(*
Check carrier : Type.
Check @carrier : Setoid -> Type.
Check equal : carrier -> carrier -> Prop.
Check @equal : forall s : Setoid, carrier -> carrier -> Prop.
Check @equal : forall s : Setoid, @carrier s -> @carrier s -> Prop.
*)
(**
表記：
  値コンストラクタ、第二引数のequalの定義だけを与えてSetoidを作る。
 *)
Notation Setoid_of eq := {| equal := eq |}.

(**
表記：
  equal の中置記法を用意する。
 *)
Notation "(== :> S )" := (equal (s:=S)).     (* (@equal S) でもよい。 *)
Notation "(==)" := (== :> _).                (* equql ではだめ。 *)
Notation "x == y :> S" := (equal (s:=S) x y) (* (@equal S x y) でもよい。 *)
                            (at level 70, y at next level, no associativity).
Notation "x == y" := (x == y :> _)          (* equql ではだめ。 *)
                       (at level 70, no associativity).

Section Example_1.
  Definition eq2 {A : Type} (x y : A * A) : Prop :=
    x.1 = y.1 /\ x.2 = y.2.
  
  Program Definition eq2_Setoid {A : Type} : Setoid := Setoid_of (@eq2 A).
  Next Obligation.
    by rewrite /eq2.
  Qed.
  Next Obligation.
    move: H.
    rewrite /eq2; case.
    by split.
  Qed.
  Next Obligation.
    rewrite /eq2.
    case: H.
    case: H0.
    rewrite /=.
    split; by subst.
  Qed.
  
  Variables x y : @eq2_Setoid nat : Type.
  Variables x' y' : @eq2_Setoid nat : Type.
  Check x == y : Prop.
End Example_1.

(**
# Setoid上の関数
http://mathink.net/program/coq_map.html
 *)

(**
## Map
*)
Record Map (X : Setoid) (Y : Setoid) : Type :=
  {
    map :> X -> Y;
    prf_Map :> Proper ((==) ==> (==)) map
  (* ∀ x y, x == y −> map x == map y を意味する。*)
  }.
Existing Instance prf_Map.
Notation makeMap f := {| map := f |}.       (* mapを与える。 *)

(**
Properについて：
型Xでequalなら型Yでもequalとすること（同値関係の保存性）を基にして、
rewriteによる書き換えができるようになる。 *)

Structure Binop (X : Setoid) : Type :=
  {
    binop :> X -> X -> X;
    prf_Binop :> Proper ((==) ==> (==) ==> (==)) binop
  (* ∀ x y x' y', x == x' -> y == y' -> x ・ y == x' ・ y' を意味する。*)
  }.
Existing Instance prf_Binop.
Notation makeBinop op := {| binop := op |}. (* binopを与える。 *)

Section Example_2.
  (* Example_1 の続き。 *)
  Definition plus2 (x y : nat * nat) : (nat * nat) :=
    (fst x + fst y, snd x + snd y).
  
  Program Definition plus2_Binop : Binop eq2_Setoid := {| binop := plus2 |}.
  Next Obligation.
    (* Proper (eq2 ==> eq2 ==> eq2) plus2 *)
    rewrite /Proper /respectful.
    rewrite /eq2 /plus2.
    move=> x y H1 x' y' H2.
    case: H1.
    case: H2.
    rewrite /= => H1 H2 H3 H4.
    split.
    by rewrite H1 H3.
    by rewrite H2 H4.
  Qed.
  
  Variables x x' : @eq2_Setoid nat : Type.
  Variables y y' : @eq2_Setoid nat : Type.

  (* ********** *)
  (* Properの例 *)
  (* ********** *)
  Check binop plus2_Binop x y : eq2_Setoid.
  Check       plus2_Binop x y : eq2_Setoid.
  Check       plus2 x y : nat * nat.
  Goal x == x' -> y == y' -> (plus2_Binop x y) == (plus2_Binop x' y').
  Proof.
    intros Hxx' Hyy'.
    admit.
(*
    rewrite Hxx'.
    rewrite Hyy'.
    reflexivity.
*)
  Qed.
End Example_2.

(**
# モノイド
*)
Record Monoid : Type :=
  {
    monoid_setoid :> Setoid;
    monoid_unit : monoid_setoid;
    monoid_binop : Binop monoid_setoid;
    prf_Monoid_idl : forall x, monoid_binop monoid_unit x == x;
    prf_Monoid_idr : forall x, monoid_binop x monoid_unit == x
  }.
Notation makeMonoid s unit op :=
  {|
    monoid_setoid := s;
    monoid_unit := unit;
    monoid_binop := op                      (* binopを与える。 *)
  |}.

Section Example_3.
  Program Definition Mult : Monoid :=
    makeMonoid (@eq2_Setoid nat) (0, 0) plus2_Binop.
  Next Obligation.
      by rewrite /eq2 /plus2 /=.
  Qed.
  Next Obligation.
      by rewrite /eq2 /plus2 //=.
  Qed.
End Example_3.


(**
# Power
*)
(* *************** *)
(* ad-hoc 多相の例 *)
(* *************** *)
Record Monoid' {A : Setoid} (dot : Binop A) (one : A) : Type :=
  {
    prf_Monoid_idl' : forall x, dot one x == x;
    prf_Monoid_idr' : forall x, dot x one == x
  }.

Fixpoint power `{@Monoid' A dot one} (a : A) (n : nat) :=
  match n with
    | 0%nat => one
    | S p => dot a (power a p)
  end.

(**
# Group
 *)

(**
# 参考：
    http://www.labri.fr/perso/casteran/CoqArt/TypeClassesTut/typeclassestut.pdf
    http://mathink.net/program/coq_setoid.html
    http://mathink.net/program/coq_map.html
    http://mathink.net/program/coq_group.html
 *)

(* END *)
