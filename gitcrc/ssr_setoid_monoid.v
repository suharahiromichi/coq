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

Section Example_1.                          (* 補足説明 *)
  Check Setoid_of eq : Setoid.
  Check Setoid_of (@eq nat) : Setoid.
  
  Program Definition eq_Setoid (A: Type) : Setoid := Setoid_of (@eq A).
  (* 証明は要求されないで、定義が完了した。 *)

  Definition U : Setoid := eq_Setoid nat.
  (* Variables x y : @carrier U : Type. *)
  Variables x y : U : Type.
  (* Check @equal U x y : Prop. *)
  Check equal x y : Prop.
  Check x == y :> U : Prop.
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

Record Binop (X : Setoid) : Type :=
  {
    binop :> @carrier X -> @carrier X -> @carrier X;
    prf_Binop :> Proper ((==) ==> (==) ==> (==)) binop
  (* ∀ x y x' y', x == x' -> y == y' -> x ・ y == x' ・ y' を意味する。*)
  }.
Existing Instance prf_Binop.
Notation makeBinop op := {| binop := op |}. (* binopを与える。 *)

Section Example_2.
  (* Example_1 の続き。 *)
  Variables x x' : U.
  Variables y y' : U.

  Check Binop U.
  Program Definition test : Binop U := {| binop := addn |}.
  
  Goal x == x' -> y == y' -> test x y == test x' y'.
  Proof.
    intros Hxx' Hyy'.
    rewrite Hxx'.
    rewrite Hyy'.
    reflexivity.
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

Check Monoid.
Program Definition Mult : Monoid :=
  makeMonoid U 0%nat test.

(**
# 参考：
    http://www.labri.fr/perso/casteran/CoqArt/TypeClassesTut/typeclassestut.pdf
    http://mathink.net/program/coq_setoid.html
    http://mathink.net/program/coq_map.html
    http://mathink.net/program/coq_group.html
 *)

(* END *)
