(**
私家版：代数的構造とCoq

@suharahiromichi

2015_01_02
*)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Generalizable All Variables.

Require Import Basics Tactics Coq.Setoids.Setoid Morphisms.
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
- Recordの中（implicitな場合）は、carrier がSetoidを意味することになる。
- Recordの外（explicitな場合）は、carrier : Setoid -> Type となる。
コアーションが自動的に有効になり、「carrier s」が、「s」になる（eq2_Setoidの例）。
 *)

Check carrier : Setoid -> Type.
Check equal : forall s : Setoid, carrier s -> carrier s -> Prop.

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
  (* 自然数を要素とする二次元のベクトル *)
  Definition eq2 {A : Type} (x y : A * A) : Prop :=
    x.1 = y.1 /\ x.2 = y.2.
  
  Program Definition eq2_Setoid {A : Type} : Setoid := Setoid_of (@eq2 A).
  Next Obligation.
    by rewrite /eq2.
  Defined.
  Next Obligation.
    move: H.
    rewrite /eq2; case.
    by split.
  Defined.
  Next Obligation.
    rewrite /eq2.
    case: H.
    case: H0.
    rewrite /=.
    split; by subst.
  Defined.
  
  Check carrier eq2_Setoid : Type.
  Check eq2_Setoid : Setoid.
  Check eq2_Setoid : Type.                  (* コアーションが有効 *)
  Check eq2_Setoid = eq2_Setoid.
  Check (carrier eq2_Setoid) = (carrier eq2_Setoid).
  (* eq2_Setoid = eq2_Setoid であり、コアーションが有効 *)
  
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

Record Binop (X : Setoid) : Type :=
  {
    binop :> X -> X -> X;
    prf_Binop :> Proper ((==) ==> (==) ==> (==)) binop
  (* ∀ x y x' y', x == x' -> y == y' -> x ・ y == x' ・ y' を意味する。*)
  }.
Existing Instance prf_Binop.
Notation makeBinop op := {| binop := op |}. (* binopを与える。 *)

Section Example_2.
  (* Example_1 の続き。自然数を要素とする二次元のベクトル *)
  Definition plus2 (x y : nat * nat) : (nat * nat) := (x.1 + y.1, x.2 + y.2).
  
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
  Defined.
  Notation "x +.2 y" := (plus2_Binop x y)
                          (at level 50, left associativity).
  
(*
  Instance propler :
  Proper ((@equal _) ==> (@equal _) ==> (@equal _)) (plus2_Binop).
  Proof.
    rewrite /Proper /respectful.
    rewrite /eq2 /plus2.
    move=> x y H1 x' y' H2.
    case: H1.
    case: H2.
    rewrite /= => H1 H2 H3 H4.
    rewrite /plus2 /eq2 /=.
    split.
    by rewrite H1 H3.
    by rewrite H2 H4.
  Qed.
*)
  
  Variables x x' : @eq2_Setoid nat : Type.
  Variables y y' : @eq2_Setoid nat : Type.
  
  (* ********** *)
  (* Properの例 *)
  (* ********** *)
  Check x +.2 y : eq2_Setoid.
  Check binop plus2_Binop x y : eq2_Setoid. (* 同上 *)
  Check       plus2_Binop x y : eq2_Setoid. (* 同上 *)
  Check       plus2 x y : nat * nat.

  Goal x == x' -> y == y' -> x +.2 y == x' +.2 y'.
  Proof.
    intros Hxx' Hyy'.
(*
    rewrite Hxx'.
    rewrite Hyy'.
    reflexivity.
*)
    admit.                                  (* XXXX *)
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
  (* Example_2 の続き。自然数を要素とする二次元のベクトル *)
  Program Definition N2A : Monoid :=
    makeMonoid (@eq2_Setoid nat) (0, 0) plus2_Binop.
  Next Obligation.
      by rewrite /eq2 /plus2 /=.
  Qed.
  Next Obligation.
      by rewrite /eq2 /plus2 //=.
  Qed.

  Definition N2zero : N2A := (0, 0).
  Definition N2one  : N2A := (1, 1).
  Definition N2two  : N2A := (2, 2).
  
  Compute plus2_Binop N2one N2two.          (* (3, 3) *)
(* Compute (N2one +.2 N2two). XXXX *)
End Example_3.

(**
# Power
*)
Program Fixpoint power {dot : Binop N2A} {one : N2A}
        (a : N2A) (n : nat) : N2A :=
  match n with
    | 0%nat => one
    | S p => dot a (@power dot one a p)
  end.

(** plus2 N2two を10回繰り返す。 *)
Check @power plus2_Binop N2zero N2two 10.
Compute @power plus2_Binop N2zero N2two 10.   (* (20, 20) *)

(* *************** *)
(* ad-hoc 多相の例 *)
(* *************** *)
Class Monoid' {A : Setoid} (dot : Binop A) (one : A) : Type:=
  {
    prf_Monoid_idl' : forall x, dot one x == x;
    prf_Monoid_idr' : forall x, dot x one == x
  }.

Definition eq2_Monoid : Monoid' plus2_Binop N2zero : Type.
Proof.
  split.
  - move=> x.
    rewrite /plus2_Binop /= /eq2 /plus2 /=.
    split; by rewrite add0n.
  - move=> x.
    rewrite /plus2_Binop /= /eq2 /plus2 /=.
    split; by rewrite addn0.
Qed.

Fixpoint power' `{Monoid' A dot one} (a : A) (n : nat) : A :=
  match n with
    | 0%nat => one
    | S p => dot a (power' a p)
  end.

(** plus2 N2two を10回繰り返す。 *)
Check power' : _ -> nat -> _.
Check power' N2two 2 : N2A.                 (* 型は決まる。 *)
(* Compute power' N2two 2 : N2A. *)         (* 値は求められない。 *)

Check @power' :
  forall (A : Setoid) (dot : Binop A) (one : A), (* ad-hoc 多相の分 *)
    Monoid' dot one -> A -> nat -> A.            (* 引数で指定された分 *)
Check @power' N2A plus2_Binop N2zero
      eq2_Monoid  N2two 10.

Compute @power' N2A plus2_Binop N2zero
        eq2_Monoid  N2two 10.               (* (20, 20) *)

(**
# Group
未了。
 *)

(**
# 参考：
    http://www.labri.fr/perso/casteran/CoqArt/TypeClassesTut/typeclassestut.pdf

    http://mathink.net/program/coq_setoid.html
    http://mathink.net/program/coq_map.html
    http://mathink.net/program/coq_group.html

    http://qnighy.github.io/coqex2014/ex6.html
    https://github.com/suharahiromichi/coq/blob/master/ex2014/ex37.v
 *)

(* END *)
