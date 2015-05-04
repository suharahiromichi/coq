(**
私家版：代数的構造とCoq
「Magma の六角形」を実装してみる。

@suharahiromichi

2015_01_02
2015_05_01
*)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
(*
Generalizable All Variables.
Require Import Basics Tactics Coq.Setoids.Setoid Morphisms.
*)
Require Import ssreflect ssrbool ssrnat eqtype seq ssrfun.

(**
# Setoid
 *)
Class setoid_equal (A : Type) := setoid_eq : A -> A -> Prop.
Infix "==" := setoid_eq.
Class Setoid (A : Type) (equal : setoid_equal A) : Prop :=
  {
    (* 同値関係（だけ） *)
    prf_Setoid_ref :                        (* 反射律 *)
      forall x : A, equal x x;
    prf_Setoid_sym :                        (* 対象律 *)
      forall x y : A, equal x y -> equal y x;
    prf_Setoid_trans :                      (* 推移律 *)
      forall x y z : A, equal x y -> equal y z -> equal x z
  }.

Generalizable Variables A equal.

Class magma_binop `{X : @Setoid A equal} := magma_op : A -> A -> A.
Infix "*" := magma_op.
Class Magma `{X : @Setoid A equal} (dot : magma_binop) : Prop :=
  {
    prf_binop : forall (x1 y1 x2 y2 : A),
                  x1 == y1 -> x2 == y2 -> x1 * x2 == y1 * y2
  }.

(* ******************** *)
(* bool 排他的論理和の群 *)
(* ******************** *)
Check setoid_equal bool.
Instance bool_equal : setoid_equal bool := eq.
Check false == true : Prop.

Check @Setoid bool bool_equal.
Program Instance bool_setoid' : @Setoid bool eq.
(* Obligation はなし *)
Program Instance bool_setoid : @Setoid bool bool_equal.
Next Obligation.
    by [].                                  (* bool_equal は reflextivity できる。 *)
Qed.
Next Obligation.
    by [].
Qed.
Next Obligation.
  by rewrite H H0.                          (* bool_equal は rewrite できる。 *)
Qed.

Check @magma_binop bool bool_equal bool_setoid.
Instance bool_dot : @magma_binop bool bool_equal bool_setoid := xorb.
Eval compute in false * false.              (* false *)
Eval compute in false * true.               (* true *)
Eval compute in true * false.               (* true *)
Eval compute in true * true.                (* false *)

Check @Magma bool bool_equal bool_setoid bool_dot.
Program Instance bool_magma : @Magma bool eq bool_setoid xorb.
Next Obligation.
  by rewrite H H0.
Qed.

Section Group_1.
  Generalizable Variables dot inv ST MG QG one L.

  Check @Magma.
  Class qg_divop `{X : @Magma A equal ST dot} := qg_op : A -> A -> A.
  Infix "/" := qg_op.
  Class Quasigroup `{X : @Magma A equal ST dot} (divl : qg_divop) (divr : qg_divop) : Prop :=
    {
      (* divlの引数を直感的な順番にした。 *)
      divisible_l : forall (a b : A), (divl b a) * a == b;
      divisible_r : forall (a b : A), a * (divr b a) == b
    }.
  
  Check @Quasigroup.
  Class lp_unitop `{X : @Quasigroup A equal ST dot MG inv inv} := lp_op : A.
  Class Loop `{X : @Quasigroup A equal ST dot MG inv inv} (lp_unit : A) : Prop :=
    {
      lp_identical_l : forall x : A, lp_unit * x == x;
      lp_identical_r : forall x : A, x == lp_unit * x
    }.
  
  Check @Loop.
  Class Group_1 `{X : @Loop A equal ST dot MG inv QG one} : Prop :=
    {
      prf_group_1 : forall (x y z : A), (x * y) * z == x * (y * z)
    }.
  
  (* ******************** *)
  (* bool 排他的論理和の群 *)
  (* ******************** *)
  Check @qg_divop bool bool_equal bool_setoid bool_dot bool_magma.
  Instance bool_div : @qg_divop bool bool_equal bool_setoid bool_dot bool_magma := xorb.
  Eval compute in false / false.              (* false *)
  Eval compute in false / true.               (* true *)
  Eval compute in true / false.               (* true *)
  Eval compute in true / true.                (* false *)

  Check @Quasigroup bool bool_equal bool_setoid bool_dot bool_magma bool_div bool_div.
  Program Instance bool_qg : @Quasigroup bool bool_equal bool_setoid bool_dot bool_magma bool_div bool_div.
  Next Obligation.                          (* 左割算 *)
  Proof.
      by case: a; case: b.
  Qed.
  Next Obligation.                          (* 右割算 *)
  Proof.
      by case: a; case: b.
  Qed.
  
  Check `(@lp_unitop bool eq ST xorb MG inv QG).
  Check @lp_unitop bool bool_equal bool_setoid bool_dot bool_magma bool_div bool_qg.
  Instance bool_unit : @lp_unitop bool bool_equal bool_setoid bool_dot bool_magma bool_div bool_qg := false.

  Program Instance bool_loop : @Loop bool bool_equal bool_setoid bool_dot bool_magma bool_div bool_qg bool_unit.
  Next Obligation.                          (* 左単位元 *)
      by case x.
  Qed.
  Next Obligation.                          (* 右単位元 *)
      by case x.
  Qed.

  Check @Group_1 bool bool_equal bool_setoid bool_dot bool_magma bool_div bool_qg bool_unit bool_loop.
  Program Instance bool_group_1 : @Group_1 bool bool_equal bool_setoid bool_dot bool_magma bool_div bool_qg bool_unit bool_loop.
  Next Obligation.                          (* 結合則 *)
  Proof.
    rewrite /magma_op /bool_dot.
    by rewrite Bool.xorb_assoc_reverse.
  Qed.
End Group_1.

Section Group_2.
  Generalizable Variables dot inv ST MG SG one M. (* MGは、Group_1 とは別なものになる。 *)

  Check @Magma.
  Class Semigroup `{X : @Magma A equal ST dot} : Prop :=
    {
      prf_semigroup : forall (x y z : A), (x * y) * z == x * (y * z)
    }.
  
  Check @Semigroup.
  Class Monoid `{X : @Semigroup A equal ST dot MG} (mon_unit : A) : Prop :=
    {
      mon_identical_l : forall x : A, mon_unit * x == x;
      mon_identical_r : forall x : A, x == mon_unit * x
  }.
  
  Check @Monoid.
  Class gp_invop `{X : @Monoid A equal ST dot MG SG one} := gp_op : A -> A.
  Notation "'~' x" := (gp_invop x).
  Class Group_2 `{X : @Monoid A equal ST dot MG SG one} (inv : gp_invop) : Prop :=
    {
      invertible_l : forall (x : A), (inv x) * x == one;
      invertible_r : forall (x : A), x * (inv x) == one
    }.
  
  (* ******************** *)
  (* bool 排他的論理和の群 *)
  (* ******************** *)
  Check @Semigroup bool bool_equal bool_setoid bool_dot bool_magma.
  Program Instance bool_sg : @Semigroup bool bool_equal bool_setoid bool_dot bool_magma.
  Next Obligation.                          (* 結合則 *)
  Proof.
    rewrite /magma_op /bool_dot.
    by rewrite Bool.xorb_assoc_reverse.
  Qed.

  Check @Monoid bool bool_equal bool_setoid bool_dot bool_magma bool_sg bool_unit.
  Program Instance bool_monoid : @Monoid bool bool_equal bool_setoid bool_dot bool_magma bool_sg bool_unit.
  Next Obligation.                          (* 左単位元 *)
      by case x.
  Qed.
  Next Obligation.                          (* 右単位元 *)
      by case x.
  Qed.

  Check @gp_invop bool bool_equal bool_setoid bool_dot bool_magma bool_sg bool_unit bool_monoid.
  Instance bool_inv : @gp_invop bool bool_equal bool_setoid bool_dot bool_magma bool_sg bool_unit bool_monoid := id.

  Check @Group_2 bool bool_equal bool_setoid bool_dot bool_magma bool_sg bool_unit bool_monoid bool_inv.
  Program Instance bool_groop_2 : @Group_2 bool bool_equal bool_setoid bool_dot bool_magma bool_sg bool_unit bool_monoid bool_inv.
  Next Obligation.                          (* 左逆元 *)
    by case x.
  Qed.
  Next Obligation.                          (* 右逆元 *)
    by case x.
  Qed.
End Group_2.

(**
# 参考：
    http://www.labri.fr/perso/casteran/CoqArt/TypeClassesTut/typeclassestut.pdf
    http://mathink.net/program/coq_setoid.html
    http://mathink.net/program/coq_map.html
    http://mathink.net/program/coq_group.html
    http://en.wikipedia.org/wiki/Magma_(algebra)
*)

(* END *)
