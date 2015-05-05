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
(* ***** 性質 ********* *)
(* ******************** *)
Generalizable Variables dot divl divr one ST.

Class Associative `{X : @Magma A equal ST dot} : Prop :=
  associative : forall (x y z : A), (x * y) * z == x * (y * z).
  
Class LIdentical `{X : @Magma A equal ST dot} (e : A) : Prop :=
  left_identical: forall x : A, e * x == x.

Class RIdentical `{X : @Magma A equal ST dot} (e : A) : Prop :=
  right_identical: forall x : A , x * e == x.

Class Identical `{X : @Magma A equal ST dot} (e : A) : Prop :=
  {
    identical_l : LIdentical e;
    identical_r : RIdentical e
  }.

(* divの引数を直感的な順番にした。 *)
Class LDivisible `{X : @Magma A equal ST dot} (div : A -> A -> A) : Prop :=
  left_divisible: forall (a b : A), (div b a) * a == b.

Class RDivisible `{X : @Magma A equal ST dot} (div : A -> A -> A) : Prop :=
  right_divisible: forall (a b : A), a * (div b a) == b.

Class Divisible `{X : @Magma A equal ST dot} (divL divR : A -> A -> A) : Prop :=
  {
    divisible_l : LDivisible divL;
    divisible_r : RDivisible divL
  }.

(* Invertible の定義を Monoid からMagmaに移動する。 *)
Class LInvertible `{X : @Magma A equal ST dot}  (e : A) (inv : A -> A) : Prop :=
  left_invertible: forall (x : A), (inv x) * x == e.
  
Class RInvertible `{X : @Magma A equal ST dot}  (e : A) (inv : A -> A) : Prop :=
  right_invertible: forall (x : A), (inv x) * x == e.

Class Invertible `{X : @Magma A equal ST dot}  (e : A) (inv : A -> A) : Prop :=
  {
    invertible_l :> LInvertible e inv;
    invertible_r :> RInvertible e inv
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
  Generalizable Variables MG QG.

  Check @Magma.
  Check `(@Magma A equal ST dot).
  Class qg_divop `{X : @Magma A equal ST dot} := qg_op : A -> A -> A.
  Infix "/" := qg_op.
  Class Quasigroup `{X : @Magma A equal ST dot} (divl divr : qg_divop) : Prop :=
    {
      divisible : Divisible divl divr
    }.
  
  Check @Quasigroup.
  Check `(@Quasigroup A equal ST dot MG divl divr).
  Class lp_unitop `{X : @Quasigroup A equal ST dot MG divl divr} := lp_op : A.
  Class Loop `{X : @Quasigroup A equal ST dot MG divl divr} (lp_unit : A) : Prop :=
    {
      lp_identical : Identical lp_unit      (* IdenticalはMagmaで定義している。 *)
    }.
  
  Check @Loop.
  Check `(@Loop A equal ST dot MG divl divr QG one).
  Class Group_1 `{X : @Loop A equal ST dot MG divl divr QG one} : Prop :=
    {
        prf_group_1 : Associative
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
  Next Obligation.
  Proof.
    apply Build_Divisible.
    - rewrite /LDivisible.                  (* 左割算 *)
      rewrite /bool_div.
        by case; case.
    - rewrite /RDivisible.                  (* 右割算 *)
      rewrite /bool_div.
        by case; case.
  Qed.
  
  Check `(@lp_unitop bool eq ST xorb MG divl divr QG).
  Check @lp_unitop bool bool_equal bool_setoid bool_dot bool_magma bool_div bool_div bool_qg.
  Instance bool_unit : @lp_unitop bool bool_equal bool_setoid bool_dot bool_magma bool_div bool_div bool_qg := false.

  Program Instance bool_loop : @Loop bool bool_equal bool_setoid bool_dot bool_magma bool_div bool_div bool_qg bool_unit.
  Next Obligation.
    apply Build_Identical.
    - rewrite /LIdentical.                  (* 左単位元 *)
        by case.
    - rewrite /RIdentical.                  (* 右単位元 *)
        by case.
  Qed.

  Check @Group_1 bool bool_equal bool_setoid bool_dot bool_magma bool_div bool_div bool_qg bool_unit bool_loop.
  Program Instance bool_group_1 : @Group_1 bool bool_equal bool_setoid bool_dot bool_magma bool_div bool_div bool_qg bool_unit bool_loop.
  Next Obligation.                          (* 結合則 *)
  Proof.
    rewrite /Associative.
      by apply Bool.xorb_assoc_reverse.    
  Qed.
End Group_1.

Section Group_2.
  Generalizable Variables MG SG. (* MGは、Group_1 とは別なものになる。 *)

  Check @Magma.
  Class Semigroup `{X : @Magma A equal ST dot} : Prop :=
    {
      prf_semigroup : forall (x y z : A), (x * y) * z == x * (y * z)
    }.
  
  Check @Semigroup.
  Class Monoid `{X : @Semigroup A equal ST dot MG} (mon_unit : A) : Prop :=
    {
      mon_identical : Identical mon_unit    (* IdenticalはMagmaで定義している。 *)
  }.
  
  Check @Monoid.
  Class gp_invop `{X : @Monoid A equal ST dot MG SG one} := gp_op : A -> A.
(*  Notation "'~' x" := (gp_invop x). *)

(*  
  Invertible の定義を Monoid からMagmaに移動する。
  Class LInvertible `{X : @Monoid A equal ST dot MG SG one} (inv : gp_invop) : Prop :=
    left_invertible: forall (x : A), (inv x) * x == one.
  
  Class RInvertible `{X : @Monoid A equal ST dot MG SG one} (inv : gp_invop) : Prop :=
    right_invertible: forall (x : A), x * (inv x) == one.
  
  Class Invertible `{X : @Monoid A equal ST dot MG SG one} (inv : gp_invop) : Prop :=
    {
      invertible_l :> LInvertible inv;
      invertible_r :> RInvertible inv
    }.
  
  Class Group_2 `{X : @Monoid A equal ST dot MG SG one} (inv : gp_invop) : Prop :=
    {
      invertible : Invertible inv
    }.
*)
  Class Group_2 `{X : @Monoid A equal ST dot MG SG one} (inv : gp_invop) : Prop :=
    {
      invertible : Invertible one inv
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

  Check Monoid bool_unit.
  Check @Monoid bool bool_equal bool_setoid bool_dot bool_magma bool_sg bool_unit.
  Program Instance bool_monoid : @Monoid bool bool_equal bool_setoid bool_dot bool_magma bool_sg bool_unit.
  Next Obligation.
    apply Build_Identical.
    - rewrite /LIdentical.                  (* 左単位元 *)
        by case.
    - rewrite /RIdentical.                  (* 右単位元 *)
        by case.
  Qed.
  Check bool_monoid : Monoid bool_unit.
  
  Check gp_invop.
  Check @gp_invop bool bool_equal bool_setoid bool_dot bool_magma bool_sg bool_unit bool_monoid.
  Instance bool_inv : @gp_invop bool bool_equal bool_setoid bool_dot bool_magma bool_sg bool_unit bool_monoid := id.

  Check @Group_2 bool bool_equal bool_setoid bool_dot bool_magma bool_sg bool_unit bool_monoid bool_inv.
  Program Instance bool_groop_2 : @Group_2 bool bool_equal bool_setoid bool_dot bool_magma bool_sg bool_unit bool_monoid bool_inv.
  Next Obligation.
    apply Build_Invertible.
    - rewrite /LInvertible.                 (* 左逆元 *)
      rewrite /bool_unit /bool_inv => x.
      by case x.
    - rewrite /RInvertible.                 (* 右逆元 *)
      rewrite /bool_unit /bool_inv => x.
      by case x.
  Qed.
  
  (* 補足説明 *)
  Check `(@Monoid bool bool_equal ST bool_dot MG SG bool_unit).
  (* 一部を、Generalizable Variable にしてもよいが、証明している対象が違ってきているかもしれない。 *)
  Program Instance bool_monoid' : `(@Monoid bool bool_equal ST bool_dot MG SG bool_unit).
  Next Obligation.                          (* 左単位元 *)
    apply Build_Identical.
    - rewrite /LIdentical.                  (* 左単位元 *)
        by case.
    - rewrite /RIdentical.                  (* 右単位元 *)
        by case.
  Qed.
  Check bool_monoid'. (* forall (ST : Setoid bool_equal) (MG : Magma bool_dot) (SG : Semigroup), Monoid bool_unit *)

(*  
  Program Instance bool_groop_2' : Group_2 bool_inv. (* @がいらない場合もある。 *)
  Next Obligation.                          (* 左逆元 *)
    by case x.
  Qed.
  Next Obligation.                          (* 右逆元 *)
    by case x.
  Qed.
*)
End Group_2.

Section Group_3.
  Generalizable Variables inv MG QG LP SG MON GP.
  
  Check @Group_1.
  Check `(@Group_1 A equal ST dot MG divl divr QG one LP).
  Class gp1_invop `{X : @Group_1 A equal ST dot MG divl divr QG one LP} := gp1_op : A -> A.
  (*  Notation "'~' x" := (gp1_invop x). *)

  Class inv_Group_1 `{@Group_1 A equal ST dot MG divl divr QG one LP} (inv : gp1_invop) : Prop :=
    {
      invertible' : Invertible one inv
    }.
  
  Check `(@Group_2 A equal ST dot MG SG one MON inv).
  Class gp2_divop `{@Group_2 A equal ST dot MG SG one MON inv} := gp2_op : A -> A -> A.
  Infix "/" := gp2_op.
  Class div_Group_2 `{@Group_2 A equal ST dot MG SG one MON inv} (divl divr : gp2_divop) : Prop :=
    {
      divisible' : Divisible divl divr
    }.
  
End Group_3.
  
(**
# 参考：
    http://www.labri.fr/perso/casteran/CoqArt/TypeClassesTut/typeclassestut.pdf
    http://mathink.net/program/coq_setoid.html
    http://mathink.net/program/coq_map.html
    http://mathink.net/program/coq_group.html
    http://en.wikipedia.org/wiki/Magma_(algebra)
*)

(* END *)
