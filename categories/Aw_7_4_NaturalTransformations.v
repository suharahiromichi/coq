From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* Generalizable All Variables. *)
Require Import Aw_0_Notations.
Require Import Aw_1_3_Categories.
Require Import Aw_1_4_Functors.
Require Import Aw_1_5_Isomorphisms.

(*******************************************************************************)
(* Chapter 7.4: Natural Transformations                                        *)
(*******************************************************************************)

Generalizable Variable A B.

(* Definition 7.6 *)
(* 自然変換 *)
(* 圏CとD、関手F:C→D と G:C→D が与えられたとき、
   自然変換 ϑ : F→G は以下を満たす。 *)

Class NaturalTransformation `{C : Category} `{D : Category} {Fobj1 Fobj2 : C -> D}
      (F : @Functor C _ _ D _ _ Fobj1) (G : @Functor C _ _ D _ _ Fobj2) :=
  {
    (* Dの射 ϑc : F c → G c が存在する。Dの射ϑcは、cにおけるϑの成分という。 *)
    nt_component : forall c : C, (Fobj1 c) ~~{D}~~> (Fobj2 c);
    
    (* ϑc' \\o F f === G f \\o ϑc が成立する。可換になる。 *)
    nt_commutes  : forall `(f : A ~> B),
                     (nt_component B) \\o F \ f === G \ f \\o (nt_component A)
  }.
Notation "F ~~~> G" := (@NaturalTransformation _ _ _ _ _ _ _ _ F G) : category_scope.
Coercion nt_component : NaturalTransformation >-> Funclass.

(* the identity natural transformation *)
(* 恒等自然変換 ϑ : F→F *)
Program Instance nt_id `{C : Category} `{D : Category} {Fobj}
           (F : @Functor C _ _ D _ _ Fobj) : NaturalTransformation F F.
Obligation 1.
Proof.
  Check c.
  Check F c.
  Check @iid _ _ _ c.
  Check (fun c => @iid _ _ _ (F c)).  
  Check (@Build_NaturalTransformation _ _ _ _ _ _ _ _ F F (fun c => @iid _ _ _ (F c))).
  apply (@Build_NaturalTransformation _ _ _ _ _ _ _ _ F F (fun c => @iid _ _ _ (F c))).
  move=> A B f.
(*
  setoid_rewrite left_identity.
  setoid_rewrite right_identity.
*)
  rewrite [iid \\o _]left_identity.         (* 左辺 *)
  rewrite [_ \\o iid]right_identity.        (* 右辺 *)
  reflexivity.
Defined.
Obligation 2.
Proof.
  rewrite [iid \\o _]left_identity.
  rewrite [_ \\o iid]right_identity.
  reflexivity.
Defined.  

(* 自然変換は結合律を満たす。 *)
Program Instance nt_comp `{C : Category} `{D : Category}
        {Fobj} {F : @Functor C _ _ D _ _ Fobj}
        {Gobj} {G : @Functor C _ _ D _ _ Gobj}
        {Hobj} {H : @Functor C _ _ D _ _ Hobj}
        (nt_f_g : F ~~~> G) (nt_g_h : G ~~~> H) : F ~~~> H.
Obligation 1.
Proof.
  Check (fun c => nt_g_h c \\o nt_f_g c) : (forall c : C, Fobj c ~~{ D }~~> Hobj c).
  apply (@Build_NaturalTransformation _ _ _ _ _ _ _ _ F H (fun c => nt_g_h c \\o nt_f_g c)).
  move=> A B f.
  have comm1 := @nt_commutes _ _ C _ _ D _ _ F G nt_f_g.
  have comm2 := @nt_commutes _ _ C _ _ D _ _ G H nt_g_h.
  rewrite associativity.
  rewrite comm1.
  rewrite -associativity.
  rewrite comm2.
  rewrite associativity.
  reflexivity.
Defined.
Obligation 2.
  have comm1 := @nt_commutes _ _ C _ _ D _ _ F G nt_f_g.
  have comm2 := @nt_commutes _ _ C _ _ D _ _ G H nt_g_h.
  rewrite associativity.
  rewrite comm1.
  rewrite -associativity.
  rewrite comm2.
  rewrite associativity.
  reflexivity.
Defined.

(* END *)
