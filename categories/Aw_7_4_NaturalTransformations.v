Generalizable All Variables.
Require Import Notations.
Require Import Categories_ch1_3.
Require Import Functors_ch1_4.
Require Import Isomorphisms_ch1_5.

(*******************************************************************************)
(* Chapter 7.4: Natural Transformations                                        *)
(*******************************************************************************)

(* Definition 7.6 *)
Structure NaturalTransformation `{C1:Category}`{C2:Category}{Fobj1 Fobj2:C1->C2}(F1:Functor C1 C2 Fobj1)(F2:Functor C1 C2 Fobj2) :=
{ nt_component : forall c:C1, (Fobj1 c) ~~{C2}~~> (Fobj2 c)
; nt_commutes  : forall `(f:A~>B), (nt_component A) >>> F2 \ f ~~ F1 \ f >>> (nt_component B)
}.
Notation "F ~~~> G" := (@NaturalTransformation _ _ _ _ _ _ _ _ F G) : category_scope.
Coercion nt_component : NaturalTransformation >-> Funclass.

(* the identity natural transformation *)
Definition nt_id `{C:Category}`{D:Category}{Fobj}(F:Functor C D Fobj) : NaturalTransformation F F.
  apply (@Build_NaturalTransformation _ _ _ _ _ _ _ _ F F (fun c => id (F c))).
  abstract (intros;
            setoid_rewrite left_identity;
            setoid_rewrite right_identity;
            reflexivity).
  Defined.
Definition nt_comp `{C:Category}`{D:Category}
  {Fobj}{F:Functor C D Fobj}
  {Gobj}{G:Functor C D Gobj}
  {Hobj}{H:Functor C D Hobj}
  (nt_f_g:F ~~~> G) (nt_g_h:G ~~~> H) : F ~~~> H.
  apply (@Build_NaturalTransformation _ _ _ _ _ _ _ _ F H (fun c => nt_f_g c >>> nt_g_h c)).
  abstract (intros;
            set (@nt_commutes _ _ C _ _ D _ _ F G nt_f_g) as comm1;
            set (@nt_commutes _ _ C _ _ D _ _ G H nt_g_h) as comm2;
            setoid_rewrite    associativity;
            setoid_rewrite    comm2;
            setoid_rewrite <- associativity;
            setoid_rewrite <- comm1;
            reflexivity).
  Defined.

