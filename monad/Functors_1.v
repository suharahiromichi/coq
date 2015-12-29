(******************************************************************************)
(* Chapter 1.4: Functors                                                      *)
(******************************************************************************)
(* @suharahiromichi *)

(*
(0)
同じディレクトリにある Categories.v を使う。

(1) ベースライン
http://www.megacz.com/berkeley/coq-categories/
これをもとに改変。Instance ... Proper を使うようにした。
 *)

Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq.
Require Import finset fintype.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Import Notations.
Require Import Morphisms.
Require Import Categories.

Class Functor `(C1 : Category) `(C2 : Category) (fobj : C1 -> C2) :=
  {
    functor_fobj := fobj;
    fmor                : forall {a b : C1}, a ~> b -> (fobj a) ~> (fobj b);
    fmor_respects       : forall {a b : C1} {f f' : a ~> b},
                            f === f' -> fmor f === fmor f';
    fmor_respects2      : forall {a b : C1},
                            Proper (@eqv (a ~> b) ==> @eqv (fobj a ~> fobj b)) fmor;
    fmor_preserves_id   : forall {a : C1}, @fmor a a id === id;
(* forall a, fmor (id a) === id (fobj a); *)
    fmor_preserves_comp : forall {a b c : C1} {f : a ~> b} {g : b ~> c},
                            (fmor g) \\o (fmor f) === fmor (g \\o f)
  }.
About functor_fobj.
About fmor.
About fmor_respects.

Check fmor.
Check @fmor.

Implicit Arguments fmor [ Obj Hom Obj0 Hom0 C1 C2 fobj a b ].
Implicit Arguments fmor_respects       [ Obj Hom Obj0 Hom0 C1 C2 fobj a b ].
Implicit Arguments fmor_preserves_id   [ Obj Hom Obj0 Hom0 C1 C2 fobj     ].
Implicit Arguments fmor_preserves_comp [ Obj Hom Obj0 Hom0 C1 C2 fobj a b c ].

Check fmor.

Notation "F \ f" := (fmor F f)   : category_scope.

Instance functor_fmor_Proper  `(C1 : Category) `(C2 : Category)
         (Fobj : C1 -> C2) (F : Functor Fobj) (a b : C1) :
  Proper (@eqv (a ~> b) ==> @eqv (Fobj a ~> Fobj b)) (@fmor _ _ _ _ _ _ _ _ a b).
Proof.
  by apply fmor_respects2.
Qed.

Coercion functor_fobj : Functor >-> Funclass.

(* the identity functor *)
Definition functor_id `(C : Category) : Functor (fun x => x).
Proof.
(*  apply (Build_Functor _ _ C _ _ C (fun x => x) (fun a b f => f)) *)
  About Build_Functor.
  Check (@Build_Functor _ _ C _ _ C).
  Check (@Build_Functor _ _ C _ _ C (fun x => x)). (* fobj を与える。 *)
  Check (@Build_Functor _ _ C _ _ C (fun x => x) (fun a b f => f)). (* fmor を与える。 *)
  Check (fun a b f => f).
  apply (@Build_Functor _ _ C _ _ C (fun x => x) (fun a b f => f)).
  - move=> a b f f' H.
    rewrite H.
    reflexivity.
  - admit.
  - reflexivity.
  - reflexivity.
Defined.

(* the constant functor *)
Definition functor_const `(C : Category) `{D : Category} (d : D) : Functor (fun _ => d).
  About Build_Functor.
  Check fun _ _ _ => @id _ d.
  Check (@Build_Functor _ _ D _ _ D (fun _ => d)). (* fobj を与える。 *)
  Check (@Build_Functor _ _ D _ _ D (fun _ => d) (fun _ _ _ => id)). (* fmor を与える。 *)
  (* apply Build_Functor with (fmor := fun _ _ _ => (id d)). *)
  apply (@Build_Functor _ _ D _ _ D (fun _ => d) (fun _ _ _ => id)).
  - reflexivity.
  - admit.
  - reflexivity.
  - move=> a b c _ _.
    by apply left_identity.
  Defined.

Generalizable Variables Fobj Gobj.

Locate "_ ○ _".
Locate "_ \\o _".
Locate "_ \ _".

(* functors compose *)
Definition functor_comp `(C1 : Category) `(C2 : Category) `(C3 : Category)
           `(F : @Functor _ _ C1 _ _ C2 Fobj) `(G : @Functor _ _ C2 _ _ C3 Gobj) :
  Functor (Gobj ○ Fobj).
Proof.
  Check fmor.
  Check @fmor.
  Check fmor G.
  Check (fun a b m => fmor G (fmor F m)).
  Check (@Build_Functor _ _ _ _ _ _ _).
  Check (@Build_Functor _ _ _ _ _ _ _
                        (fun a b m => fmor G (fmor F m))).
    
  apply (@Build_Functor _ _ _ _ _ _ _
                        (fun a b m => fmor G (fmor F m))).
  - intros a b f f' H.
    rewrite H.
    reflexivity.
  - move=> a b.
    Fail apply fmor_respects2.
    admit.
  - repeat setoid_rewrite fmor_preserves_id.
    reflexivity.
  - repeat setoid_rewrite fmor_preserves_comp.
    reflexivity.
(*
   [ abstract (intros; setoid_rewrite H ; auto; reflexivity)
   | abstract (intros; repeat setoid_rewrite fmor_preserves_id; auto; reflexivity)
   | abstract (intros; repeat setoid_rewrite fmor_preserves_comp; auto; reflexivity)
   ].
*)
  Defined.


Notation "f >>>> g" := (@functor_comp _ _ _ _ _ _ _ _ _ _ f _ g)   : category_scope.


(*
Lemma functor_comp_assoc `{C':Category}`{D:Category}`{E:Category}`{F:Category}
  {F1obj}(F1:Functor C' D F1obj)
  {F2obj}(F2:Functor D E F2obj)
  {F3obj}(F3:Functor E F F3obj)
  `(f:a~>b) :
  ((F1 >>>> F2) >>>> F3) \ f ~~ (F1 >>>> (F2 >>>> F3)) \ f.
  intros; simpl.
  reflexivity.
  Qed.
 *)

(* this is like JMEq, but for the particular case of ~~; note it does not require any axioms! *)
Inductive heq_morphisms `{C : Category} {a b : C} (f : a ~> b) :
  forall {a' b' : C}, a' ~> b' -> Prop :=
| heq_morphisms_intro :
    forall {f' : a ~> b}, eqv f f' -> @heq_morphisms _ _ C a b f a b f'.

Definition heq_morphisms_refl :
  forall `{C : Category} a b f,
    @heq_morphisms _ _ C a b f a  b  f.
Proof.
  intros.
  apply heq_morphisms_intro.
  reflexivity.
Qed.

Definition heq_morphisms_symm :
  forall `{C : Category} a b f a' b' f',
    @heq_morphisms _ _ C a b f a' b' f' -> @heq_morphisms _ _ C a' b' f' a b f.
Proof.
  refine(fun ob hom c a b f a' b' f' isd =>
           match isd with
             | heq_morphisms_intro f''' z => @heq_morphisms_intro _ _ c _ _ f''' f _
           end).
  symmetry.
  auto.
Qed.

Definition heq_morphisms_tran : forall `{C : Category} a b f a' b' f' a'' b'' f'',
  @heq_morphisms _ _ C a b f a' b' f' ->
  @heq_morphisms _ _ C a' b' f' a'' b'' f'' ->
  @heq_morphisms _ _ C a b f a'' b'' f''.
  destruct 1.
  destruct 1.
  apply heq_morphisms_intro.
  setoid_rewrite <- H0.
  apply H.
Qed.

(*
Add Parametric Relation  (Ob:Type)(Hom:Ob->Ob->Type)(C:Category Ob Hom)(a b:Ob) : (hom a b) (eqv a b)
  reflexivity proved by  heq_morphisms_refl
  symmetry proved by     heq_morphisms_symm
  transitivity proved by heq_morphisms_tran
  as parametric_relation_heq_morphisms.
  Add Parametric Morphism `(c:Category Ob Hom)(a b c:Ob) : (comp a b c)
  with signature (eqv _ _ ==> eqv _ _ ==> eqv _ _) as parametric_morphism_comp.
  auto.
  Defined.
*)

(* Notation "a ~~{ C }~~> b" := (@hom _ _ C a b). *)

Implicit Arguments heq_morphisms [ Obj Hom C a b a' b' ].
Hint Constructors heq_morphisms.

Check fmor.
Check hom.
Definition EqualFunctors `{C1 : Category} `{C2 : Category}
           {F1obj} (F1 : Functor F1obj)
           {F2obj} (F2 : Functor F2obj) :=
  forall a b (f f' : hom a b),
    f === f' -> heq_morphisms (fmor F1 f) (fmor F2 f').

(* f f' : a~~{C1}~~>b *)

Notation "f ~~~~ g" := (EqualFunctors f g) (at level 45).

Class IsomorphicCategories `(C : Category) `(D : Category) :=
  {
    ic_f_obj    : C -> D;
    ic_g_obj    : D -> C;
    ic_f        : Functor ic_f_obj;
    ic_g        : Functor ic_g_obj;
    
(*  ic_forward  : ic_f >>>> ic_g ~~~~ functor_id C; *)
    ic_forward  :
      @functor_comp _ _ _ _ _ _ _ _ _ _ ic_f _ ic_g ~~~~ functor_id C;

(*  ic_backward : ic_g >>>> ic_f ~~~~ functor_id D  *)
    ic_backward :
      @functor_comp _ _ _ _ _ _ _ _ _ _ ic_g _ ic_f ~~~~ functor_id D
  }.

(* this causes Coq to die: *)
(* Definition IsomorphicCategories := Isomorphic (CategoryOfCategories). *)
