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
    fmor_preserves_id   : forall {a : C1}, @fmor a a id === id;
(* forall a, fmor (id a) === id (fobj a); *)
    fmor_preserves_comp : forall {a b c : C1} {f : a ~> b} {g : b ~> c},
                            (fmor g) \\o (fmor f) === fmor (g \\o f)
  }.
Coercion functor_fobj : Functor >-> Funclass.

Check functor_fobj : ∀Obj Hom C1 Obj0 Hom0 C2 fobj _ _, C2.
(* ,の前の最後の「_」は、普通の引数で、C1（の対象） *)
Check @fmor        : ∀Obj Hom C1 Obj0 Hom0 C2 fobj _ a b _, fobj a ~> fobj b.
(* ,の前の最後の「_」は、普通の引数で、a ~> b の型を持つ。 *)

(* fobj と fmor の意味：
カテゴリ1 C1 = (Obj, Hom)
カテゴリ2 C2 = (Obj0, Hom0)

fobj : C1 -> C2、カテゴリC1（の対象）からC2（の対象）への写像
ファンクタからのコアーションが効く。

fmor : (a ~> b) -> (fobj a ~> fobj b)
カテゴリC1（の射）からC2（の射）への写像、
ただし fobj が与えられないと、意味をなさないことに注意！
 *)

Check @fmor : ∀Obj Hom C1 Obj0 Hom0 C2 fobj _ a b _, fobj a ~> fobj b.
Check fmor : _ ~> _ -> _ ~> _.
About fmor.                       (* Set Implicit Arguments の所為で、
                                     fobj は implicit になっている。 *)
Arguments fmor {Obj Hom Obj0 Hom0 C1 C2} fobj {_ a b} _ : rename.
Check fmor.                          (* fobj を指定するようにする。 *)
(*
Reserved Notation "F \ f" (at level 51, left associativity).
Notation "F \ f" := (fmor F f) : category_scope.
 *)

(* parametric_morphism_fmor *)
(* これの証明に、Classの公理に Proper (eqv ==> eqv) fmor が必要なわけではない。 *)
Instance functor_fmor_Proper `(C1 : Category) `(C2 : Category)
         (Fobj : C1 -> C2) (F : Functor Fobj) (a b : C1) :
  Proper (@eqv (a ~> b) ==> @eqv (Fobj a ~> Fobj b)) (@fmor _ _ _ _ _ _ _ _ a b).
Proof.
  move=> x y.                               (* これが肝 *)
  Check (@fmor_respects _ _ C1 _ _ C2 Fobj F a b x y).
  by apply (@fmor_respects _ _ C1 _ _ C2 Fobj F a b x y).
Qed.

(* 恒等関手 *)
(* the identity functor *)
Definition functor_id `(C : Category) : Functor (fun (x : C) => x).
Proof.
  (* 恒等関手 : C -> C *)
  Check (fun (x : C) => C).                 (* カテゴリC(の対象)から、カテゴリC(の対象)の写像 *)
  Check (fun (a b : C) (f : a ~> b) => f).  (* カテゴリC(の射)から、カテゴリC(の射)の写像 *)
  
  (* ***** *)
  About Build_Functor.
  Check (@Build_Functor _ _ C _ _ C).
  Check (@Build_Functor _ _ C _ _ C (fun (x : C) => x)). (* fobj を与える。 *)
  Check (@Build_Functor _ _ C _ _ C (fun (x : C) => x)
                        (fun (a b : C) (f : a ~> b) => f)). (* fmor を与える。 *)
  apply (@Build_Functor _ _ C _ _ C (fun x => x) (fun a b f => f)).
  (* fmor_respects *)
  - move=> a b f f' H.
    rewrite H.
    reflexivity.
  (* fmor_preserves_id *)
  - reflexivity.
  (* fmor_preserves_comp *)
  - reflexivity.
Defined.

(* 定数関手 *)
(* the constant functor *)
Definition functor_const `(C : Category) `{D : Category} (d : D) :
  Functor (fun (x : C) => d).
Proof.
  (* 定数関手 : C -> D *)
  Check (fun (x : C) => d).                 (* カテゴリC(の対象)から、カテゴリD(の対象)の写像 *)
  Check (fun (a b : C) (f : a ~> b) => id).  (* カテゴリC(の射)から、カテゴリD(の射)の写像 *)
  
  About Build_Functor.
  Check (@Build_Functor _ _ C _ _ D (fun (x : C) => d)). (* fobj を与える。 *)
  Check (@Build_Functor _ _ C _ _ D (fun (x : C) => d)
                        (fun (a b : C) (f : a ~> b) => id)). (* fmor を与える。 *)
  apply (@Build_Functor _ _ C _ _ D (fun _ => d) (fun _ _ _ => id)).
  - reflexivity.
  - reflexivity.
  - move=> a b c _ _.
    by apply left_identity.
Defined.

Generalizable Variables Fobj Gobj.

Locate "_ ○ _".                            (* "f ○ g" := fun x => f (g x) *)
Locate "_ \o _".                            (* SSReflect では、こっちを使う。 *)
Locate "_ \\o _".                           (* "f \\o g" := comp f g *)

(* 関手の合成 *)
(* functors compose *)
Definition functor_comp `(C1 : Category) `(C2 : Category) `(C3 : Category)
           `(F : @Functor _ _ C1 _ _ C2 Fobj) `(G : @Functor _ _ C2 _ _ C3 Gobj) :
  Functor (Gobj \o Fobj).
Proof.
  Check F : C1 -> C2.              (* C1の対象からC2の対象への写像  *)
  Check Fobj : C1 -> C2.           (* C1の対象からC2の対象への写像  *)
  Check fmor F.                    (* C1の射からC2の射への写像 *)
  Check G : C2 -> C3.              (* C2の対象からC3の対象への写像  *)
  Check Gobj : C2 -> C3.           (* C2の対象からC3の対象への写像  *)
  Check fmor G.                    (* C2の射からC3の射への写像 *)

  Check G \o F.
  Check Gobj \o Fobj.
  
  Check (fun (a b : C1) (m : a ~> b) => fmor F m). (* m は C1の射 *) (* C2の射を返す *)
  Check (fun (a b : C1) (m : a ~> b) => fmor G (fmor F m)). (* C3の射を返す *)
  
  Check @Build_Functor _ _ C1 _ _ C3.
  Check @Build_Functor _ _ C1 _ _ C3 (G \o F). (* fobj を与える。 *)
  Check @Build_Functor _ _ C1 _ _ C3 (G \o F)
        (fun a b m => fmor G (fmor F m)).  (* fmor を与える。 *)
    
  apply (@Build_Functor _ _ C1 _ _ C3 _ (* fobj (G \o F) を指定するとうまくいかない *)
                        (fun a b m => fmor G (fmor F m))).
  - move=> a b f f' H.
    rewrite H.
    reflexivity.
  - repeat setoid_rewrite fmor_preserves_id.
    reflexivity.
  - repeat setoid_rewrite fmor_preserves_comp.
    reflexivity.
Defined.

(* みなおし、ここまで。 *)

(*
Notation "f >>>> g" := (@functor_comp _ _ _ _ _ _ _ _ _ _ f _ g)   : category_scope.
*)

(*
Generalizable Variables Xobj Yobj Zobj a b.

Arguments functor_comp : clear implicits.
Check functor_comp.
Arguments functor_comp {Obj Hom C1 Obj0 Hom0 C2 Obj1 Hom1 C3} Fobj f Gobj g : rename.
Check functor_comp.

Lemma functor_comp_assoc `{C : Category} `{D : Category} `{E : Category} `{F : Category}
      `(X : @Functor _ _ C _ _ D Xobj)
      `(Y : @Functor _ _ D _ _ E Yobj)
      `(Z : @Functor _ _ E _ _ F Zobj) :
  forall (a b : C) (f : a ~> b),
    fmor (functor_comp _ (functor_comp _ X _ Y) _ Z) f ===
         fmor (functor_comp _ X _ (functor_comp _ Y _ Z)) f.
      
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
  move=> Obj Hom C a b f.
  apply heq_morphisms_intro.
  reflexivity.
Qed.

Definition heq_morphisms_symm :
  forall `{C : Category} a b f a' b' f',
    @heq_morphisms _ _ C a b f a' b' f' -> @heq_morphisms _ _ C a' b' f' a b f.
Proof.
  refine (fun ob hom c a b f a' b' f' isd =>
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
