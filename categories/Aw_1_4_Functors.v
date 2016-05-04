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

From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Import Morphisms.
Require Import Aw_0_Notations.
Require Import Aw_1_3_Categories.

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

Notation "F \ f" := (fmor F f) : category_scope.
Open Scope category_scope.

(* parametric_morphism_fmor *)
(* これの証明に、Classの公理に Proper (eqv ==> eqv) fmor が必要なわけではない。 *)
(* また、(@fmor _ _ .... a b) は fmor と略せない。  *)
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
Program Instance functor_id `(C : Category) : Functor (fun (x : C) => x) :=
  {|
    fmor := fun (a b : C) (f : a ~> b) => f
  |}.
Obligation 2.                               (* id === id *)
Proof.
  Check (fun (x : C) => C).                 (* カテゴリC(の対象)から、カテゴリC(の対象)の写像 *)
  Check (fun (a b : C) (f : a ~> b) => f).  (* カテゴリC(の射)から、カテゴリC(の射)の写像 *)
  reflexivity.                              (* fmor_preserves_id *)
Defined.
Obligation 3.                               (* g \\o f === g \\o f *)
Proof.
  reflexivity.                              (* fmor_preserves_comp *)
Defined.

(* 定数関手 *)
(* the constant functor *)
Program Instance functor_const `(C : Category) `{D : Category} (d : D) :
  Functor (fun (x : C) => d) :=
  {|
    fmor := fun (a b : C) (f : a ~> b) => id
  |}.
Obligation 1.
Proof.
  Check (fun (x : C) => d). (* カテゴリC(の対象)から、カテゴリD(の対象)の写像 *)
  Check (fun (a b : C) (f : a ~> b) => id). (* カテゴリC(の射)から、カテゴリD(の射)の写像 *)
  reflexivity.
Defined.
Obligation 2.
Proof.
  reflexivity.
Defined.
Obligation 3.
Proof.
  by apply left_identity.
Defined.

Generalizable Variables Fobj Gobj.

Locate "_ ○ _".                            (* "f ○ g" := fun x => f (g x) *)
Locate "_ \o _".                            (* SSReflect では、こっちを使う。 *)
Locate "_ \\o _".                           (* "f \\o g" := comp f g *)

(* 関手の合成 *)
(* functors compose *)
Program Instance functor_comp `(C1 : Category) `(C2 : Category) `(C3 : Category)
        `(F : @Functor _ _ C1 _ _ C2 Fobj) `(G : @Functor _ _ C2 _ _ C3 Gobj) :
  Functor (Gobj \o Fobj) :=
  {|
    fmor := fun a b m => G \ (F \ m)
  |}.
Obligation 1.
Proof.
  Check F : C1 -> C2.              (* C1の対象からC2の対象への写像  *)
  Check Fobj : C1 -> C2.           (* C1の対象からC2の対象への写像  *)
  Check fmor F.                    (* C1の射からC2の射への写像 *)
  Check G : C2 -> C3.              (* C2の対象からC3の対象への写像  *)
  Check Gobj : C2 -> C3.           (* C2の対象からC3の対象への写像  *)
  Check fmor G.                    (* C2の射からC3の射への写像 *)
  rewrite H.
  reflexivity.
Defined.
Obligation 2.
Proof.
  repeat setoid_rewrite fmor_preserves_id.
  reflexivity.
Defined.
Obligation 3.
Proof.
  repeat setoid_rewrite fmor_preserves_comp.
  reflexivity.
Defined.

Notation "f >>>> g" := (@functor_comp _ _ _ _ _ _ _ _ _ _ f _ g)   : category_scope.
Open Scope category_scope.

Generalizable Variables Xobj Yobj Zobj a b.

(*
Lemma functor_comp_assoc `{C : Category} `{D : Category} `{E : Category} `{F : Category}
      `(F1 : @Functor _ _ C _ _ D Xobj)
      `(F2 : @Functor _ _ D _ _ E Yobj)
      `(F3 : @Functor _ _ E _ _ F Zobj) :
  forall (a b : C) (f : a ~> b),
    ((F1 >>>> F2) >>>> F3) \ f === (F1 >>>> (F2 >>>> F3)) \ f.
      
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
| heq_morphisms_intro {f' : a ~> b} :
    eqv f f' -> @heq_morphisms _ _ C a b f a b f'.

Definition heq_morphisms_refl `{C : Category} a b f :
  @heq_morphisms _ _ C a b f a  b  f.
Proof.
  apply heq_morphisms_intro.
  reflexivity.
Qed.
Check heq_morphisms_refl.
Check @heq_morphisms_refl :
  forall {Obj Hom C} {a b : Obj} {f : a ~> b},
    heq_morphisms f f.

Definition heq_morphisms_symm `{C : Category} a b f a' b' f' :
  @heq_morphisms _ _ C a b f a' b' f' -> @heq_morphisms _ _ C a' b' f' a b f.
Proof.
  case=> f'' H.
  apply: heq_morphisms_intro.
  rewrite H.
  reflexivity.
Qed.
Check heq_morphisms_symm.
Check @heq_morphisms_symm :
  forall {Obj Hom C}
         {a b : Obj} {f : a ~> b}
         {a' b' : Obj} {f' : a' ~> b'},
    heq_morphisms f f' -> heq_morphisms f' f.

Definition heq_morphisms_tran `{C : Category} a b f a' b' f' a'' b'' f'' :
  @heq_morphisms _ _ C a b f a' b' f' ->
  @heq_morphisms _ _ C a' b' f' a'' b'' f'' ->
  @heq_morphisms _ _ C a b f a'' b'' f''.
Proof.
  case=> f''' H.
  case=> f'''' H'.
  apply: heq_morphisms_intro.
  rewrite -H'.
  by apply: H.
Qed.
Check heq_morphisms_tran.
Check @heq_morphisms_tran :
  forall {Obj Hom C}
         {a b : Obj} {f : a ~> b}
         {a' b' : Obj} {f' : a' ~> b'}
         {a'' b'' : Obj} {f'' : a'' ~> b''},
    heq_morphisms f f' -> heq_morphisms f' f'' -> heq_morphisms f f''.

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
    
    ic_forward  : ic_f >>>> ic_g ~~~~ functor_id C;
    ic_backward : ic_g >>>> ic_f ~~~~ functor_id D
  }.

(* this causes Coq to die: *)
(* Definition IsomorphicCategories := Isomorphic (CategoryOfCategories). *)
