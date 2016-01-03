Generalizable All Variables.
Require Import Notations.
Require Import Categories_ch1_3.
Require Import Functors_ch1_4.
Require Import Isomorphisms_ch1_5.

(******************************************************************************)
(* Chapter 1.6.1: Product Categories                                          *)
(******************************************************************************)

Section ProductCategories.

  Context `(C1:Category Ob1 Hom1).
  Context `(C2:Category Ob2 Hom2).

  (* trying to use the standard "prod" here causes a universe inconsistency once we get to coqBinoidal;
   * moreover, using a general fully-polymorphic pair type seems to trigger some serious memory leaks
   * in Coq *)
  Inductive  prod_obj : Type := pair_obj : C1 -> C2 -> prod_obj.
    Definition fst_obj x := match x with pair_obj a _ => a end.
    Definition snd_obj x := match x with pair_obj _ b => b end.

  Inductive  prod_mor (a b:prod_obj) : Type :=
    pair_mor :
      ((fst_obj a)~~{C1}~~>(fst_obj b)) ->
      ((snd_obj a)~~{C2}~~>(snd_obj b)) ->
      prod_mor a b.
    Definition fst_mor {a b:prod_obj}(x:prod_mor a b) := match x with pair_mor a _ => a end.
    Definition snd_mor {a b:prod_obj}(x:prod_mor a b) := match x with pair_mor _ b => b end.

  Definition ProductCategory : Category prod_obj prod_mor.
    refine
    {| id   := fun (a:prod_obj)  => pair_mor a a (id (fst_obj a)) (id (snd_obj a))
     ; comp := fun a b c (f:prod_mor a b) (g:prod_mor b c) =>
                  match f with pair_mor f1 f2 => match g with pair_mor g1 g2 => pair_mor _ _ (f1>>>g1) (f2>>>g2) end end
    ; eqv  := fun a b (f:prod_mor a b) (g:prod_mor a b)    => 
                  match f with pair_mor f1 f2 => match g with pair_mor g1 g2 => (f1~~g1)/\(f2~~g2) end end
    |}.
    intros.
      abstract (apply Build_Equivalence; intros; simpl; intros;
      [ unfold Reflexive; intros; case x; intros; split; reflexivity
      | unfold Symmetric; intros; destruct y; destruct x; split; case H; intros; symmetry; auto
      | unfold Transitive; intros; destruct x; destruct z; destruct y; split; case H; case H0; intros; auto ]).
      abstract (intros; unfold Proper; simpl; unfold respectful; intros;
                destruct x0; destruct y0; destruct x; destruct y;
                case H; intros; case H0; intros; split; auto).
      abstract (intros; destruct a; destruct b; case f; intros; simpl; setoid_rewrite left_identity; split; reflexivity).
      abstract (intros; destruct a; destruct b; case f; intros; simpl; setoid_rewrite right_identity; split; symmetry; reflexivity).
      abstract (intros; destruct a; destruct b; destruct c; case f; intros; destruct d; simpl; case g; intros;
                destruct h; setoid_rewrite associativity; split; reflexivity).
      Defined.
End ProductCategories.

Implicit Arguments pair_obj [ Ob1 Hom1 Ob2 Hom2 C1 C2 ].
Implicit Arguments pair_mor [ Ob1 Hom1 Ob2 Hom2 C1 C2 ].
Notation "C ×× D" := (ProductCategory C D).

Section ProductCategoryFunctors.

  Context `{C:Category}.
  Context `{D:Category}.

  Definition func_pi1 : Functor (C ×× D) C (fun c => fst_obj _ _ c).
    refine {| fmor := fun a b (f:prod_mor _ _ a b) => fst_mor _ _ f |}; intros; simpl in *.
    destruct f; destruct f'; simpl in *; destruct H; auto.
    reflexivity.
    destruct f; destruct g; simpl in *; auto.
    Defined.

  Definition func_pi2 : Functor (C ×× D) D (fun c => snd_obj _ _ c).
    refine {| fmor := fun a b (f:prod_mor _ _ a b) => snd_mor _ _ f |}; intros; simpl in *.
    destruct f; destruct f'; simpl in *; destruct H; auto.
    reflexivity.
    destruct f; destruct g; simpl in *; auto.
    Defined.

  Definition llecnac_fmor (I:C) : forall (a b:D)(f:a~~{D}~~>b), (pair_obj I a)~~{C××D}~~>(pair_obj I b).
    intros; apply pair_mor; [ exact (id I) | auto ].
    Defined.
  Definition func_llecnac (I:C) : Functor D (C ×× D) (pair_obj I).
    refine {| fmor := fun a b f => llecnac_fmor I a b f |}.
    abstract (intros; simpl; repeat split; simpl; auto).
    abstract (intros; simpl; repeat split; simpl; auto).
    abstract (intros; simpl; repeat split; simpl; auto).
    Defined.

  Definition rlecnac_fmor (I:D) : forall (a b:C)(f:a~~{C}~~>b), (pair_obj a I)~~{C××D}~~>(pair_obj b I).
    intros; apply pair_mor; [ auto | exact (id I) ].
    Defined.
  Definition func_rlecnac (I:D) : Functor C (C ×× D) (fun c => (pair_obj c I)).
    refine {| fmor := fun a b f => rlecnac_fmor I a b f |}.
    abstract (intros; simpl; repeat split; simpl; auto).
    abstract (intros; simpl; repeat split; simpl; auto).
    abstract (intros; simpl; repeat split; simpl; auto).
    Defined.

  Context `{E:Category}.
  Definition cossa : ((C ×× D) ×× E) -> (C ×× (D ×× E)).
    intros.
    case X as [a1 a2]; intros.
    case a1 as [a11 a12]; intros.
    exact (pair_obj a11 (pair_obj a12 a2)).
    Defined.
  Definition cossa_fmor (a:((C ×× D) ×× E)) (b:((C ×× D) ×× E)) (f:a~~{(C ×× D) ×× E}~~>b) : (cossa a)~~{C ×× (D ×× E)}~~>(cossa b).
    case a  as [ [a11 a12] a2];
    case b  as [ [b11 b12] b2];
    case f  as [ [f11 f12] f2];
    apply pair_mor; auto;
    apply pair_mor; auto.
    Defined.
  Definition func_cossa : Functor ((C ×× D) ×× E) (C ×× (D ×× E)) cossa.
    refine {| fmor := fun a b f => cossa_fmor a b f |}.
    abstract (intros;
              case a  as [ [a11 a12] a2];
              case b  as [ [b11 b12] b2];
              case f  as [ [f11 f12] f2];
              case f' as [ [g11 g12] g2];
              case H; intro H'; case H';
              split; [ idtac | split ]; auto).
    abstract (intros; case a as [ [a11 a12] a2]; split; [ idtac | split ]; reflexivity).
    abstract (intros;
              case a as [ [a11 a12] a2];
              case b as [ [b11 b12] b2];
              case c as [ [c11 c12] c2];
              case f as [ [f11 f12] f2];
              case g as [ [g11 g12] g2];
              intros; reflexivity).
    Defined.
  Definition func_diagonal : Functor C (C ×× C) (fun c => (pair_obj c c)).
    refine {| fmor := fun a b f => @pair_mor _ _ C _ _ C (pair_obj a a) (pair_obj b b) f f |}.
    abstract (intros; simpl; repeat split; simpl; auto).
    abstract (intros; simpl; repeat split; simpl; auto).
    abstract (intros; simpl; repeat split; simpl; auto).
    Defined.
End ProductCategoryFunctors.

Section func_prod.
  Context `{C1:Category}`{C2:Category}`{C3:Category}`{C4:Category}{Fobj1}{Fobj2}(F1:Functor C1 C2 Fobj1)(F2:Functor C3 C4 Fobj2).

  Definition functor_product_fobj a := pair_obj (Fobj1 (fst_obj _ _ a)) (Fobj2 (snd_obj _ _ a)).

  Definition functor_product_fmor (a b:(C1 ×× C3))(f:a~~{C1 ×× C3}~~>b)
     : (functor_product_fobj a)~~{C2 ×× C4}~~>(functor_product_fobj b).
  destruct a; intros.
  destruct b; intros.
  apply pair_mor; simpl;
  [ apply (fmor F1) | apply (fmor F2) ];
  case f; intros;
  auto.
  Defined.

  Hint Unfold fst_obj.
  Definition func_prod : Functor (C1 ×× C3) (C2 ×× C4) functor_product_fobj.
    refine {| fmor := fun a b (f:a~~{C1 ×× C3}~~>b) => functor_product_fmor a b f |}.
    abstract (intros; destruct a; try destruct b; destruct f; destruct f'; split; destruct H;
              [ apply (@fmor_respects _ _ _ _ _ _ _ F1 _ _ h  h1)
              | apply (@fmor_respects _ _ _ _ _ _ _ F2 _ _ h0 h2)
              ]; auto).
    abstract (intros; case a; intros; simpl; split; apply fmor_preserves_id).
    abstract (intros; destruct a; destruct b; destruct c; case f; intros; case g; intros; split; simpl; apply fmor_preserves_comp).
    Defined.

End func_prod.
Notation "f **** g" := (func_prod f g).

Instance iso_prod `{C:Category}`{D:Category}{a b:C}{c d:D}(ic:a≅b)(id:@Isomorphic _ _ D c d)
  : @Isomorphic _ _ (C ×× D) (pair_obj a c) (pair_obj b d) :=
  { iso_forward  := pair_mor (pair_obj a c) (pair_obj b d) (iso_forward ic)  (iso_forward id)
  ; iso_backward := pair_mor (pair_obj b d) (pair_obj a c) (iso_backward ic) (iso_backward id)
  }.
  abstract (simpl; split; apply iso_comp1).
  abstract (simpl; split; apply iso_comp2).
  Defined.



