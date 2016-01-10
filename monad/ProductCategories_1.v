(******************************************************************************)
(* Chapter 1.6.1: Product Categories                                          *)
(******************************************************************************)

(*
(0)
同じディレクトリにある Categories.v と Functor.v を使う。

(1) ベースライン
http://www.megacz.com/berkeley/coq-categories/
これをもとに改変。Instance ... Proper を使うようにした。
 *)

Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq.
Require Import finset fintype.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Import Notations.                   (* coq standard libs. *)
Require Import Categories.                  (* same dir. *)
Require Import Functors.                    (* same dir. *)
Require Import Isomorphisms.                (* same dir. *)

(* 積圏 *)
Section ProductCategories.

  Locate "_ ~~{ _ }~~> _".                  (* Categories.v *)
  
(*
  Context `(C1 : Category Obj1 Hom1).
  Context `(C2 : Category Obj2 Hom2).
*)  
  Context `(C1 : Category).                 (* Obj Hom *)
  Context `(C2 : Category).                 (* Obj0 Hom0 *)
  
  (* trying to use the standard "prod" here causes a universe
  inconsistency once we get to coqBinoidal; moreover, using a
  general fully-polymorphic pair type seems to trigger some serious
  memory leaks in Coq *)
  
  Inductive  prod_obj : Type :=
  | pair_obj : C1 -> C2 -> prod_obj.
  
  Definition fst_obj (x : prod_obj) : C1 :=
    match x with
      | pair_obj a _ => a
    end.
  
  Definition snd_obj (x : prod_obj) : C2 :=
    match x with
      | pair_obj _ b => b
    end.

  Inductive prod_mor (a b : prod_obj) : Type :=
    pair_mor :
      ((fst_obj a) ~~{C1}~~> (fst_obj b)) -> (* f1 *)
      ((snd_obj a) ~~{C2}~~> (snd_obj b)) -> (* f2 *)
      prod_mor a b.                          (* f *)
  Check prod_mor : prod_obj → prod_obj → Type.
  
  Definition prod_eqv (a b : prod_obj)
             (f : prod_mor a b) (g : prod_mor a b) : Prop :=
    match f with
      | pair_mor f1 f2 =>
        match g with
          | pair_mor g1 g2 =>
            f1 === g1 /\ f2 === g2
        end
    end.
  
  Program Instance prod_Equiv (a b : prod_obj) : Equivalence (@prod_eqv a b).
  Obligation 1.                             (* Reflexive *)
  Proof.
    rewrite /prod_eqv /Reflexive /=.
    case=> f1 f2.
    split.
    - reflexivity.
    - reflexivity.
  Qed.
  Obligation 2.                             (* Symmetric *)
  Proof.
    rewrite /prod_eqv /Symmetric /=.
    case=> f1 f2.
    case=> g1 g2.
    case=> H1 H2.
    split.
    - rewrite H1.
      reflexivity.
    - rewrite H2.
      reflexivity.
  Qed.
  Obligation 3.                             (* Transitive *)
  Proof.
    rewrite /prod_eqv /Transitive /=.
    case=> f1 f2.
    case=> g1 g2.
    case=> h1 h2.
    case=> Hfg1 Hfg2.
    case=> Hgh1 Hgh2.
    split.
    - rewrite Hfg1 Hgh1.
      reflexivity.
    - rewrite Hfg2 Hgh2.
      reflexivity.
  Qed.
  
  (* 射はSetoidでないといけない。 *)
  Instance PC_mor (a b : prod_obj) : Setoid :=
    {
      carrier := prod_mor a b;
      eqv := @prod_eqv a b
    }.
  Check PC_mor : prod_obj → prod_obj → Setoid.
  Print PC_mor.
  
  Definition fst_mor {a b : prod_obj} (f : prod_mor a b) :=
    match f with
      | pair_mor a _ => a
    end.
  
  Definition snd_mor {a b : prod_obj} (f : prod_mor a b) :=
    match f with
      | pair_mor _ b => b
    end.
  
  Check @Category.
  Check prod_obj : Type.
  Check prod_mor : prod_obj → prod_obj → Type.
  Check PC_mor   : prod_obj → prod_obj → Setoid.
  Check @Category prod_obj PC_mor.
  
  Program Instance ProductCategory : @Category prod_obj PC_mor.
  Obligation 1.                             (* id *)
  Proof.
    apply pair_mor.
    - apply id.
    - apply id.
  Defined.
  Obligation 2.                             (* comp *)
  Proof.
    apply pair_mor.
    Check (fun (f1 : fst_obj a ~~{ C1 }~~> fst_obj b)
               (g1 : fst_obj b ~~{ C1 }~~> fst_obj c) => (g1 \\o f1)).
    - apply (fun (f1 : fst_obj a ~~{ C1 }~~> fst_obj b)
                 (g1 : fst_obj b ~~{ C1 }~~> fst_obj c) => (g1 \\o f1));
        by [apply X | apply X0].
    - apply (fun (f2 : snd_obj a ~~{ C2 }~~> snd_obj b)
                 (g2 : snd_obj b ~~{ C2 }~~> snd_obj c) => (g2 \\o f2));
        by [apply X | apply X0].
  Defined.
  Obligation 3.                             (* comp_respects *)
  Proof.
    rewrite /ProductCategory_obligation_2.
    move=> g1 g2 Hg.
    move=> f1 f2 Hf.
    move: Hg Hf.
    rewrite /prod_eqv.
    case g1 => gf1 gs1.
    case f1 => ff1 fs1.
    case g2 => gf2 gs2.
    case f2 => ff2 fs2.
    case=> Hgf Hgs.
    case=> Hff Hfs.
    split.
    - rewrite Hgf Hff.
      reflexivity.
    - rewrite Hgs Hfs.
      reflexivity.
  Defined.
  Obligation 4.                             (* id \\o f === f  *)
  Proof.
    case: f => ff fs.
    split.
    - rewrite left_identity.
      reflexivity.
    - rewrite left_identity.
      reflexivity.
  Defined.
  Obligation 5.                             (* f \\o id === f  *)
  Proof.
    case: f => ff fs.
    split.
    - rewrite right_identity.
      reflexivity.
    - rewrite right_identity.
      reflexivity.
  Defined.
  Obligation 6.                             (* f \\o g \\o h === f \\o (g \\o h) *)
  Proof.
    case: f => ff fs.
    split.
    - case: g => gf gs.
      case: h => hf hs.
      rewrite associativity.
      reflexivity.
    - case: g => gf gs.
      case: h => hf hs.
      rewrite associativity.
      reflexivity.
  Defined.
End ProductCategories.

Notation "C ×× D" := (ProductCategory C D).

(*
Implicit Arguments pair_obj [ Ob1 Hom1 Ob2 Hom2 C1 C2 ].
Implicit Arguments pair_mor [ Ob1 Hom1 Ob2 Hom2 C1 C2 ].
 *)

Check @pair_obj : ∀Obj Hom C1 Obj Hom C2 a b, prod_obj C1 C2.
Check @pair_mor : ∀Obj Hom C1 Obj Hom C2 a b f g, prod_mor a b.
Check @fst_obj.
Check @fst_mor.
Arguments pair_obj {Obj1 Hom1} C1 {Obj2 Hom2} C2 a b : rename.
Arguments pair_mor {Obj1 Hom1} C1 {Obj2 Hom2} C2 {a b} f g : rename.
Arguments fst_obj  {Obj1 Hom1} C1 {Obj2 Hom2} C2 D : rename.
Arguments snd_obj  {Obj1 Hom1} C1 {Obj2 Hom2} C2 D : rename.
Arguments fst_mor  {Obj1 Hom1} C1 {Obj2 Hom2} C2 a b i : rename.
Arguments snd_mor  {Obj1 Hom1} C1 {Obj2 Hom2} C2 a b i : rename.
Check pair_obj _ _ : _ -> _ -> prod_obj _ _.
Check pair_mor _ _ : _ ~> _ ->  _ ~> _ -> prod_mor _ _.
Check fst_obj _ _ : prod_obj _ _ -> _.
Check snd_obj _ _  : prod_obj _ _ -> _.
Check fst_mor _ _ _ _ : prod_mor _ _ -> _ ~> _.

Check @PC_mor : ∀Obj Hom C1 Obj0 Hom0 C2 _ _, Setoid.
Arguments PC_mor {Obj1 Hom1} C1 {Obj2 Hom2} C2 f g : rename.
Check PC_mor _ _ : prod_obj _ _ → prod_obj _ _ → Setoid.

Section ProductCategoryFunctors.

  Context `{C : Category}.                  (* Obj Hom C *)
  Context `{D:Category}.                    (* Obj0 Hom0 D *)

  Check @Functor.
  Check @Functor _ _ (C ×× D) Obj Hom C (fun c => fst_obj _ _ c).

  Check @prod_obj Obj Hom C Obj0 Hom0 D.
  Check prod_obj C D.

  Check @PC_mor Obj Hom C Obj0 Hom0 D.
  Check PC_mor C D.
  
  Check @fst_obj Obj Hom C Obj0 Hom0 D : prod_obj C D → C.
  Check fst_obj C D : prod_obj C D → C.
  
  Check fun (c : prod_obj C D) => @fst_obj Obj Hom C Obj0 Hom0 D c.
  Check fun (c : prod_obj C D) => fst_obj C D c.
  
  Check @Functor (prod_obj C D) (@PC_mor Obj Hom C Obj0 Hom0 D) (C ×× D)
        Obj Hom C (fun c => fst_obj _ _ c).
  Check Functor (fun (c : prod_obj C D) => @fst_obj Obj Hom C Obj0 Hom0 D c).
  Check Functor (fun (c : prod_obj C D) => fst_obj C D c).
  
  (* 積圏からもとの圏をとりだす関手 *)
  Program Instance func_pi1 :
    @Functor _ _ (C ×× D) _ _ C
             (fun (c : prod_obj C D) => fst_obj C D c).
  Obligation 1.
  (* fst_obj C D a ~~{ C }~~> fst_obj C D b *)
  Proof.
    by apply fst_mor.
  Defined.
  Obligation 2.
  (* fst_mor C D a b f === fst_mor C D a b f' *)
  Proof.
    rewrite /func_pi1_obligation_1.
    case: f H => ff fs.
    case: f' => f'f f's H /=.
    by case: H.
  Defined.
  Obligation 3.
  (* id === id *)
  Proof.
    reflexivity.
  Defined.
  Obligation 4.
  Proof.
    rewrite /func_pi1_obligation_1.
    case: f => ff fs.
    case: g => gf gs.
    reflexivity.
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



