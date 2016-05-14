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

From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Import Aw_0_Notations.              (* coq standard libs. *)
Require Import Aw_1_3_Categories.           (* same dir. *)
Require Import Aw_1_4_Functors.             (* same dir. *)
Require Import Aw_1_5_Isomorphisms.         (* same dir. *)

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
      eqv := @prod_eqv a b;
      eqv_equivalence := prod_Equiv a b
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
  Obligation 1.                             (* iid *)
  Proof.
    apply pair_mor.
    - apply iid.
    - apply iid.
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
  Obligation 4.                             (* iid \\o f === f  *)
  Proof.
    case: f => ff fs.
    split.
    - rewrite left_identity.
      reflexivity.
    - rewrite left_identity.
      reflexivity.
  Defined.
  Obligation 5.                             (* f \\o iid === f  *)
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
Arguments pair_obj {Obj1 Hom1 C1 Obj2 Hom2 C2} a b : rename.
Arguments pair_mor {Obj1 Hom1 C1 Obj2 Hom2 C2 a b} f g : rename.
Arguments fst_obj  {Obj1 Hom1 C1 Obj2 Hom2 C2} D : rename.
Arguments snd_obj  {Obj1 Hom1 C1 Obj2 Hom2 C2} D : rename.
Arguments fst_mor  {Obj1 Hom1 C1 Obj2 Hom2 C2 a b} i : rename.
Arguments snd_mor  {Obj1 Hom1 C1 Obj2 Hom2 C2 a b} i : rename.
Check pair_obj : _ -> _ -> prod_obj _ _.    (* 圏の指定は要らない。 *)
Check pair_mor : _ ~> _ ->  _ ~> _ -> prod_mor _ _.
Check fst_obj  : prod_obj _ _ -> _.
Check snd_obj  : prod_obj _ _ -> _.
Check fst_mor  : prod_mor _ _ -> _ ~> _.

Check @PC_mor : ∀Obj Hom C1 Obj0 Hom0 C2 _ _, Setoid.
Arguments PC_mor {Obj1 Hom1 C1 Obj2 Hom2 C2} f g : rename.
Check PC_mor : prod_obj _ _ → prod_obj _ _ → Setoid.

Check @Functor : ∀Obj Hom C1 Obj0 Hom0 C2 _, Type.
Arguments Functor {Obj Hom} C1 {Obj0 Hom0} C2 i : rename.

Section ProductCategoryFunctors.

  Context `{C : Category}.                  (* Obj Hom C *)
  Context `{D:Category}.                    (* Obj0 Hom0 D *)

  Check @Functor.
  Check @Functor _ _ (C ×× D) Obj Hom C (fun c => fst_obj c).
  Check Functor (C ×× D) C (fun c => fst_obj c).

  Check @prod_obj Obj Hom C Obj0 Hom0 D.
  Check prod_obj C D.

  Check @PC_mor Obj Hom C Obj0 Hom0 D.
  Check PC_mor.
  
  Check @fst_obj Obj Hom C Obj0 Hom0 D : prod_obj C D → C.
  Check fst_obj : prod_obj C D → C.
  
  Check fun (c : prod_obj C D) => @fst_obj Obj Hom C Obj0 Hom0 D c.
  Check fun (c : prod_obj C D) => fst_obj c.
  
  Check @Functor (prod_obj C D) (@PC_mor Obj Hom C Obj0 Hom0 D) (C ×× D)
        Obj Hom C (fun c => fst_obj _ c).
  Check Functor (C ×× D) C (fun (c : prod_obj C D) => @fst_obj Obj Hom C Obj0 Hom0 D c).
  
  (* 積圏からもとの圏をとりだす関手 *)
  Program Instance func_pi1 : Functor (C ×× D) C
                                      (fun (c : prod_obj C D) => fst_obj c).
  Obligation 1.
  (* fst_obj a ~~{ C }~~> fst_obj b *)
  Proof.
    by apply fst_mor.
  Defined.
  Obligation 2.
  (* fst_mor f === fst_mor f' *)
  Proof.
    rewrite /func_pi1_obligation_1.
    case: f H => ff fs.
    case: f' => f'f f's H /=.
    by case: H.
  Defined.
  Obligation 3.
  (* iid === iid *)
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
  
  Program Instance func_pi2 : Functor (C ×× D) D
                                      (fun (c : prod_obj C D) => snd_obj c).
  Obligation 1.
  (* snd_obj a ~~{ D }~~> snd_obj b *)
  Proof.
    by apply snd_mor.
  Defined.
  Obligation 2.
  (* snd_mor f === snd_mor f' *)
  Proof.
    rewrite /func_pi2_obligation_1.
    case: f H => ff fs.
    case: f' => f'f f's H /=.
    by case: H.
  Defined.
  Obligation 3.
  (* iid === iid *)
  Proof.
    reflexivity.
  Defined.
  Obligation 4.
  Proof.
    rewrite /func_pi2_obligation_1.
    case: f => ff fs.
    case: g => gf gs.
    reflexivity.
  Defined.  
  
  (* 積圏の左が恒等射である場合 *)
  Definition llecnac_fmor (I : C) (a b : D) (g : a ~~{D}~~> b) :
    (pair_obj I a) ~~{C××D}~~> (pair_obj I b).
  Proof.
    apply: pair_mor => /=.
    - by apply: iid.
    - by apply: g.
  Defined.
  
  (* 圏から左が恒等射である積圏への関手 *)
  Program Instance func_llecnac (I : C) : Functor D (C ×× D) (pair_obj I).
  Obligation 1.
  (* prod_mor (pair_obj I a) (pair_obj I b) *)
   Proof.
    apply: pair_mor;
      by apply llecnac_fmor.
  Defined.
  Obligation 2.
  Proof.
    split; [reflexivity | done].
  Defined.
  Obligation 3.
    split; [reflexivity | reflexivity].
  Defined.
  Obligation 4.
  Proof.
    split.
    - rewrite left_identity.
      reflexivity.
    - reflexivity.
  Defined.
  
  (* 積圏の右が恒等射である場合 *)
  Definition rlecnac_fmor (I : D) (a b : C) (f : a ~~{C}~~> b) :
    (pair_obj a I) ~~{C××D}~~> (pair_obj b I).
  Proof.
    apply: pair_mor => /=.
    - by apply: f.
    - by apply: iid.
  Defined.
  
  (* 圏から右が恒等射である積圏への関手 *)
  Program Instance func_rlecnac (I : D) : Functor C (C ×× D) (fun c => (pair_obj c I)).
  Obligation 1.
  (* prod_mor (pair_obj a I) (pair_obj b I) *)
  Proof.
    apply: pair_mor;
      by apply rlecnac_fmor.
  Defined.
  Obligation 2.
  Proof.
    split; [done | reflexivity].
  Defined.
  Obligation 3.
    split; [reflexivity | reflexivity].
  Defined.
  Obligation 4.
  Proof.
    split.
    - reflexivity.
    - rewrite right_identity.
      reflexivity.
  Defined.
  
  Context `{E : Category}.
  
  (* 積圏の結合律 *)
  Definition cossa : ((C ×× D) ×× E) -> (C ×× (D ×× E)).
  Proof.
    move=> [[HC HD] HE].
    by [].
  Defined.
  
  (* 次の定理のための補題 *)
  Definition cossa_fmor (a : ((C ×× D) ×× E)) (b : ((C ×× D) ×× E))
             (f : a ~~{(C ×× D) ×× E}~~> b) :
    (cossa a) ~~{C ×× (D ×× E)}~~> (cossa b).
  Proof.
    case: a f => HCxD HE.
    case: b => GCxD GE.
    case: HCxD.
    case: GCxD.
    move=> HC HD GC GD.
    case=> fCD fE.
    case: fCD => fC fD.
    done.
  Defined.

  (* cossa は、関手である。 *)
  Program Instance func_cossa : Functor ((C ×× D) ×× E) (C ×× (D ×× E)) cossa :=
    {|
      fmor := fun a b f => cossa_fmor f
    |}.
  Obligation 1.
  Proof.
    move: a b f f' H.
    (* ∀a b f f' _, cossa_fmor f === cossa_fmor f' *)
    move=> [[a11 a12] a2].                  (* case a *)
    move=> [[b11 b12] b2].                  (* case b *)
    move=> [[f11 f12] f2].                  (* case f *)
    move=> [[g11 g12] g2].                  (* case f' *)
    case; case.
    split; [exact | split; exact].
  Defined.
  Obligation 2.
  Proof.
    (* ∀ a : (C ×× D) ×× E, cossa_fmor iid === iid *)
    case: a => HCxD HE.
    case: HCxD => HC HD.
    split; [reflexivity | split; reflexivity].
  Defined.
  Obligation 3.
  Proof.
    move: a b c f g.
    (* ∀a b c f g, cossa_fmor g \\o cossa_fmor f === cossa_fmor (g \\o f) *)
    move=> [[a11 a12] a2].                  (* case a *)
    move=> [[b11 b12] b2].                  (* case b *)
    move=> [[c11 c12] c2].                  (* case c *)
    move=> [[f11 f12] f2].                  (* case f *)
    move=> [[g11 g12] g2].                  (* case g *)
    rewrite /=; split; [reflexivity | split; reflexivity].
  Defined.
  
  (* 同じ圏の積 C^2 *)
  Program Instance func_diagonal : Functor C (C ×× C) (fun c => (pair_obj c c)).
  Obligation 1.
  (* prod_mor (pair_obj a a) (pair_obj b b) *)
  Proof.
    by apply: pair_mor.
  Defined.
  Obligation 3.
  (* iid === iid ∧ iid === iid *)
  Proof.
    split; reflexivity.
  Defined.
  Obligation 4.
  (* g \\o f === g \\o f ∧ g \\o f === g \\o f *)
  Proof.
    split; reflexivity.
  Defined.
End ProductCategoryFunctors.

Section func_prod.
  
  Context `{C1 : Category} `{C2 : Category} `{C3 : Category} `{C4 : Category}.
  Variables (Fobj1 : C1 -> C2) (Fobj2 : C3 -> C4).
  Variables (F1 : Functor C1 C2 Fobj1) (F2 : Functor C3 C4 Fobj2).

  Definition functor_product_fobj (a : prod_obj C1 C3) :=
    pair_obj (Fobj1 (fst_obj a)) (Fobj2 (snd_obj a)).  
  Check functor_product_fobj.
  Check functor_product_fobj : prod_obj C1 C3 → prod_obj C2 C4.

  Definition functor_product_fmor (a b : (C1 ×× C3)) (f : a ~~{C1 ×× C3}~~> b) :
    (functor_product_fobj a) ~~{C2 ×× C4}~~> (functor_product_fobj b).
  Proof.
    case: a f => HC1 HC3 H.
    apply: pair_mor => /=.
    - apply (fmor F1); by case H.
    - apply (fmor F2); by case H.
  Defined.
  
  Hint Unfold fst_obj.

  Program Instance func_prod : Functor (C1 ×× C3) (C2 ×× C4) functor_product_fobj :=
    {|
      fmor := fun a b (f:a~~{C1 ×× C3}~~>b) => functor_product_fmor f
    |}.
  Obligation 1.
  Proof.
    move: a b f f' H.
    (* ∀a b f f' _, functor_product_fmor f === functor_product_fmor f' *)
    move=> [a1 a2].                         (* case a *)
    move=> [b1 b2].                         (* case b *)
    move=> [f1 f2].                         (* case f *)
    move=> [g1 g2].                         (* case g *)
    case=> H1 H2.                           (* case H *)
    split; [rewrite H1 | rewrite H2]; reflexivity.
  Defined.
  Obligation 2.
  Proof.
  (* ∀ a : C1 ×× C3, functor_product_fmor iid === iid *)
    case: a => [a1 a2] /=.
      by split; apply fmor_preserves_id.
  Defined.
  Obligation 3.
  Proof.
    move: a b c f g.
  (* ∀a b c f g,
   functor_product_fmor g \\o functor_product_fmor f ===
   functor_product_fmor (g \\o *)
    move=> [a1 a2].                         (* case a *)
    move=> [b1 b2].                         (* case b *)
    move=> [c1 c2].                         (* case c *)
    case=> f1 f3.                           (* case f *)
    case=> g1 g3.                           (* csae g *)
    by move=> /=; split; apply fmor_preserves_comp.
  Defined.
End func_prod.

Notation "f **** g" := (func_prod f g).

Program Instance iso_prod `{C : Category} `{D : Category} {a b : C} {c d : D}
         (ic : a ≅ b) (id : @Isomorphic _ _ D c d) :
  @Isomorphic _ _ (C ×× D) (pair_obj a c) (pair_obj b d).
Obligation 1.                               (* prod_mor (pair_obj a c) (pair_obj b d) *)
Proof.
  apply: pair_mor => /=.
  - by case: ic.
  - by case: id.
Defined.
Obligation 2.                               (* prod_mor (pair_obj b d) (pair_obj a c) *)
Proof.
  apply: pair_mor => /=.
  - by case: ic.
  - by case: id.
Defined.
Obligation 3.
Proof.
   by split; apply iso_comp1.
Defined.
Obligation 4.
Proof.
   by split; apply iso_comp2.
Defined.

(* END *)
