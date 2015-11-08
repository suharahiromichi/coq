(**
池渕さん 「プログラマのための圏論の基礎」
- Categories for the Working Programmer -
1. 圏論とプログラミング、プロダクト
http://www.iij-ii.co.jp/lab/techdoc/category/category1.html

勉強のために、この表層をSSReflectに移した。
オリジナルと同様にSetoidClassを使用しているが、
これをeqTypeに移行することが、次の課題である。
*)

Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq.
Require Import Relation_Definitions.        (* relation *)
Require Import Classes.RelationClasses.     (* Equivalence *)
Require Import Classes.SetoidClass.         (* Setoid *)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(*
Reserved Notation "A ~> B" (at level 89, right associativity, only parsing).
Reserved Notation "f 'o' g" (at level 41, right associativity, only parsing).
 *)

Notation "x === z" := (equiv x z) (at level 70).

Section Categories.
  Variable Obj : Type.                      (* 対象の定義 *)
  Variable Mor : Obj -> Obj -> Type.        (* 射の定義 *)
  Variable smor : forall (A B : Obj), Setoid (Mor A B).
  
  Class Category :=
    {
      (* 恒等射の定義 *)
      idC : forall {A : Obj}, Mor A A;
      
      (* 射の合成の定義 *)
      composeC : forall {A B C : Obj}, Mor B C -> Mor A B -> Mor A C;
      
      (* 単位律の定義 *)
      left_identity : forall (A B : Obj) (f : Mor A B), composeC idC f === f;
      right_identity : forall (A B : Obj) (f : Mor A B), composeC f idC === f;
      
      (* 結合律の定義 *)
      associativity : forall (A B C D : Obj)
                             (f : Mor A B) (g : Mor B C) (h : Mor C D),
          composeC (composeC h g) f === composeC h (composeC g f)
    }.
  
   (* == は Setoid で定義された equiv であり、
   省略された引数は @equiv (A ~> D) (smor A D) *)

(*
  Notation "A ~> B" := (Mor A B).           (* 射 *)
  Notation "f 'o' g" := (composeC f g).     (* 射の結合 *)
*)
  Variable Cat : Category.

  (* 可換の定義 *)
  Definition commute {A B C : Obj} (f : Mor A B) (g : Mor B C) (h : Mor A C) :=
    composeC g f === h.


  (* 直積 *)
  Class Product (P : Obj -> Obj -> Obj) (CP : Category) :=
    {
      proj1 : forall {A B : Obj}, Mor (P A B) A;
      proj2 : forall {A B : Obj}, Mor (P A B) B;
      
      (* 仲介射 *)
      mediating : forall {A B X : Obj}, Mor X A -> Mor X B -> Mor X (P A B);
      (* mediating = (&&&) *)
      
      (* Proofs *)
      (* commute CP のCPは、Section Commutativity の Cat に渡される。 *)
      med_commute1 : forall (A B X : Obj) (f : Mor X A) (g : Mor X B),
          commute (mediating f g) proj1 f;
      med_commute2 : forall (A B X : Obj) (f : Mor X A) (g : Mor X B),
          commute (mediating f g) proj2 g;
      med_unique : forall (A B X : Obj)
                          (f : Mor X A) (g : Mor X B) (h : Mor X (P A B)),
          commute h proj1 f -> commute h proj2 g -> h == mediating f g
    }.

  Variable P : Obj -> Obj -> Obj.
  Variable Prod : Product P Cat.

  Definition parallel {A B C D : Obj}
             (f : Mor A B) (g : Mor C D) : Mor (P A C) (P B D) :=
    let (p1, p2) :=
        (@proj1 P Cat Prod A C, @proj2 P Cat Prod A C) in
    mediating (composeC f p1) (composeC g p2).
  (* parallel = (***) または <f,g> *)

End Categories.


Section Functions.                  (* 集合と関数の世界 *)
  (* Ordinary tuples are products *)
  
(*  Definition Map A B := A -> B. *)
  
(*  Definition eq_ext {A B : Type} (f g : A -> B) := forall x, f x = g x. *)
  
  Theorem refl_ext : forall (A B : Type) (f : A -> B), (@eqfun B A) f f.
  Proof.
    unfold eqfun. auto.
  Qed.
  
  Theorem symm_ext : forall (A B : Type) (f g :A -> B),
      eqfun f g -> eqfun g f.
  Proof.
    unfold eqfun. auto.
  Qed.
  
  Theorem trans_ext : forall (A B : Type) (f g h : A -> B),
      eqfun f g -> eqfun g h -> eqfun f h.
  Proof.
    unfold eqfun. eauto using eq_trans.
  Qed.
  
  Instance ReflExt : forall (A B : Type), Reflexive (@eqfun A B) :=
    {
      reflexivity := (@refl_ext B A)
    }.
  
  Instance SymmExt : forall (A B : Type), Symmetric (@eqfun A B) :=
    {
      symmetry := @symm_ext B A
    }.
  
  Instance TransExt : forall (A B : Type), Transitive (@eqfun A B) :=
    {
      transitivity := @trans_ext B A
    }.
  
  Instance EquivExt : forall (A B : Type), Equivalence (@eqfun A B) :=
    {
      Equivalence_Reflexive := @ReflExt A B;
      Equivalence_Symmetric := @SymmExt A B;
      Equivalence_Transitive := @TransExt A B
    }.

(*  Instance EqMor : forall (A B : Type), Setoid (Map A B) := (* Setoid *) *)
  Instance EqMor : forall (A B : Type), Setoid (A -> B) := (* Setoid *)
    {
      equiv := @eqfun B A
    }.

  Instance Func : Category EqMor :=         (* Category *)
    {
      idC A := id;
      composeC A B C := funcomp tt           (* funcomp *)
    }.
  Proof.
    unfold equiv. red. unfold eqfun. auto.
    unfold equiv. red. unfold eqfun. auto.
    unfold equiv. red. unfold eqfun. auto.
  Defined.

  Variable P : Type -> Type -> Type.

  Instance Prod : Product _ prod Func :=
    {
      proj1 A B := fst;
      proj2 A B := snd;
      mediating A B X := fun f g x => (f x, g x)
    }.
  Proof.
    unfold commute. simpl. unfold eqfun. auto.
    unfold commute. simpl. unfold eqfun. auto.
    unfold commute. simpl. unfold eqfun. unfold funcomp.
    intros.
    rewrite <- H. rewrite <- H0.
    apply surjective_pairing.
  Qed.
  
End Functions.

