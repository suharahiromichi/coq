(**
池渕さん 「プログラマのための圏論の基礎」
- Categories for the Working Programmer -
1. 圏論とプログラミング、プロダクト
http://www.iij-ii.co.jp/lab/techdoc/category/category1.html

勉強のために、この表層をSSReflectに移した。
オリジナルと異なり、Setoid は自分で定義している。
これをeqTypeに移行することが、次の課題である。
*)

Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq.
(* Require Import Relation_Definitions.        (* relation *) *)
(* EquivExt はいらない？ *)
(* Require Import Classes.RelationClasses.     (* Equivalence *) *)
(* Require Import Classes.SetoidClass.         (* Setoid *) *)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(*
Reserved Notation "A ~> B" (at level 89, right associativity, only parsing).
Reserved Notation "f 'o' g" (at level 41, right associativity, only parsing).
 *)

Class Setoid (carrier : Type) :=
  {
    equiv : carrier -> carrier -> Prop
  }.
(* Coercion carrier : Setoid >-> Sortclass. *)
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
          commute h proj1 f -> commute h proj2 g -> h === mediating f g
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
  
(*
  Instance EquivExt : forall (A B : Type), Equivalence (@eqfun A B) :=
    {
      Equivalence_Reflexive := @frefl A B;
      Equivalence_Symmetric := @fsym A B;
      Equivalence_Transitive := @ftrans A B
    }.
*)
  Instance EqMor : forall (A B : Type), Setoid (A -> B) := (* Setoid *)
    {
      equiv := @eqfun B A
    }.

  Instance Func : Category EqMor :=         (* Category *)
    {
      idC A := id;
      composeC A B C := funcomp tt          (* compose *)
    }.
  Proof.
    - by rewrite //=.
    - by rewrite //=.
    - by rewrite //=.
  Defined.

  Variable P : Type -> Type -> Type.

  Instance Prod : Product Func prod Func :=
    {
      proj1 A B := @fst A B;
      proj2 A B := @snd A B ;
      mediating A B X := fun f g x => (f x, g x)
    }.
  Proof.
    - by rewrite //=.
    - by rewrite //=.
    - rewrite /commute /= /eqfun.
      move=> A B X f g h H H0 x.
      rewrite -H -H0.
      by apply surjective_pairing.
  Qed.
End Functions.

Section Orders.                          (* 半順序の世界 *)
  (* max of nat is a product *)
  
  Theorem ge_n : forall n, (n >= n)%coq_nat.          (* n >= n *)
  Proof.
    auto with arith.
  Qed.
  
  Theorem ge_trans' : forall n m p,
      (m >= p)%coq_nat -> (n >= m)%coq_nat -> (n >= p)%coq_nat.
  Proof.
    (* intros n m p. eauto using le_trans. *)
    admit.
  Qed.
  
  Definition eq_ge n m (p q : ge n m) := True.
  Check eq_ge.
  
(*
  Instance EquivGe : forall n m, Equivalence (@eq_ge n m).
  Proof.
    intros n m. constructor; constructor.
  Qed. 
*)  
  Instance EqGe : forall n m, Setoid (n >= m)%coq_nat := (* Setoid *)
    {
      equiv := (@eq_ge n m)
    }.
  
  Instance Order : Category EqGe :=         (* Category *)
    {
      idC := ge_n;
      composeC := ge_trans'
    }.
  Proof.
    simpl. unfold eq_ge. auto.
    simpl. unfold eq_ge. auto.
    simpl. unfold eq_ge. auto.
  Defined.
  
  Lemma max_val : forall n m, max n m = n \/ max n m = m.
  Proof.
    intros n m.
    admit.
(*    destruct (le_or_lt n m);
      [right|left]; [apply max_r|apply max_l];
      auto with arith.*)
  Qed.


  Theorem max_med : forall n m x,
      (n <= x)%coq_nat -> (m <= x)%coq_nat -> (max n m <= x)%coq_nat.
  Proof.
    intros n m x.
    destruct (max_val n m); intuition.
    admit.
    admit.
  Qed.
  
  Theorem max_ge1 : forall n m, (max n m >= n)%coq_nat.
  Proof.
    intros n m.
    destruct (max_val n m); intuition.
  Qed.
  
  Theorem max_ge2 : forall n m, (max n m >= m)%coq_nat.
  Proof.
    intros n m.
    destruct (max_val n m); intuition.
  Qed.
  
  Instance Max : Product Order max Order :=
    {
      proj1 := max_ge1;
      proj2 := max_ge2;
      mediating := max_med
    }.
  Proof.
    unfold commute. simpl. unfold eq_ge. auto.
    unfold commute. simpl. unfold eq_ge. auto.
    unfold commute. simpl. unfold eq_ge. auto.
  Defined.
  
  (* an application of parallel (***) *)
  
  Theorem parallel_max : forall n m l k,
      (n >= m)%coq_nat -> (l >= k)%coq_nat -> (max n l >= max m k)%coq_nat.
  Proof.
    apply (@parallel nat ge EqGe Order).
    apply Max.
  Qed.
  
End Orders.

(* モノイド *)
(* END *)
