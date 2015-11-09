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
Require Import Classes.RelationClasses.     (* Equivalence *)
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
  
  Instance EquivExt : forall (A B : Type), Equivalence (@eqfun A B) :=
    {
      Equivalence_Reflexive := @frefl A B;
      Equivalence_Symmetric := @fsym A B;
      Equivalence_Transitive := @ftrans A B
    }.
  
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
  
  Check leqnn : forall n : nat, n <= n.

  (* leq_trans とは前提の順番が違うので、作り直しておく。 *)
  Lemma leq_trans' : forall m n p : nat, n <= p -> m <= n -> m <= p.
  Proof.
    move=> m n p H1 H2.
    move: H2 H1.
    by apply: leq_trans.
  Qed.

  (* leq_trans とは前提の順番が違うので、作り直しておく。 *)
  Lemma leq_trans'' : forall m n p : nat, p <= n -> n <= m -> p <= m.
  Proof.
    move=> m n p H1 H2.
    move: H1 H2.
    by apply: leq_trans.
  Qed.
  
  Definition eq_leq m n (p q : m <= n) := true.
  Definition eq_geq m n (p q : m >= n) := true.
  
  Instance EquivLeq : forall m n, Equivalence (@eq_leq m n).
  Proof.
    by [].
  Qed. 
  
  Instance EqGeq : forall m n, Setoid (m >= n) :=
    {
      equiv := (@eq_geq m n)
    }.
  
  Instance EqLeq : forall m n, Setoid (m <= n) :=
    {
      equiv := (@eq_leq m n)
    }.
  
  Instance Order' : Category EqGeq :=
    {
      idC := leqnn;
      composeC := leq_trans''
    }.
  Proof.
    - by [].
    - by [].
    - by [].
  Defined.
  
  Instance Order : Category EqLeq :=
    {
      idC := leqnn;
      composeC := leq_trans'
    }.
  Proof.
    - by [].
    - by [].
    - by [].
  Defined.
  
  Check leq_maxl : forall m n : nat, m <= maxn m n.
  Check leq_maxr : forall m n : nat, n <= maxn m n.  
  
  (* Arith/Lt.v *)
  Lemma leq_or_lt : forall m n : nat, m <= n \/ n < m.
  Proof.
    move=> m n.
    by pattern m, n; apply nat_double_ind; auto with arith.
  Qed.
  
  Lemma max_val : forall m n, maxn m n = m \/ maxn m n = n.
  Proof.
    move=> m n.
    case: (leq_or_lt m n).
    - right.
        by apply/maxn_idPr.
    - left.
        apply/maxn_idPl.
          by auto with arith.
  Qed.
  
  Lemma max_med : forall m n x,
      m <= x -> n <= x -> maxn m n <= x.
  Proof.
    intros n m x.
    case: (max_val n m); by move=> ->.
  Qed.

  Instance Max : Product Order' maxn Order' :=
    {
      proj1 := leq_maxl;
      proj2 := leq_maxr;
      mediating := max_med
    }.
  Proof.
    - by [].
    - by [].
    - by [].
  Defined.
  (* an application of parallel (***) *)
  
  Theorem parallel_max : forall m n p q,
      m >= n -> p >= q -> maxn m p >= maxn n q.
  Proof.
    move=> m n p q.
    Check @parallel nat (fun m n=> m >= n)  EqGeq Order' maxn.
    Check @parallel nat (fun m n=> m >= n)  EqGeq Order' maxn Max n m p q.
    by apply: (@parallel nat (fun m n=> m >= n)  EqGeq Order' maxn Max).
  Qed.

End Orders.

(* モノイド *)
(* END *)
