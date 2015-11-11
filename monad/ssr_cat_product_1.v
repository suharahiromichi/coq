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
Require Import Classes.RelationClasses.     (* Equivalence *)

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
  (* === は Setoid で定義された equiv であり、
   省略された引数は @equiv (Mor A D) (smor A D) *)

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

(* *********************** *)
(* 関数の世界、関数 と 直積 *)
(* *********************** *)
Section Functions.
  (* Ordinary tuples are products *)
  
  Instance EquivExt : forall (A B : Type), Equivalence (@eqfun A B) := (* notu *)
    {
      Equivalence_Reflexive := @frefl A B;
      Equivalence_Symmetric := @fsym A B;
      Equivalence_Transitive := @ftrans A B
    }.
  
  Instance EqMor : forall (A B : Type), Setoid (A -> B) :=
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

(* ********************** *)
(* 半順序の世界、>= と max *)
(* ********************** *)
Section Orders.
  (* max of nat is a product *)
  
  Definition geq m n := m >= n.
  
  Check leqnn : forall n : nat, n <= n.

  Lemma geq_trans : forall m n p : nat, n >= p -> m >= n -> m >= p.
  Proof.
    move=> m n p H1 H2.
    move: H1 H2.
      by apply: leq_trans.
  Qed.
  
  Definition eq_geq m n (p q : m >= n) := true.
  
  Instance EquivGeq : forall m n, Equivalence (@eq_geq m n). (* notu *)
  Proof.
      by [].
  Qed. 
  
  Instance EqGeq : forall m n, Setoid (m >= n) :=
    {
      equiv := (@eq_geq m n)
    }.
  
  Instance Order : Category EqGeq :=
    {
      idC := leqnn;
      composeC := geq_trans
    }.
  Proof.
    - by [].
    - by [].
    - by [].
  Defined.
  
  Check leq_maxl : forall m n : nat, m <= maxn m n.
  Check leq_maxr : forall m n : nat, n <= maxn m n.  
  
  Lemma max_med : forall m n x,
      m <= x -> n <= x -> maxn m n <= x.
  Proof.
    move=> m n x H1 H2.
    rewrite geq_max.
    apply/andP.
      by split.
  Qed.
  
  Instance Max : Product Order maxn Order :=
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
    Check @parallel nat geq EqGeq Order maxn.
    Check @parallel nat geq EqGeq Order maxn Max m n p q.
      by apply: (@parallel nat geq EqGeq Order maxn Max m n p q).
  Qed.
End Orders.

(* ********************** *)
(* 半順序の世界、<= と min *)
(* ********************** *)
Section Orders'.
  
  Check leqnn : forall n : nat, n <= n.

  (* leq_trans とは前提の順番が違うので、作り直しておく。 *)
  Lemma leq_trans' : forall m n p : nat, n <= p -> m <= n -> m <= p.
  Proof.
    move=> m n p H1 H2.
    move: H2 H1.
      by apply: leq_trans.
  Qed.
  
  Definition eq_leq m n (p q : m <= n) := true.
  
  Instance EquivLeq : forall m n, Equivalence (@eq_leq m n). (* notu *)
  Proof.
      by [].
  Qed. 
  
  Instance EqLeq : forall m n, Setoid (m <= n) :=
    {
      equiv := (@eq_leq m n)
    }.
  
  Instance Order' : Category EqLeq :=
    {
      idC := leqnn;
      composeC := leq_trans'
    }.
  Proof.
    - by [].
    - by [].
    - by [].
  Defined.

  Check geq_minl : forall m n : nat, minn m n <= m.
  Check geq_minr : forall m n : nat, minn m n <= n.
  
  Lemma min_med : forall m n x,
      x <= m -> x <= n -> x <= minn m n.
  Proof.
    move=> m n x H1 H2.
    rewrite leq_min.
    apply/andP.
      by split.
  Qed.  
  
  Instance Min : Product Order' minn Order' :=
    {
      proj1 := geq_minl;
      proj2 := geq_minr;
      mediating := min_med
    }.
  Proof.
    - by [].
    - by [].
    - by [].
  Defined.
  (* an application of parallel (***) *)
  
  Theorem parallel_min : forall m n p q,
      m <= n -> p <= q -> minn m p <= minn n q.
  Proof.
    move=> m n p q.
    Check @parallel nat leq  EqLeq Order' minn.
    Check @parallel nat leq  EqLeq Order' minn Min m n p q.
      by apply: (@parallel nat leq EqLeq Order' minn Min m n p q).
  Qed.  
End Orders'.

(* END *)
