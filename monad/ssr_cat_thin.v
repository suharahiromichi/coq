(**
やせた圏の例
*)

Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section Categories.

  Class Setoid :=
    {
      carrier : Type;
      equiv : carrier -> carrier -> Prop
    }.
  Coercion carrier : Setoid >-> Sortclass.
  Notation "x === z" := (equiv x z) (at level 70).
  
  Class Category :=
    {
      (* 対象の定義 *)
      Obj : Type;                           (* Category -> Type *)
      
      (* 射の定義 *)      
      Mor : Obj -> Obj -> Setoid;           (* Coersion が有効になる。 *)
      
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
End Categories.


(* 対象がやせている *)
Section Sample1.

  Instance EqNat : forall (A B : unit), Setoid :=
    {
      carrier := nat;
      equiv := eq
    }.

  Instance Add : Category :=
    {
      Obj := unit;
      Mor := EqNat;
      idC A := 0;
      composeC A B C := addn
    }.
  Proof.
    - by [].
    - by [].
    - move=> A B C D f g h.
      by rewrite addnA.
  Defined.
  
  Program Instance Mul : Category :=
    {
      Obj := unit;
      Mor := EqNat;
      idC A := 1;
      composeC A B C := muln
    }.
  Next Obligation.
  Proof.
    by rewrite mul1n.
  Qed.
  Next Obligation.
  Proof.
    by rewrite muln1.
  Qed.
  Next Obligation.
    by rewrite mulnA.
  Qed.

(*
ssr_cat_monoid も参照のこと。
モノイド、リストのcat 
 *)
End Sample1.


(* 射がやせている *)
Section Sample2.

  Definition eq_leq m n (p q : m <= n) := true.

  (* leq_trans とは前提の順番が違うので、作り直しておく。 *)
  Lemma leq_trans' : forall m n p : nat, n <= p -> m <= n -> m <= p.
  Proof.
    move=> m n p H1 H2.
    move: H2 H1.
      by apply: leq_trans.
  Qed.
  
  Instance EqLeq : forall (m n : nat), Setoid :=
    {
      carrier := m <= n;
      equiv := @eq_leq m n
    }.
  
  Instance SemiOrder : Category :=
    {
      Obj := nat;
      Mor := EqLeq;
      idC := leqnn;
      composeC := leq_trans'
    }.
  Proof.
    - by [].
    - by [].
    - by [].
  Defined.
End Sample2.
  
(* END *)
