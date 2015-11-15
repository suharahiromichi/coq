(**
池渕さん 「プログラマのための圏論の基礎」
- Categories for the Working Programmer -
1. 圏論とプログラミング、プロダクト
http://www.iij-ii.co.jp/lab/techdoc/category/category1.html

これをもとに、モノイドを作る。
*)

Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq.
(* Require Import Classes.RelationClasses.     (* Equivalence *) *)

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

Section Monoids.
  
  Instance EqNat : forall (A B : unit), Setoid :=
    {
      carrier := nat;
      equiv := eq
    }.
  
  Check Mor : Obj -> Obj -> Setoid.
  Check EqNat : unit -> unit -> Setoid.
  (* Obj := unit のもとで型は一致する。 *)
  
  Check composeC : Mor _ _ -> Mor _ _ -> Mor _ _.
  Check muln : nat -> nat -> nat.
  (* Mor _ _ は Setoid で、carrier によるコアーションのもとで、型は一致する。 *)
  
  Instance NatMonoid : Category :=          (* Category *)
    {
      Obj := unit;
      Mor := EqNat;
      idC A := 1;
      composeC A B C := muln                (* compose *)
    }.
  Proof.
    - move=> A B f /=.
        by rewrite mul1n.
    - move=> A B f /=.
        by rewrite muln1.
    - move=> A B C D f g h /=.
        by rewrite mulnA.
  Defined.

End Monoids.

(* END *)
