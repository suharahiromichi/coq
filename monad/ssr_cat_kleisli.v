(**
Kleisli クライスリ圏
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

  Coercion Obj : Category >-> Sortclass.
  Coercion Mor : Category >-> Funclass.
  
  Class Kleisli (C : Category) (T : C -> C) :=
    {
      pure: forall {X : C}, C X (T X);
      bind: forall {X Y : C}, C X (T Y) -> C (T X) (T Y)
    }.
End Categories.

Section Monad.
  
  Instance EqMor : forall (A B : Set), Setoid :=
    {
      carrier := A -> B;
      equiv := @eqfun B A
    }.
  
  Instance Func : Category :=               (* Category *)
    {
      Obj := Set;
      Mor := EqMor;
      idC A := id;
      composeC A B C := funcomp tt          (* compose *)
    }.
  Proof.
    - by [].
    - by [].
    - by [].
  Defined.

  About option.              (* Coq.Init.Datatypes.option *)
  Check Some : forall A : Type, A -> option A.
  Check @None : forall A : Type, option A.
  
  Instance Maybe : @Kleisli Func option :=
    {
      pure X x := Some x;
      bind X Y f m :=
        match m with
          | Some x => f x
          | _ => None
        end
    }.
End Monad.

(* END *)
