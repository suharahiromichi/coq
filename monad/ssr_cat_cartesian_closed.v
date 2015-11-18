(**
デカルト閉圏
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
  
  (* 可換の定義 *)
  Definition commute {CP : Category} {A B C : Obj}
             (f : Mor A B) (g : Mor B C) (h : Mor A C) :=
    composeC g f === h.
  

  (* 直積 *)
  Class Product {CP : Category} :=
    {
      P : Obj -> Obj -> Obj;
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

  Class Cartesian_Closed {CCC : Category} {CP : Product} :=
    {
      Exp : Obj -> Obj -> Obj;
      eval  : forall {X Y Z : Obj}, Mor (P (Exp Y X) Z) Y;
      f     : forall {X Y Z : Obj}, Mor (P X Z) Y;
      curry : forall {X Y Z : Obj}, Mor (P X Z) Y -> Mor X (Exp Y X)
    }.
End Categories.

(**
この世で一番簡単なデカルト閉圏
キメラ 2011-01-31
 *)
Section SimplCCC.

  Instance EqMor : forall (A B : bool), Setoid :=
    {
      carrier := bool -> bool;
      equiv := @eqfun bool bool
    }.
  
  Instance Func : Category :=               (* Category *)
    {
      Obj := bool;
      Mor := EqMor;
      idC A := id;
      composeC A B C := funcomp tt          (* compose *)
    }.
  Proof.
    - by [].
    - by [].
    - by [].
  Defined.

  Instance Prod : Product :=
    {
      P := andb;                            (* && *)
      proj1 A B := id;                      (* XXXX *)
      proj2 A B := id;                      (* XXXX *)
      mediating A B X :=
        fun (f g : bool -> bool) (x : bool) => f x && g x
    }.
  Proof.
    - admit.
    - admit.
    - admit.
  Qed.
  
  Compute false ==> false.                  (* true *)
  Compute true ==> false.                   (* false *)
  Compute false ==> true.                   (* true *)
  Compute true ==> true.                    (* true *)
  Instance CCC : Cartesian_Closed :=
    {
      Exp := implb                          (* ==> *)
    }.

End SimplCCC.

(* 未完 *)
