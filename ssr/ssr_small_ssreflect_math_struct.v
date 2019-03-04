(** SSReflect/Mathcomp の数学的構造 *)
(*
From mathcomp Require Import all_ssreflect.

Set Printing All.
Print Choice.mixin_of.
Print Countable.mixin_of.
Print Finite.mixin_of.

From mathcomp Require Import all_algebra.
*)
Require Import List.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Definition is_true (x : bool) : Prop := x = true.
Coercion is_true : bool >-> Sortclass.

Definition pred := fun T : Type => T -> bool.

Inductive reflect (P : Prop) : bool -> Prop :=
| ReflectT :   P -> reflect P true
| ReflectF : ~ P -> reflect P false.

Module Equality.
  Definition rel := fun T : Type => T -> pred T.
  
  Record mixin_of (T : Type) : Type :=
    Mixin {
        op : rel T;
        ax : forall x y, reflect (x = y) (op x y)
      }.
  
  Structure type : Type :=
    Pack {
        sort :> Type;
        mixin : mixin_of sort
      }.
End Equality.

Notation eqType := Equality.type.
Notation EqType := Equality.Pack.

Definition eq_op T := Equality.op (Equality.mixin T).
(* @Equality.op (Equality.sort T) (Equality.mixin T). *)
Check eq_op : forall T : eqType, Equality.rel (Equality.sort T).
Notation "x == y" := (@eq_op _ x y) (at level 70, no associativity).
(* T : eqType の部分がimplicitである。 *)

Print Graph.
Definition isSome (T : Type) (u : option T) :=
  match u return bool with
  | Some _ => true
  | None => false
  end.
Coercion isSome : option >-> bool.

Module Choice.
  
  Definition eqfun (A B : Type) (f g : B -> A) :=
    forall x : B, f x = g x.
  Print eqfun.
  Notation "f1 =1 f2" := (eqfun f1 f2) (at level 70, no associativity).

  Record mixin_of (T : Type) :=
    Mixin {
        find : pred T -> nat -> option T;
        fsm : forall P n x, find P n = Some x -> P x;
        exf : forall P : pred T, (exists x, P x) -> exists n, find P n;
        feq : forall P Q : pred T, P =1 Q -> find P =1 find Q
      }.
  Print isSome.
  
  Record class_of (T : Type) :=
    Class {
        base :> Equality.mixin_of T;
        mixin : mixin_of T
      }.
  
  Structure type :=
    Pack {
        sort :> Type;
        class : class_of sort
      }.
End Choice.

Module Countable.
  
  Definition pcancel (rT aT : Type) (f : aT -> rT) (g : rT -> option aT) :=
    forall x : aT, g (f x) = Some x.

  Record mixin_of (T : Type) :=
    Mixin {
        pickle : T -> nat;
        unpickle : nat -> option T;
        pickleK : pcancel pickle unpickle
      }.
  
  Record class_of (T : Type) :=
    Class {
        base :> Choice.class_of T;
        mixin : mixin_of T
      }.
  
  Structure type :=
    Pack {
        sort :> Type;
        class : class_of sort
      }.

End Countable.

Definition associative (S : Type) (op : S -> S -> S) (x y z : S) :=
  op x (op y z) = op (op x y) z.
Definition commutative (S T : Type) (op : S -> S -> T) (x y : S) :=
  op x y = op y x.
Definition left_id (S T : Type) (e : S) (op : S -> T -> T) (x : T) :=
  op e x = x.
Definition right_id (S T : Type) (e : S) (op : T -> S -> T) (x : T) :=
  op x e = x.

Definition left_inverse (S T R : Type) (e : R)
           (inv : T -> S) (op : S -> T -> R) (x : T) := op (inv x) x = e.

Definition left_distributive (S T : Type) (op : S -> T -> S) (add : S -> S -> S)
           (x y : S) (z : T) := op (add x y) z = add (op x z) (op y z).
Definition right_distributive (S T : Type) (op : S -> T -> T) (add : T -> T -> T)
           (x : S) (y z : T) := op x (add y z) = add (op x y) (op x z).

Module Zmodule.

  Record mixin_of (V : Type) : Type :=
    Mixin {
        zero : V;
        opp : V -> V;
        add : V -> V -> V;
        assoc : forall (x y z : V), @associative V add x y z;
        commu : forall (x y : V), @commutative V V add x y;
        l_id : forall (x : V), @left_id V V zero add x;
        linv : forall (x : V), @left_inverse V V V zero opp add x
      }.

  Record class_of (T : Type) :=
    Class {
        base : Choice.class_of T;
        mixin : mixin_of T
      }.
  
  Structure type :=
    Pack {
        sort; _ : class_of sort;
        _ : Type
      }.
End Zmodule.

Notation zmodType := Zmodule.type.
Notation addZ := (@Zmodule.add _).

Module Ring.
  Record mixin_of (R : zmodType) : Type :=
    Mixin {
        one : Zmodule.sort R;
        mul : Zmodule.sort R -> Zmodule.sort R -> Zmodule.sort R;
        assoc : forall (x y z : Zmodule.sort R), @associative (Zmodule.sort R) mul x y z;
        l_id : forall (x : Zmodule.sort R),
            @left_id (Zmodule.sort R) (Zmodule.sort R) one mul x;
        r_id : forall (x : Zmodule.sort R),
            @right_id (Zmodule.sort R) (Zmodule.sort R) one mul x;
(*
        l_d : forall (x y z : Zmodule.sort R),
            @left_distributive (Zmodule.sort R) (Zmodule.sort R) mul
                               (addZ _ (Zmodule.sort R) (Zmodule.sort R)) x y z;
        r_d : right_distributive mul Zmodule.add; *)
        (* _ : one != 0 *)
      }.

  Record class_of (R : Type) : Type :=
    Class {
        base : Zmodule.class_of R;
        mixin : mixin_of (Zmodule.Pack base R)
      }.
End Ring.

Definition nat_of_bool (b : bool) := if b then 1 else 0.
Coercion nat_of_bool : bool >-> nat.

Module Finite.
  Fixpoint count (T : Type) (a : T -> bool) (s : list T) : nat :=
    match s with
    | nil => 0
    | (x :: s') => a x + count a s'
    end.
  
  Locate "_ == _".
  Print eq_op.
  Definition count_mem (T : eqType) (x : Equality.sort T) (e : list (Equality.sort T)) :=
    count (fun y => x == x) e.
  

  Print count_mem.     (* Notation count_mem x := (count (pred1 x)) *)
  (* pred1 = 
     fun (T : Equality.Exports.eqType) (a1 : T) => [pred x | xpred1 a1 x]
     : forall T : Equality.Exports.eqType, T -> simpl_pred T
   *)
  
  Definition axiom (T : eqType) (e : list (Equality.sort T)) :=
    forall x : Equality.sort T, (count_mem x) e = 1.

(*
  Variable T : eqType.
  Variable  mixin_enum : list (Equality.sort T).
  Check axiom mixin_enum.
*)
  Record mixin_of (T : eqType) :=
    Mixin {
        mixin_base : Countable.mixin_of (Equality.sort T);
        mixin_enum : list (Equality.sort T);
        ax : axiom mixin_enum
      }.
  
  Check mixin_enum : forall T : eqType,   mixin_of T -> list (Equality.sort T).
  Check axiom : forall T : eqType, list (Equality.sort T) -> Prop.
  Check @axiom _ (mixin_enum _) : Prop.
  
  Record class_of (T : eqType) :=
    Class {
        base :> Countable.class_of (Equality.sort T);
        mixin : mixin_of T
      }.
  
  Structure type :=
    Pack {
        sort :> eqType;
        class : class_of sort
      }.
End Finite.


(* END *)
