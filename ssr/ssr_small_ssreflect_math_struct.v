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

Definition negb (b : bool) := if b then false else true.
Definition pred := fun T : Type => T -> bool.
Definition rel := fun T : Type => T -> pred T.

Definition is_true (x : bool) : Prop := x = true.
Coercion is_true : bool >-> Sortclass.

Definition isSome (T : Type) (u : option T) :=
  match u return bool with
  | Some _ => true
  | None => false
  end.
Coercion isSome : option >-> bool.

Inductive reflect (P : Prop) : bool -> Prop :=
| ReflectT :   P -> reflect P true
| ReflectF : ~ P -> reflect P false.

Definition eqfun (A B : Type) (f g : B -> A) := forall x : B, f x = g x.
Notation "f1 =1 f2" := (eqfun f1 f2) (at level 70, no associativity).

Definition pcancel (rT aT : Type) (f : aT -> rT) (g : rT -> option aT) :=
  forall x : aT, g (f x) = Some x.

Section Relations.
  Variable S T R : Type.
  
  Definition associative (op : S -> S -> S)
             (x y z : S) := op x (op y z) = op (op x y) z.
  Definition commutative (op : S -> S -> T)
             (x y : S) := op x y = op y x.
  Definition left_id (e : S) (op : S -> T -> T)
             (x : T) := op e x = x.
  Definition right_id (e : S) (op : T -> S -> T)
             (x : T) := op x e = x.
  
  Definition left_inverse (e : R) (inv : T -> S) (op : S -> T -> R)
             (x : T) := op (inv x) x = e.
  Definition left_distributive (op : S -> T -> S) (add : S -> S -> S)
             (x y : S) (z : T) := op (add x y) z = add (op x z) (op y z).
  Definition right_distributive (op : S -> T -> T) (add : T -> T -> T)
             (x : S) (y z : T) := op x (add y z) = add (op x y) (op x z).
End Relations.

(** eqType *)
Module Equality.
  
  Record mixin_of (T : Type) : Type :=
    Mixin {
        op : rel T;
        a : forall x y, reflect (x = y) (op x y)
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
Check eq_op : forall T : eqType, rel (Equality.sort T).

Notation "x == y" := (@eq_op _ x y) (at level 70, no associativity).
Notation "x != y" := (negb (@eq_op _ x y)) (at level 70, no associativity).

(** ChoiceType *)
Module Choice.
  
  Record mixin_of (T : Type) :=
    Mixin {
        find : pred T -> nat -> option T;
        a1 : forall P n x, find P n = Some x -> P x;
        a2 : forall P : pred T, (exists x, P x) -> exists n, find P n; (* isSome *)
        a3 : forall P Q : pred T, P =1 Q -> find P =1 find Q
      }.
  
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

(** CountType *)
Module Countable.
  
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


Delimit Scope ring_scope with R.
Delimit Scope term_scope with T.
Local Open Scope ring_scope.

(* Module Import GRing. *)
Module GRing.
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
Section ClassDef.

Record class_of T := Class { base : Choice.class_of T; mixin : mixin_of T }.
Local Coercion base : class_of >-> Choice.class_of.

Structure type := Pack {sort; _ : class_of sort; _ : Type}.
Local Coercion sort : type >-> Sortclass.
Variables (T : Type) (cT : type).
Definition class := let: Pack c _ as cT' := cT return class_of cT' in c.


End ClassDef.

Module Exports.
Coercion base : class_of >-> Choice.class_of.
Coercion mixin : class_of >-> mixin_of.
Coercion sort : type >-> Sortclass.
Bind Scope ring_scope with sort.
(*
Coercion eqType : type >-> Equality.type.
Canonical eqType.
Coercion choiceType : type >-> Choice.type.
Canonical choiceType.
*)
Notation zmodType := type.
Notation ZmodMixin := Mixin.
End Exports.

End Zmodule.
Import Zmodule.Exports.

Definition zero V := Zmodule.zero (Zmodule.class V).
Definition opp V := Zmodule.opp (Zmodule.class V).
Definition add V := Zmodule.add (Zmodule.class V).

Local Notation "0" := (zero _) : ring_scope.
Local Notation "-%R" := (@opp _) : ring_scope.
Local Notation "- x" := (opp x) : ring_scope.
Local Notation "+%R" := (@add _) : ring_scope.
Local Notation "x + y" := (add x y) : ring_scope.
Local Notation "x - y" := (x + - y) : ring_scope.

(*

Module GRing.
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
    
    Coercion sort : type >-> Sortclass.
    Variables (T : Type) (cT : type).
    Definition class := let: Pack c _ as cT' := cT return class_of cT' in c.
  End Zmodule.

Variable T : eqType.
Variable a : (Equality.sort T).
Variable a' : (Equality.sort T).
Check a != a.

Variable R : zmodType.
Variable b : (Zmodule.sort R).
Variable b' : R.
Check b != b.
Check b' != b'.
 *)

  Module Ring.
    Record mixin_of (R : zmodType) : Type :=
      Mixin {
          one : R;
          mul : R -> R -> R;
          assoc : forall (x y z : R), @associative R mul x y z;
          l_id : forall (x : R),
              @left_id R R one mul x;
          r_id : forall (x : R),
              @right_id R R one mul x;
          l_d : forall (x y z : R), @left_distributive R R mul +%R x y z;
          r_d : forall (x y z : R), @right_distributive R R mul +%R x y z;
          (* onez : one != 0 *)
        }.
    (* 
          one : Zmodule.sort R;
          mul : Zmodule.sort R -> Zmodule.sort R -> Zmodule.sort R;
          assoc : forall (x y z : Zmodule.sort R), @associative (Zmodule.sort R) mul x y z;
          l_id : forall (x : Zmodule.sort R),
              @left_id (Zmodule.sort R) (Zmodule.sort R) one mul x;
          r_id : forall (x : Zmodule.sort R),
              @right_id (Zmodule.sort R) (Zmodule.sort R) one mul x;
            l_d : forall (x y z : Zmodule.sort R),
            @left_distributive (Zmodule.sort R) (Zmodule.sort R) mul
            (addZ _ (Zmodule.sort R) (Zmodule.sort R)) x y z;
            r_d : right_distributive mul Zmodule.add;
            
    Record class_of (R : Type) : Type :=
      Class {
          base : Zmodule.class_of R;
          mixin : mixin_of (Zmodule.Pack base R)
        }.

     *)
(*    
    Variable R : Type.
    Variable base : Zmodule.class_of R.
    Check Zmodule.Pack base R : Zmodule.type.
    Check Zmodule.Pack base R : zmodType.
  *)  
    Record class_of (R : Type) : Type :=
      Class {
          base : Zmodule.class_of R;
          mixin : mixin_of (Zmodule.Pack base R)
        }.

    Structure type :=
      Pack {
          sort; _ : class_of sort;
          _ : Type
        }.
    
    Coercion sort : type >-> Sortclass.
    Variables (T : Type) (cT : type).
    Definition class := let: Pack c _ as cT' := cT return class_of cT' in c.
    
  End Ring.
End GRing.
  
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
