(** SSReflect/Mathcomp の数学的構造 *)

Require Import List.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Set Printing All.               (* コアーションを省かずに表示する。 *)

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

Definition nat_of_bool (b : bool) := if b then 1 else 0.
Coercion nat_of_bool : bool >-> nat.

Fixpoint count (T : Type) (a : T -> bool) (s : list T) : nat :=
  match s with
  | nil => 0
  | (x :: s') => a x + count a s'           (* nat_of_bool *)
  end.

Inductive reflect (P : Prop) : bool -> Prop :=
| ReflectT :   P -> reflect P true
| ReflectF : ~ P -> reflect P false.

Definition eqfun (A B : Type) (f g : B -> A) := forall x : B, f x = g x.
Notation "f1 =1 f2" := (eqfun f1 f2) (at level 70, no associativity).

Definition pcancel (rT aT : Type) (f : aT -> rT) (g : rT -> option aT) :=
  forall x : aT, g (f x) = Some x.

Section Relations.
  Variable S T R : Type.
  
  Definition associative (op : S -> S -> S) :=
    forall (x y z : S), op x (op y z) = op (op x y) z.
  Definition commutative (op : S -> S -> T) :=
    forall (x y : S), op x y = op y x.
  Definition left_id (e : S) (op : S -> T -> T) :=
    forall (x : T), op e x = x.
  Definition right_id (e : S) (op : T -> S -> T) :=
    forall (x : T), op x e = x.
  Definition left_inverse (e : R) (inv : T -> S) (op : S -> T -> R) :=
    forall (x : T), op (inv x) x = e.
  Definition left_distributive (op : S -> T -> S) (add : S -> S -> S) :=
    forall (x y : S) (z : T), op (add x y) z = add (op x z) (op y z).
  Definition right_distributive (op : S -> T -> T) (add : T -> T -> T) :=
    forall (x : S) (y z : T), op x (add y z) = add (op x y) (op x z).
  
End Relations.

(** eqType *)
Module Equality.
  
  Record mixin_of (T : Type) :=
    Mixin {
        op : rel T;
        ax : forall x y, reflect (x = y) (op x y);
      }.
  
  Structure type :=
    Pack {
        sort :> Type;
        mixin : mixin_of sort;
      }.
End Equality.

Coercion Equality.sort : Equality.type >-> Sortclass.
Notation eqType := Equality.type.
Notation EqType := Equality.Pack.

Definition eq_op {T : eqType} := Equality.op (Equality.mixin T).
Check @eq_op : forall T : eqType, rel (Equality.sort T).
Check @eq_op : forall T : eqType, rel T.
Notation "x == y" := (eq_op x y) (at level 70, no associativity).
Notation "x != y" := (negb (@eq_op _ x y)) (at level 70, no associativity).

(** ChoiceType 可算選択公理 *)
Module Choice.
  
  Record mixin_of (T : Type) :=
    Mixin {
        find : pred T -> nat -> option T;
        ax1 : forall P n x, find P n = Some x -> P x;
        ax2 : forall P : pred T, (exists x, P x) -> exists n, find P n; (* isSome *)
        ax3 : forall P Q : pred T, P =1 Q -> find P =1 find Q;
      }.
  
  Record class_of (T : Type) :=
    Class {
        base :> Equality.mixin_of T;
        mixin : mixin_of T;
      }.
  
  Structure type :=
    Pack {
        sort :> Type;
        class : class_of sort;
      }.
  
  Coercion eqType (cT : type) := EqType (base (class cT)).
End Choice.

Coercion Choice.base : Choice.class_of >-> Equality.mixin_of.
Coercion Choice.mixin : Choice.class_of >-> Choice.mixin_of.
Coercion Choice.sort : Choice.type >-> Sortclass.
Notation choiceType := Choice.type.
Notation ChoiceType := Choice.Pack.
Canonical Structure Choice.eqType.

(** CountType *)
Module Countable.
  
  Record mixin_of (T : Type) :=
    Mixin {
        pickle : T -> nat;
        unpickle : nat -> option T;
        pickleK : pcancel pickle unpickle;
      }.
  
  Record class_of (T : Type) :=
    Class {
        base :> Choice.class_of T;
        mixin : mixin_of T;
      }.
  
  Structure type :=
    Pack {
        sort :> Type;
        class : class_of sort;
      }.

  Coercion eqType (cT : type) := EqType (base (class cT)).
  Coercion choiceType (cT : type) := ChoiceType (base (class cT)).
End Countable.

Coercion Countable.base : Countable.class_of >-> Choice.class_of.
Coercion Countable.mixin : Countable.class_of >-> Countable.mixin_of.
Coercion Countable.sort : Countable.type >-> Sortclass.
Notation countType := Countable.type.
Notation CountType := Countable.Pack.
Canonical Structure Countable.eqType.
Canonical Structure Countable.choiceType.

(** finType *)
Module Finite.
  
  (* T : Equality.sort T *)
  Definition count_mem (T : eqType) (x : T) (e : list T) :=
    count (fun y => x == x) e.
  
  Definition axiom (T : eqType) (e : list T) :=
    forall x : T, (count_mem x) e = 1.
  
  Record mixin_of (T : eqType) :=
    Mixin {
        mixin_base : Countable.mixin_of T;
        mixin_enum : list T;
        ax : axiom mixin_enum
      }.
  
  Record class_of (T : eqType) :=
    Class {
        base :> Countable.class_of T;
        mixin : mixin_of T
      }.
  
  Structure type :=
    Pack {
        sort :> eqType;
        class : class_of sort
      }.
  
  Coercion eqType (cT : type) := EqType (base (class cT)).
  Coercion choiceType (cT : type) := ChoiceType (base (class cT)).
  Coercion countType (cT : type) := CountType (base (class cT)).  
End Finite.

Coercion Finite.base : Finite.class_of >-> Countable.class_of.
Coercion Finite.mixin : Finite.class_of >-> Finite.mixin_of.
Coercion Finite.sort : Finite.type >-> eqType. (* Sortclass *)
Notation finType := Finite.type.
Notation FinType := Finite.Pack.
Canonical Structure Finite.eqType.
Canonical Structure Finite.choiceType.
Canonical Structure Finite.countType.

(** GRing *)
Module GRing.

  Delimit Scope ring_scope with R.
  Open Scope ring_scope.
  
  (** Zmodule Z加群 *)
  Module Zmodule.

    Record mixin_of (V : Type) :=
      Mixin {
          zero : V;
          opp : V -> V;
          add : V -> V -> V;
          ax1 : associative add;
          ax2 : commutative add;
          ax3 : left_id zero add;
          ax4 : left_inverse zero opp add;
        }.

    Record class_of (T : Type) :=
      Class {
          base : Choice.class_of T;
          mixin : mixin_of T
        }.
    
    Structure type :=
      Pack {
          sort :> Type;
          class : class_of sort;
          _ : Type;
        }.
    
    (* Pack の class メンバ関数とおなじなので、使わない。 *)
    Definition class' (cT : type) :=
      match cT as cT' return (class_of (sort cT')) with
      | @Pack sort class _ => class
      end.
    (* Mathcomp の場合： *)
    (* Definition class' := let: Pack s c as cT' := cT return class_of cT' in c. *)
    
    (*
    Coercion eqType (cT : type) :=
      @Equality.Pack (sort cT)
                     (@Choice.base (xT cT)
                                   (@base (xT cT) (class cT : class_of (xT cT)))).
     *)
    Coercion eqType (cT : type) := EqType (base (class cT)).
    Coercion choiceType (cT : type) := ChoiceType (base (class cT)).
  End Zmodule.
  
  Coercion Zmodule.base : Zmodule.class_of >-> Choice.class_of.
  Coercion Zmodule.mixin : Zmodule.class_of >-> Zmodule.mixin_of.
  Coercion Zmodule.sort : Zmodule.type >-> Sortclass.
  Notation zmodType := Zmodule.type.
  Notation ZmodType := Zmodule.Pack.
  (* zmodType に対して、== と != を使えるようにする。 *)
  Canonical Structure Zmodule.eqType.       (* one != 0 のため。 *)
  Canonical Structure Zmodule.choiceType.
  
  (* zero などの引数に、コアーション Zmodule.mixin が機能する。 *)
  (* Zmodule.zero (Zmodule.mixin (Zmodule.class V)) *)
  Definition zero V := Zmodule.zero (Zmodule.class V).
  Definition opp V := Zmodule.opp (Zmodule.class V).
  Definition add V := Zmodule.add (Zmodule.class V).
  
  Local Notation "0" := (zero _) : ring_scope.
  Local Notation "-%R" := (@opp _) : ring_scope.
  Local Notation "- x" := (opp x) : ring_scope.
  Local Notation "+%R" := (@add _) : ring_scope.
  Local Notation "x + y" := (add x y) : ring_scope.
  Local Notation "x - y" := (x + - y) : ring_scope.
  
  (** Ring *)
  Module Ring.
    
    Record mixin_of (R : zmodType) :=
      Mixin {
          one : R;
          mul : R -> R -> R;
          ax1 : associative mul;
          ax2 : left_id one mul;
          ax3 : right_id one mul;
          ax4 : left_distributive mul +%R;
          ax5 : right_distributive mul +%R;
          ax6 : one != 0;
        }.
    
    Record class_of (R : Type) :=
      Class {
          base : Zmodule.class_of R;
          mixin : mixin_of (Zmodule.Pack base R);
        }.
    
    Structure type :=
      Pack {
          sort :> Type;
          class : class_of sort;
          _ : Type;
        }.
    
    Coercion eqType (cT : type) := EqType (base (class cT)).
    Coercion choiceType (cT : type) := ChoiceType (base (class cT)).
    Coercion zmodType (cT : type) := ZmodType (base (class cT)) cT. (* 3引数 *)
  End Ring.
  
  Coercion Ring.base : Ring.class_of >-> Zmodule.class_of.
  Coercion Ring.mixin : Ring.class_of >-> Ring.mixin_of.
  Coercion Ring.sort : Ring.type >-> Sortclass.
  Notation ringType := Ring.type.
  Notation RingType := Ring.Pack.
  Canonical Structure Ring.eqType.
  Canonical Structure Ring.choiceType.
  Canonical Structure Ring.zmodType.
  
End GRing.
  
(* END *)
