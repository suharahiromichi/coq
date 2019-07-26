(** SSReflect/Mathcomp の数学的構造 *)

Require Import List.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* Set Printing All. *)               (* コアーションを省かずに表示する。 *)

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

(*
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
*)

(** eqType *)
Module Equality.
  
  Record mixin_of (T : Type) :=
    Mixin {
        op : rel T;
        ax : forall x y : T, reflect (x = y) (op x y);
      }.
  
  Structure type :=
    Pack {
        sort :> Type;
        mixin : mixin_of sort;
      }.
End Equality.

Coercion Equality.sort : Equality.type >-> Sortclass.
Notation EqMixin := Equality.Mixin.
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
Notation ChoiceMixin := Choice.Mixin.
Notation ChoiceClass := Choice.Class.
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
Notation CountMixin := Countable.Mixin.
Notation CountClass := Countable.Class.
Notation countType := Countable.type.
Notation CountType := Countable.Pack.
Canonical Structure Countable.eqType.
Canonical Structure Countable.choiceType.

(** finType *)
Module Finite.
  
  (* T : Equality.sort T *)
  Definition count_mem (T : eqType) (x : T) (e : list T) :=
    count (fun y => y == x) e.
  
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
Notation FinMixin := Finite.Mixin.
Notation FinClass := Finite.Class.
Notation finType := Finite.type.
Notation FinType := Finite.Pack.
Canonical Structure Finite.eqType.
Canonical Structure Finite.choiceType.
Canonical Structure Finite.countType.

(** GRing *)
(* Module GRing. *)

  Delimit Scope ring_scope with R.
  Open Scope ring_scope.
  
  (** Zmodule Z加群 *)
  Module Zmodule.

    Record mixin_of (V : Type) :=
      Mixin {
          zero : V;
          opp : V -> V;
          add : V -> V -> V;
          ax1 : forall (x y z : V),
              add x (add y z) = add (add x y) z; (* associative add *)
          ax2 : forall (x y : V),
              add x y = add y x;                (* commutative add *)
          ax3 : forall (x : V), add zero x = x; (* left_id zero add *)
          ax4 : forall (x : V), add (opp x) x = zero; (* left_inverse zero opp add *)
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
  Notation ZmodMixin := Zmodule.Mixin.
  Notation ZmodClass := Zmodule.Class.
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
          ax1 : forall (x y z : R),
              mul x (mul y z) = mul (mul x y) z; (* associative mul *)
          ax2 : forall (x : R), mul one x = x;   (* left_id one mul *)
          ax3 : forall (x : R), mul x one = x; (* right_id one mul *)
          ax4 : forall (x y : R) (z : R),
              mul (add x y) z = add (mul x z) (mul y z); (* left_distributive mul +%R *)
          ax5 : forall (x : R) (y z : R),
              mul x (add y z) = add (mul x y) (mul x z); (* right_distributive mul +%R *)
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
  
(* End GRing. *)

(** ****** *)
(** sample *)
(** ****** *)

Require Import Bool.

(** eqType *)
Fail Check true == true.
Fail Check true != false.

(* Bool のなかにも、reflect があるため。 *)
Lemma eqb_spec : forall b1 b2, Top.reflect (b1 = b2) (eqb b1 b2).
Proof.
  intros b1 b2.
  destruct b1, b2; now constructor.
Qed.

Definition bool_eqMixin := EqMixin eqb_spec.
Canonical Structure bool_eqType := EqType bool_eqMixin.

Check bool_eqType : eqType.
Check true == true.
Check true != false.

(** choiceType *)

Definition choose (P : pred bool) (n : nat) :=
  match n with
  | 0 => Some false
  | 1 => Some true
  | _ => None
  end.

Lemma chooseP (P : pred bool) n x : choose P n = Some x -> P x.
Proof.
  intro H.
Admitted.
  
Lemma choose_id (P : pred bool) :
  (exists x, P x) -> exists n, choose P n. (* isSome *)
Proof.
Admitted.
  
Lemma eq_choose P Q : P =1 Q -> choose P =1 choose Q.
Proof.
  easy.
Qed.  

Definition bool_choiceMixin := ChoiceMixin chooseP choose_id eq_choose.
Canonical Structure bool_choiceClass := ChoiceClass bool_eqMixin bool_choiceMixin.
Canonical Structure bool_choiceType := ChoiceType bool_choiceClass.

Check bool_choiceType : choiceType.

(** countType *)

Definition bool_pickle : bool -> nat := nat_of_bool.

Definition bool_unpickle : nat -> option bool :=
  fun n => match n with
           | 0 => Some false
           | 1 => Some true
           | _ => None
           end.

Lemma bool_pickleK : pcancel bool_pickle bool_unpickle.
Proof.
  intros b.
  now destruct b.
Qed.  

Definition bool_countMixin := CountMixin bool_pickleK.
Canonical Structure bool_countClass := CountClass bool_choiceClass bool_countMixin.
Canonical Structure bool_countType := CountType bool_countClass.

Check bool_countType : countType.

(** finType *)

Definition bool_fin_enum := false :: true :: nil.

Lemma bool_fin_ax (x : bool) : (Finite.count_mem x) bool_fin_enum = 1.
Proof.
  unfold Finite.count_mem, bool_fin_enum.
  now destruct x.
Qed.

Definition bool_finMixin := FinMixin bool_countMixin bool_fin_ax.
Canonical Structure bool_finClass := FinClass bool_countClass bool_finMixin.
Canonical Structure bool_finType := FinType bool_finClass.

Check bool_finType : finType.

(** Zmodule *)
(** Ring *)

(* END *)
