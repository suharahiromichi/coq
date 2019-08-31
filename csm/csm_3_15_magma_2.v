(**
Coq/SSReflect/MathComp による定理証明

3.15 コマンド Record, Canonical
======
2018_04_22 @suharahiromichi
2018_08_31 @suharahiromichi、コアーション coercion (:>)
 *)

(**
補足説明：
テキストはCanonical宣言の説明だが、MathCompとしてはCoercionを併用して、
- prop_and_magma が 型クラスmagma の型インスタンスであること。
- nat_plus_magma が 型クラスmagma の型インスタンスであること。
- prop_and_magma が Prop のカノニカル解、であること。
- nat_plus_magma が nat のカノニカル解、であること。
まで説明してはどうだろうか。
*)

From mathcomp Require Import all_ssreflect.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Set Print All.

(**
# 3.15.1 コマンド Record - Magma マグマ の定義
*)

(**
## 例1: 集合Mと、M上の二項演算*の組 [(M, * )] Magma の形式化
*)
Record magma : Type :=                      (* 型クラス *)
  Magma {
      carrier :> Type;                      (* コアーション *)
      operator : carrier -> carrier -> carrier
    }.

Check magma : Type.
Check Magma : forall carrier : Type, (carrier -> carrier -> carrier) -> magma.

(** ****************** *)
(** Magma [(Prop, /\)] *)
(** ****************** *)
Check and.                             (* Prop -> Prop -> Prop *)
Definition prop_and_magma := @Magma Prop and. (* 型インスタンス *)

Print Graph.                     (* [carrier] : magma >-> Sortclass *)
Check carrier prop_and_magma : Type.
Check         prop_and_magma : magma.
Check         prop_and_magma : Type.        (* コアーション *)

Print prop_and_magma.
(** [{| carrier := Prop; operator := and |} : magma] *)
Compute carrier prop_and_magma.      (* 台 Prop を取り出す。 *)
Compute @operator prop_and_magma.    (* オペレータ and を取り出す。 *)

Lemma PropMagmaFalse (x y : prop_and_magma) : (* コアーション *)
  operator x False -> y.
Proof.
  rewrite /=; by case.
Qed.

Lemma PropMagmaFalse'' (x y : prop_and_magma) : (* コアーション *)
  @operator prop_and_magma x False -> y.
Proof.
  rewrite /=; by case.
Qed.

(** 同じことを Magma を使わずに定義する。 *)
Lemma PropFalse (x y : Prop) : and x False -> y.
Proof.
    by case.
Qed.

(** **************** *)
(** Magma [(nat, +)] *)
(** **************** *)
Definition nat_plus_magma := @Magma nat plus. (* 型インスタンス *)

Print Graph.                     (* [carrier] : magma >-> Sortclass *)
Check carrier nat_plus_magma : Type.
Check         nat_plus_magma : magma.
Check         nat_plus_magma : Type.        (* コアーション *)

Print nat_plus_magma.
(** [{| carrier := nat; operator := Init.Nat.add |} : magma] *)
Compute carrier nat_plus_magma.     (* 台 nat を取り出す。 *)
Compute @operator nat_plus_magma.   (* オペレータ plus を取り出す。 *)

Lemma NatMagmaPlus (x y : nat_plus_magma) : (* コアーション *)
  operator x y = x + y.
Proof.
  rewrite /=; by [].
Qed.

Lemma NatMagmaPlus'' (x y : nat_plus_magma) : (* コアーション *)
  @operator nat_plus_magma x y = x + y.
Proof.
  rewrite /=; by [].
Qed.

(** 同じことを Magma を使わずに定義する。 *)
Lemma NatPlus (x y : nat) :
  plus x y = x + y.
Proof.
  done.
Qed.

(**
## 例2: 代数構造の階層、半群の例
*)
Record semigroup : Type :=                  (* 型クラス *)
  Semigroup {
      scarrier :> magma;                    (* コアーション *)
      assoc : forall a b c : scarrier,      (* carrier scarrier *)
          operator a (operator b c)
          = operator (operator a b) c
    }.
(**
carrier の型引数が省略されている。
[[
      assoc : forall a b c : carrier scarrier,
          @operator scarrier a (@operator scarrier b c)
          = @operator scarrier (@operator scarrier a b) c
]]
*)

(** *************** *)
(** 半群 [(nat, +)] *)
(** *************** *)
Check addnA : associative addn.
Check addnA 1 2 3 : 1 + (2 + 3) = 1 + 2 + 3.

Definition nat_plus_semigroup := @Semigroup nat_plus_magma addnA. (* 型インスタンス *)

Print Graph.
(* [carrier] : magma >-> Sortclass *)
Check carrier (scarrier nat_plus_semigroup) : Type.
Check          scarrier nat_plus_semigroup  : magma.
Check          scarrier nat_plus_semigroup  : Type.   (* コアーション *)

(* [scarrier] : semigroup >-> magma *)
Check scarrier nat_plus_semigroup : magma.
Check          nat_plus_semigroup : semigroup.
Check          nat_plus_semigroup : magma.  (* コアーション *)

(* [scarrier; carrier] : semigroup >-> Sortclass *)
Check carrier (scarrier nat_plus_semigroup) : Type.
Check                   nat_plus_semigroup  : semigroup.
Check                   nat_plus_semigroup  : Type.   (* コアーション *)

Print nat_plus_semigroup.
(** [{| scarrier := nat_plus_magma; assoc := addnA |}] *)

(**
# 3.15.2 コマンド Canonical
*)

Canonical nat_plus_magma.
Print Canonical Projections.                (* カノニカルの表示 *)
(** [nat <- carrier ( nat_plus_magma )]  *)

Lemma NatMagmaPlus' (x y : nat) :
  operator x y = x + y.
Proof.
  rewrite /=; by [].
Qed.

(* ********* *)

Canonical nat_plus_semigroup.
Print Canonical Projections.                (* カノニカルの表示 *)
(** [nat_plus_magma <- scarrier ( nat_plus_semigroup )] *)

Notation "a ^^ b" := (@operator _ a b) (at level 30, right associativity).
(** 次でも同じ： *)
(** [Notation "a ^^ b" := (operator a b) (at level 30, right associativity).] *)

(** [Canonical nat_plus_magma]  がなくても良い例  *)
(** [Canonical nat_plus_semigroup] がなくても良い例  *)
Section TEST1.
  Variable a b : nat_plus_magma.            (* carrier nat_plus_magma *)
  
  Check @operator nat_plus_magma :
    carrier nat_plus_magma -> carrier nat_plus_magma -> carrier nat_plus_magma.
  Check @operator nat_plus_magma :
    nat_plus_magma -> nat_plus_magma -> nat_plus_magma.
  Check @operator nat_plus_magma a b : carrier nat_plus_magma.
  Check @operator nat_plus_magma a b : nat_plus_magma.
  Check a ^^ b : carrier nat_plus_magma.
  Check a ^^ b : nat_plus_magma.
  
  Lemma natPlusExample1 (x y z : nat_plus_magma) : (* carrier nat_plus_magma *)
    x ^^ (y ^^ z) = (x ^^ y) ^^ z.
  Proof.
      by rewrite (@assoc nat_plus_semigroup).
  Qed.
End TEST1.


(** [Canonical nat_plus_magma] は必要。 *)
(** [Canonical nat_plus_semigroup] がなくても良い例  *)
Section TEST2.
  Variable a b : nat.
  
  Check @operator nat_plus_magma :
    carrier nat_plus_magma -> carrier nat_plus_magma -> carrier nat_plus_magma.
  Check @operator nat_plus_magma :
    nat_plus_magma -> nat_plus_magma -> nat_plus_magma.
  Compute carrier nat_plus_magma.           (* nat *)
  Check @operator nat_plus_magma : nat -> nat -> nat.
  Check @operator nat_plus_magma a b : carrier nat_plus_magma.
  Check @operator nat_plus_magma a b : nat_plus_magma.
  
  Check operator a b : carrier nat_plus_magma. (* canonical 宣言が必要 *)
  Check operator a b : nat_plus_magma. (* canonical 宣言が必要 *)
  Check a ^^ b  : carrier nat_plus_magma.
  Check a ^^ b  : nat_plus_magma.

  Check @operator nat_plus_magma a b : nat.
  Check operator a b : nat.
  Check a ^^ b  : nat.
  
  Lemma natPlusExample2 (x y z : nat) :
    x ^^ (y ^^ z) = (x ^^ y) ^^ z.
  Proof.
      by rewrite (@assoc nat_plus_semigroup).
  Qed.
End TEST2.

(** [Canonical nat_plus_magma] は必要。 *)
(** [Canonical nat_plus_semigroup]  は必要。 *)
Lemma natPlusExample3 (x y z : nat) :
  x ^^ (y ^^ z) = (x ^^ y) ^^ z.
Proof.
    by rewrite assoc.
Qed.

(**
# 補足
*)

(** ****************** *)
(** Magma [(Prop, /\)] *)
(** ****************** *)

(**
既存の [^] の定義により、Propに対する演算ができない（？）ので、
全体に対して [^^] を使うようにした。
 *)

(** [Canonical prop_and_magma] がなくても良い例  *)
Lemma PropMagmaFalse1 (x y : prop_and_magma) : (* コアーション *)
  x ^^ False -> y.
Proof.
  rewrite /=; by case.
Qed.

(* ********* *)
(* ********* *)

Canonical prop_and_magma.
Print Canonical Projections.                (* カノニカルの表示 *)
(** [Prop <- carrier ( prop_and_magma )] *)

Lemma PropMagmaFalse2' (x y : Prop) :
  operator x False -> y.
Proof.
  rewrite /=; by case.
Qed.

(** [Canonical prop_and_magma] が必要 *)
Lemma PropMagmaFalse2 (x y : Prop) :
  x ^^ False -> y.
Proof.
  rewrite /=; by case.
Qed.

(** END *)
