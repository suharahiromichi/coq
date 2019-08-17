(**
Coq/SSReflect/MathComp による定理証明

3.15 コマンド Record, Canonical
======
2018_04_22 @suharahiromichi
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
Record magma : Type :=
  Magma {
      carrier : Type;
      operator : carrier -> carrier -> carrier
    }.

Check magma : Type.
Check Magma : forall carrier : Type, (carrier -> carrier -> carrier) -> magma.

(** Magma [(Prop, /\)] *)
Definition prop_and_magma := @Magma Prop and.
Canonical prop_and_magma.
Print Canonical Projections.                (* カノニカルの表示 *)
(** [Prop <- carrier ( prop_and_magma )] *)

Print prop_and_magma.
(** [{| carrier := Prop; operator := and |} : magma] *)
Compute carrier prop_and_magma.             (* Prop *)
Compute @operator prop_and_magma.           (* and *)

Lemma PropMagmaFalse (x y : carrier prop_and_magma) :
  @operator prop_and_magma x False -> y.
Proof.
  rewrite /=; by case.
Qed.

(** Magma [(nat, +)] *)
Definition nat_plus_magma := @Magma nat plus.
Canonical nat_plus_magma.
Print Canonical Projections.                (* カノニカルの表示 *)
(** [nat <- carrier ( nat_plus_magma )]  *)

Print nat_plus_magma.
(** [{| carrier := nat; operator := Init.Nat.add |} : magma] *)
Compute carrier nat_plus_magma.             (* nat *)
Compute @operator nat_plus_magma.           (* plus *)

Lemma NatMagmaPlus (x y : carrier nat_plus_magma) :
  @operator nat_plus_magma x y = x + y.
Proof.
  rewrite /=; by [].
Qed.

(**
## 例2: 代数構造の階層、半群の例
*)
Record semigroup : Type :=
  Semigroup {
      scarrier : magma;
      assoc : forall a b c : carrier scarrier,
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

Check addnA : associative addn.
Check addnA 1 2 3 : 1 + (2 + 3) = 1 + 2 + 3.

Definition nat_plus_semigroup := @Semigroup nat_plus_magma addnA.
Canonical nat_plus_semigroup.
Print Canonical Projections.                (* カノニカルの表示 *)
(** [nat_plus_magma <- scarrier ( nat_plus_semigroup )] *)

Print nat_plus_semigroup.
(** [{| scarrier := nat_plus_magma; assoc := addnA |}] *)

(**
# 3.15.2 コマンド Canonical
*)

Notation "a ^^ b" := (@operator _ a b) (at level 30, right associativity).
(** 次でも同じ： *)
(** [Notation "a ^^ b" := (operator a b) (at level 30, right associativity).] *)

(** [Canonical nat_plus_magma]  がなくても良い例  *)
(** [Canonical nat_plus_semigroup] がなくても良い例  *)
Section TEST1.
  Variable a b : carrier nat_plus_magma.
  
  Check @operator nat_plus_magma :
    carrier nat_plus_magma -> carrier nat_plus_magma -> carrier nat_plus_magma.
  
  Check @operator nat_plus_magma a b.
  
  Check a ^^ b.
  
  Lemma natPlusExample1 (x y z : carrier nat_plus_magma) :
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
  Compute carrier nat_plus_magma.           (* nat *)
  Check @operator nat_plus_magma : nat -> nat -> nat.
  
  Check @operator nat_plus_magma a b.
  
  Check a ^^ b.
  
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

(**
既存の [^] の定義により、Propに対する演算ができない（？）ので、
全体に対して [^^] を使うようにした。
 *)

(** [Canonical prop_and_magma]  がなくても良い例  *)
Lemma PropMagmaFalse1 (x y : carrier prop_and_magma) :
  x ^^ False -> y.
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