Section product_formation.

(* Prop, Set, Type 自体は、Type の型を持つ。 *)
Fail Check Prop : Prop.
Fail Check Set : Prop.
Fail Check Type : Prop.

Fail Check Prop : Set.
Fail Check Set : Set.
Fail Check Type : Set.

Check Prop : Type.
Check Set : Type.
Check Type : Type.
Set Printing Universes.
Check Prop : Type.                          (* Top.43 *)
Check Set : Type.                           (* Top.44 *)
Check Type : Type.                          (* Top.45 *)
Unset Printing Universes.

(* rule Prop-Prop *)
Fail Check Prop -> Prop : Prop.
Fail Check Prop -> Prop : Set.
Check Prop -> Prop : Type.
(* rule Set-Prop *)
Fail Check Set -> Prop : Prop.
Fail Check Set -> Prop : Set.
Check Set -> Prop : Type.
(* rule Type-Prop *)
Fail Check Type -> Prop : Prop.
Fail Check Type -> Prop : Set.
Check Type -> Prop : Type.

(* rule Prop-Set *)
Fail Check Prop -> Set : Prop.
Fail Check Prop -> Set : Set.
Check Prop -> Set : Type.
(* rule Set-Set *)
Fail Check Set -> Set : Prop.
Fail Check Set -> Set : Set.
Check Set -> Set : Type.
(* rule Type-Set *)
Fail Check Type -> Set : Prop.
Fail Check Type -> Set : Set.
Check Type -> Set : Type.

(* rule Prop-Type *)
Fail Check Prop -> Type : Prop.
Fail Check Prop -> Type : Set.
Check Prop -> Type : Type.
(* rule Set-Type *)
Fail Check Set -> Type : Prop.
Fail Check Set -> Type : Set.
Check Set -> Type : Type.
(* rule Type-Type *)
Fail Check Type -> Type : Prop.
Fail Check Type -> Type : Set.
Check Type -> Type : Type.


(* Prop, Set, Type の要素の関係 *)
(* Prop <= Set <= Type *)
Variable P0 : Prop.
Variable S0 : Set.
Variable T0 : Type.

Check P0 : Prop.
Check P0 : Set.
Check P0 : Type.

Fail Check S0 : Prop.
Check S0 : Set.
Check S0 : Type.

Fail Check T0 : Prop.
Fail Check T0 : Set.
Check T0 : Type.

Variables P1 : Prop.
(* rule Prop-Prop *)
Check P0 -> P1 : Prop.
Check P0 -> P1 : Set.
Check P0 -> P1 : Type.
(* rule Set-Prop *)
Check S0 -> P1 : Prop.
Check S0 -> P1 : Set.
Check S0 -> P1 : Type.
(* rule Type-Prop *)
Check T0 -> P1 : Prop.
Check T0 -> P1 : Set.
Check T0 -> P1 : Type.

Variables S1 : Set.
(* rule Prop-Set *)
Fail Check P0 -> S1 : Prop.
Check P0 -> S1 : Set.
Check P0 -> S1 : Type.
(* rule Set-Set *)
Fail Check S0 -> S1 : Prop.
Check S0 -> S1 : Set.
Check S0 -> S1 : Type.
(* rule Type-Set *)
Fail Check T0 -> S1 : Prop.
Fail Check T0 -> S1 : Set.
Check T0 -> S1 : Type.

Variables T1 : Type.
(* rule Prop-Type *)
Fail Check P0 -> T1 : Prop.
Fail Check P0 -> T1 : Set.
Check P0 -> T1 : Type.
(* rule Set-Type *)
Fail Check S0 -> T1 : Prop.
Fail Check S0 -> T1 : Set.
Check S0 -> T1 : Type.
(* rule Type-Type *)
Fail Check T0 -> T1 : Prop.
Fail Check T0 -> T1 : Set.
Check T0 -> T1 : Type.

(* nat は、S0 と同じ。 *)
Fail Check (nat -> nat) : Prop.
Check (nat -> nat) : Set.
Check (nat -> nat) : Type.

(* forall A : Prop なるAは、P0 の場合と同じ。 *)
(* forall A : Set なるAは、S0 の場合と同じ。 *)
(* forall A : Type なるAは、T0 の場合と同じ。 *)
Check (forall A : Prop, A -> A) : Prop.
Check (forall A : Prop, A -> A) : Set.
Check (forall A : Prop, A -> A) : Type.
Fail Check (forall A : Set, A -> A) : Prop.
Fail Check (forall A : Set, A -> A) : Set.
Check (forall A : Set, A -> A) : Type.
Fail Check (forall A : Type, A -> A) : Prop.
Fail Check (forall A : Type, A -> A) : Set.
Check (forall A : Type, A -> A) : Type.

(* ふつうにPropであるもの。 *)
Check (forall x : nat, 0 <= x) : Prop.
Check (forall x : nat, x = x)  : Prop.
Check (forall A : Prop, A -> A) : Prop.
Check (forall P : nat -> Prop, P O -> exists n : nat , P n) : Prop.

(* これより複雑なものは、Typeの型を持つ。 *)
Check (nat -> Prop) : Type.
Check ((Prop -> Prop) -> Prop) : Type.
Check (forall P : nat -> Prop, Prop) : Type.

End product_formation.

(* まとめ *)
(* Propであるものは、Propである。 *)

(* Propであるものは、Setである。 *)
(* 依存型で、以下のものはSetである。 *)
Variable A : Set.                           (* A : Propでもよい。 *)
Variable B : Set.
Check (forall x : A, B) : Set.              (* (Set,Set)のProd は集合 *)
Check A -> B : Set.
Fail Check (forall a : Set, a) : Set.       (* 型 *)
Fail Check (forall a : Set, a -> A) : Set.  (* (Type,Set)のProd は型 *)

(* これ以外のものは、Type である *)

(* 以上 *)

