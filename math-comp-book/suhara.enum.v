(* 4.1 enum: 値の列挙 に関連して *)

From mathcomp Require Import all_ssreflect.

(* mem_pred の引数は T ではないようだ。 *)
Definition enum_mem' T (mA : mem_pred _) := filter mA (Finite.EnumDef.enum T).

(*
Definition enum' A := (enum_mem' _ (mem A)).
これはエラーになる。「_」に A を書いてはいけない。
 *)
Notation enum' A := (enum_mem' _ (mem A)).

Check enum_mem' : forall T : finType, mem_pred T -> seq T.
(*
Check enum' : forall A : finType, seq A.
*)

Compute enum bool_finType.
Compute enum (ordinal_finType 3).

Check (enum_mem (mem [:: false])).
Check enum [:: false].

Compute enum' bool_finType.
Compute enum' (ordinal_finType 3).

Check (enum_mem' _ (mem [:: false])).
Check enum' [:: false].

(* END *)

(* #|T| = size (enum T) *)
Lemma cardT : forall A : finType, card (mem A) = size (enum A).
Proof.
  move=> A.
  by rewrite cardE.
Qed.

Check @inord 4 3 : 'I_5.
Check inord 3 : 'I_5.

(* ord_enum の定義について *)
Definition ord_enum (n : nat) : seq 'I_n := pmap insub (iota 0 n).
Check ord_enum 5.

Check @insub : forall (T : Type) (P : pred T) (sT : subType (T:=T) P), T -> option sT.
Check (fun i => i < 3) : pred nat.

Definition test (n : nat) : option 'I_n :=
  @insub nat (fun i => i < n) (ordinal_subType n) n.
Definition test' (n : nat) : option 'I_n := insub n.

Print test.
Check test 3. (* option 'I_3. *)

(* END *)
