From mathcomp Require Import all_ssreflect.
From mathcomp Require Import all_classical.
Require Import Epsilon.                     (* epsilon_statement *)
Require Import FunctionalExtensionality.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section a.
  
  Check inhabited : Type -> Prop.
  Check inhabited_witness : forall T : Type, inhabited T -> T.

  (* 型Aの要素は存在する。 *)
  Variable A : Type.
  Variable H : inhabited A.

  (* 型Aの要素を取り出す。 *)
  Check inhabited_witness H : A.
End a.

(* 全く別なところで、定義されている。 *)
About inhabited.                            (* Coq.Init.Logic.inhabited *)
About inhabited_witness.                    (* mathcomp.classical.boolp.inhabited_witness *)

Print inhabited.
(*
Inductive inhabited (A : Type) : Prop :=
| inhabits : A -> inhabited A.
*)

Print inhabited_witness.                    (* ... *)

Section a1.
  
  Variable A : Type.
  Variable H : inhabited A.

  Definition default : A.
  Proof.
    by apply: inhabited_witness.
  Defined.

End a1.

(* 型Aに要素が存在するなら、その要素を返す。 *)
Check default : forall A : Type, inhabited A -> A.

Section b.

  Check inhabited : Type -> Prop.
  (* 公理として提供 *)
  (* 型Aに要素が存在するなら、弱い依存和として定義できる。 *)
  Check epsilon_statement
    : forall (A : Type) (P : A -> Prop), inhabited A -> {x : A | (exists x0 : A, P x0) -> P x}.
  
  (* 型Aの要素は存在する。 *)
  Variable A : Type.
  Variable H : inhabited A.

  (* 型Aの要素を取り出す。 *)
  Check epsilon_statement _ H : {x : A | (exists x0 : A, _ x0) -> _ x}.
  Check proj1_sig (epsilon_statement _ H) : A.
  
  Check epsilon_statement (fun=> true) H    (* 常に true を返す。 *)
    : {x : A | (exists x0 : A, (fun=> true) x0) -> (fun=> true) x}.
End b.

About epsilon_statement.     (* Coq.Logic.Epsilon.epsilon_statement *)

Section b2.
  
  Variable A : Type.
  Variable H : inhabited A.

  Definition default' : A.
  Proof.
    apply: epsilon => //=.
    Check xpredT : A -> Prop.
    by apply: xpredT.
  Qed.

End b2.

(* END *)
