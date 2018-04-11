(** 対角線論法の証明 *)

From mathcomp Require Import all_ssreflect.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Axiom Excluded_Middle : forall (P : Prop), P \/ ~P. (* 排中律 *)
Axiom Absurd : forall (P : Prop), ~ P /\ P -> False.

Section DIAG.
  Variable φ : nat -> nat -> bool.         (* 自己参照1 *)
  
  Definition diag (n : nat) : bool := ~~ φ n n. (* 対角線関数 *)
  
  Goal exists (g : nat -> bool),
      forall (n : nat), φ n <> g. (* 自己参照2 *)
  Proof.
    exists diag.
    move=> n Hc.
    case: (Excluded_Middle (φ n n = diag n)).
    (* φ n n = diag n -> False *)
    (* diag をその定義で展開する。 *)
    - rewrite /diag => H1.
      by case H2 : (φ n n); rewrite H2 in H1.
    (* φ n n <> diag n -> False *)
    (* diag をHcで展開する。 *)
    - by rewrite Hc.
  Qed.
  
  Goal exists (g : nat -> bool),
      forall (n : nat), φ n <> g. (* 自己参照2 *)
  Proof.
    exists diag.
    move=> n Hc.
    apply: (@Absurd (φ n n = diag n)).
    split.
    - rewrite /diag => H1.
      by case H2 : (φ n n); rewrite H2 in H1.
    - by rewrite Hc.
  Qed.
  
  (* refine ((_ : φ n n <> diag n) (_ : φ n n = diag n)). *)
  (* absurd (F n n = diag F n). *)
End DIAG.

(* END *)
