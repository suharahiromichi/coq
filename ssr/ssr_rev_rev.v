From mathcomp Require Import all_ssreflect.
From mathcomp Require Import ssralg.
Require Import ZArith.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Set Print All.

(** # 二種類のreverseの定義 *)

Section Rev.
  
  Variable T : Type.                        (* 任意のT型のデータについて、 *)

  (** ## rcons を使った定義 *)

  Definition rcons l (a : T) := l ++ [:: a].

  Fixpoint rev1 (l : seq T) : seq T :=
    match l with
    | nil    => nil
    | h :: t => rcons (rev1 t) h
    end.
  
  (** ## 末尾再帰を使った定義 *)
  
  Fixpoint rev2s (l m : seq T) : seq T :=
    match l with
    | [::] => m
    | x :: l => rev2s l (x :: m)
    end.
  
  Definition rev2 (l : seq T) : seq T := rev2s l [::].
  
  (** ## rev2 に関する補題を証明する。  *)
  
  Lemma l_rev2_cat_r (l m n : seq T) : rev2s l m ++ n = rev2s l (m ++ n).
  Proof.
    elim: l m => [| x l IH m] /=.
    + done.
    + rewrite -[x :: m ++ n]cat_cons.
        by rewrite (IH (x :: m)).
  Qed.
  
  Lemma l_rev2_cat_l (s t u : seq T) : rev2s (s ++ t) u = rev2s t [::] ++ rev2s s u.
  Proof.
    elim: s u => [u | a l IH u] /=.
    - by rewrite l_rev2_cat_r.
    - by rewrite IH.
  Qed.
  
  (** ## ふたつの定義が同じであることの証明 *)
  
  Theorem rev1_rev2 (l : seq T) : rev1 l = rev2 l.
  Proof.
    rewrite /rev2.
    elim: l.
    - done.
    - move=> a l IH /=.
      rewrite IH /rcons /=.
        by rewrite l_rev2_cat_r.
  Qed.
  
  (** ## rev1 が対合であることを証明する。 *)
  
  Lemma snoc_rev1 : forall n l,
      rev1 (rcons l n) = n :: (rev1 l).
  Proof.
    move=> n l.
    elim: l => [|m l IHl] /=.
    - done.
    - by rewrite IHl.
  Qed.
  
  Theorem rev1_involutive (l : seq T) : rev1 (rev1 l) = l.
  Proof.
    elim: l => [| n l IHl] /=.
    - done.
    - rewrite snoc_rev1.
        by rewrite IHl.
  Qed.
  
  (** ## rev2 が対合であることを証明する。rev1を経由する。 *)
  
  Lemma rev2_rev2 (l : seq T) : rev2 (rev2 l) = l.
  Proof.
    rewrite -rev1_rev2.
    rewrite -rev1_rev2.
      by apply rev1_involutive.
  Qed.
  
  (** ## rev2 が対合であることを証明する。直接証明する。 *)

  Lemma rev2_rev2' (l : seq T) : rev2 (rev2 l) = l.
  Proof.
    rewrite /rev2.
    elim: l => [| a l IH] /=.
    - done.
    - Check l_rev2_cat_r l [::] [:: a].
      rewrite -(l_rev2_cat_r l [::] [:: a]).
      Check l_rev2_cat_l (rev2s l [::]) [::a] [::].
      rewrite (l_rev2_cat_l (rev2s l [::]) [::a] [::]).
        by rewrite IH /=.
  Qed.
  
End Rev.

(* END *)
