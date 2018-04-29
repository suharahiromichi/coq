From mathcomp Require Import all_ssreflect.
From mathcomp Require Import ssralg.
Require Import ZArith.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Set Print All.

Section Rev.
  
  Variable T : Type.                        (* 任意のT型のデータについて、 *)

  (** # 二種類のreverseの定義 *)
  
  (** ## rcons を使った定義 *)

  Definition rcons l (a : T) := l ++ [:: a].

  Fixpoint rev1 (l : seq T) : seq T :=
    match l with
    | nil    => nil
    | h :: t => rcons (rev1 t) h
    end.
  
  (** ### rev1 に関する補題を証明する。  *)
  
  Lemma snoc_rev1 (x : T) (l : seq T) : rev1 (rcons l x) = x :: (rev1 l).
  Proof.
    elim: l => [| x' l IHl] /=.
    - done.
    - by rewrite IHl.
  Qed.
  
  (** ## 末尾再帰を使った定義 *)
  
  Fixpoint catrev (l m : seq T) : seq T :=
    match l with
    | [::] => m
    | x :: l => catrev l (x :: m)
    end.
  
  Definition rev2 (l : seq T) : seq T := catrev l [::].
  
  (** ### rev2 に関する補題を証明する。  *)
  
  Lemma l_rev2_cat_r (l m n : seq T) : catrev l (m ++ n) = catrev l m ++ n.
  Proof.
    elim: l m => [| x l IHl m] /=.
    + done.
    + rewrite -[x :: m ++ n]cat_cons.
        by rewrite (IHl (x :: m)).
  Qed.
  
  Lemma l_rev2_cat_l (l m n : seq T) : catrev (l ++ m) n = catrev m [::] ++ catrev l n.
  Proof.
    elim: l n => [n | a l IHl n] /=.
    - by rewrite -l_rev2_cat_r.
    - by rewrite IHl.
  Qed.
  
  (** ## ふたつの定義が同じであることの証明 *)
  
  Theorem rev1_rev2 (l : seq T) : rev1 l = rev2 l.
  Proof.
    rewrite /rev2.
    elim: l.
    - done.
    - move=> a l IHl /=.
      rewrite IHl /rcons /=.
        by rewrite -l_rev2_cat_r.
  Qed.
  
  (** # 対合であることを証明する。 *)
  
  (** ## rev1 が対合であることを証明する。 *)
  
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
    elim: l => [| a l IHl] /=.
    - done.
    - Check l_rev2_cat_r l [::] [:: a].
      rewrite (l_rev2_cat_r l [::] [:: a]).
      Check l_rev2_cat_l (catrev l [::]) [::a] [::].
      rewrite (l_rev2_cat_l (catrev l [::]) [::a] [::]).
        by rewrite IHl /=.
  Qed.
  
End Rev.

(* END *)
