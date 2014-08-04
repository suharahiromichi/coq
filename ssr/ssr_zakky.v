(* mzpさんの真偽値のみの言語における決定性の証明コード(Coq) *)
(* TAPL Nagoya 2014 #1 *)
Require Import ssreflect ssrfun ssrbool eqtype ssrnat.

Inductive Term : Set :=
 | T
 | F
 | TIf (_ : Term) (_ : Term) (_ : Term).
 
Inductive Step : Term -> Term -> Prop :=
 | EIfTrue  : forall (t1 t2 : Term), Step (TIf T t1 t2) t1
 | EIfFalse : forall (t1 t2 : Term), Step (TIf F t1 t2) t2
 | EIf      : forall (t1 t1' t2 t3 : Term),
                Step t1 t1' -> Step (TIf t1 t2 t3) (TIf t1' t2 t3).
 
(* by mzp *)
Lemma dec: forall (t t' t'' : Term),
  Step t t' -> Step t t'' -> t' = t''.
Proof.
  Check Step_ind.
  intros t t' t'' Q.
 
  generalize t''.
  apply Step_ind with (t:=t) (t0:=t'); intros; auto.
    inversion H; auto.
    subst.
    inversion H4.
 
    inversion H; auto.
    inversion H4.
 
    destruct t1.
      inversion H.
      inversion H.
 
      inversion H1.
      apply H0 in H6.
      rewrite H6.
      reflexivity.
Qed.

Lemma dec' : forall (t t' t'' : Term),
  Step t t' -> Step t t'' -> t' = t''.
Proof.
  move=> t t' t'' Q.
  elim: Q t''.
  - move=> t1 t2 t'' H.
    inversion H.
    + by [].
    + by inversion H4.
  - move=> t1 t2 t'' H.
    inversion H.
    + by [].
    + by inversion H4.
  - move=> t1 t1' t2 t3 H H1 t'' H2.
    destruct t1.                            (* XXX *)
    + inversion H.
    + inversion H.
    + inversion H2.
      by rewrite (H1 t1'0).
Qed.

(* END *)
