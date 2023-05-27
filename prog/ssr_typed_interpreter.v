(**
   型付インタープリタ
   
   https://www.math.nagoya-u.ac.jp/~garrigue/lecture/2011_AW/coq7.pdf
 *)

From mathcomp Require Import all_ssreflect.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Inductive exp : Type -> Type :=
| Nat : nat -> exp nat
| Pair : forall t1 t2, exp t1 -> exp t2 -> exp (t1 * t2)
| App : forall t1 t2, exp (t1 -> t2) -> exp t1 -> exp t2
| Plus : exp (nat -> nat -> nat).

Fixpoint eval (t : Type) (e : exp t) : t :=
  match e with
  | Nat n => n
  | Pair t1 t2 a b => (eval a, eval b) (* (@eval t1 a, @eval t2 b) *)
  | App t1 t2 f g => (eval f) (eval g) (* (@eval (t1 -> t2) f) (@eval t1 g) *)
  | Plus => addn
  end.

Compute eval (App (App Plus (Nat 1)) (Nat 2)). (* 3 *)

Inductive evaluate : forall {t : Type}, exp t -> t -> Prop :=
| e_nat n : evaluate (Nat n) n
| e_pair t1 t2 (a : exp t1) (b : exp t2) (a' : t1) (b' : t2) :
    evaluate a a' -> evaluate b b' -> evaluate (Pair a b) (a' , b')
| e_app t1 t2 (f : exp (t1 -> t2)) (g : exp t1) (f' : t1 -> t2) (g' : t1) :
    evaluate f f' -> evaluate g g' -> evaluate (App f g) (f' g')
| e_plus : evaluate Plus plus.

#[global]
Hint Constructors evaluate.

Goal evaluate (App (App Plus (Nat 1)) (Nat 2)) (plus 1 2).
Proof.
  apply: e_app.
  - by apply: e_app.
  - done.
Qed.

Lemma eval_eval (t : Type) (e : exp t) (v : t) : evaluate e v <-> eval e = v.
Proof.
  split.
  - elim=> //=.
    + move=> t1 t2 a b a' b' H1 H2 H3 H4.
      by subst.
    + move=> t1 t2 a b a' b' H1 H2 H3 H4.
      by subst.
  - elim: e v => [n v H | t1 t2 e1 H1 e2 H2 v IH | t1 t2 f Hf g Hg v IH | v H];
                   subst => //=.
    + apply: e_pair.
      * by apply: H1.
      * by apply: H2.
    + apply: e_app.
      * by apply: Hf.
      * by apply: Hg.
Qed.

Require Import Program.
Program Fixpoint eval' (t : Type) (e : exp t) : {v | evaluate e v} :=
  match e with
  | Nat n => n
  | Pair t1 t2 a b => (eval' a, eval' b)
  | App t1 t2 f g => (eval' f) (eval' g)
  | Plus => addn
  end.
(* 証明責務はなし。 *)

Compute (eval (App (App Plus (Nat 1)) (Nat 2))).
Compute (eval' (App (App Plus (Nat 1)) (Nat 2))).

(** END **)
