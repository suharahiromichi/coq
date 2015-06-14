(**
プログラミング Coq --- 停止性が明らかでない関数を定義するには

http://www.iij-ii.co.jp/lab/techdoc/coqt/coqt7.html
をSSReflectに書き直した。
*)

Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq.
Require Import Recdef.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Set Print All.

Fixpoint merge (l1 l2 : seq nat) :=
  (fix merge' l' :=
    match l1, l' with
    | nil, _ => l'
    | _, nil => l1
    | x::xs, y::ys => if x <= y then x :: merge xs l' else y :: merge' ys
    end
  ) l2.

Fixpoint split (l : seq nat) : seq nat * seq nat :=
  match l with
  | nil => (nil, nil)
  | x::nil => (x :: nil, nil)
  | x::y::zs => (fun l' => (x :: fst l', y :: snd l')) (split zs)
  end.
(*
Function msort (l : seq nat) {measure length l} : seq nat :=
  match l with
  | nil => nil
  | x::nil => x::nil
  | x::y::zs => (fun l' => merge (msort (fst l')) (msort (snd l'))) (split l)
  end.
Proof.
 (* length (snd (split (x::y::zs))) < length (x::y::zs) *)
 intros.
 simpl.
 subst.
 induction (split zs).
  simpl.
  constructor.
 
  simpl.
  constructor.
  admit.
 
  simpl.
  intros.
  apply lt_S.
  apply lt_n_S.
  apply IHp.

 (* length (fst (split (x::y::zs))) < length (x::y::zs) *)
 intros.
 subst.
 functional induction (split zs).
  simpl.
  constructor.

  simpl.
  constructor.

  simpl.
  apply lt_n_S.
  apply lt_S.
  apply IHp.
Defined.
*)

(* 問10. *)
Goal forall (n m : nat), n = m \/ n <> m.
Proof.
  elim=> [m | n IHn m].                     (* elim: n *)
  - by elim: m; [left | right].             (* elim: m *)
  - elim: m => [| m _].
    + by right.
    + elim: (IHn m) => H; [left | right].
      * by f_equal.
      * by apply not_eq_S.
Qed.

(* 問11. *)
Goal forall (P Q : nat -> Prop),
       (forall n, P n -> Q n) -> ((forall n, P n) -> (forall n, Q n)).
Proof.
  move=> P Q H H0 n.
  by apply/H/H0.
Qed.

(* END *)
