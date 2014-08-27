(**
An introduction to small scale reflection in Coq

6.1.4 Example: a depth rst search algorithm

http://hal.inria.fr/docs/00/55/53/79/PDF/main-rr.pdf
*)

Require Import ssreflect ssrfun ssrbool eqtype ssrnat div seq.
Require Import path choice fintype tuple finfun finset.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Variables (T : finType) (e : T -> seq T).

Definition grel := [rel x y | y \in e x].
Check grel : rel T.                         (* simpl_rel T := rel T *)
Check [rel x y : T | y \in e x] : rel T.
Check [rel x y : nat | y \in [:: x]] : rel nat.
Check (fun x y : nat => y \in [:: x]) : rel nat.

(* 参考 *)
Check [pred n : nat | n == 0] : pred nat.
Check (fun n : nat => n == 0) : pred nat.

Fixpoint dfs (n : nat) (a : seq T) (x : T) {struct n} :=
  if n is n'.+1 then
    if x \in a then a else foldl (dfs n') (x :: a) (e x)
  else a.


(* END *)
