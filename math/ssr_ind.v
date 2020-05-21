(**
*)

From mathcomp Require Import all_ssreflect.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(**
# 完全帰納法 Complete inStrong induction

Coq/SSReflectでたった1行のコマンドで完全帰納法を適用する方法

https://qiita.com/nekonibox/items/514da8edfc6107b57254
 *)

Goal forall P (n : nat), P n.
Proof.
  move=> P n.
  elim : n {-2}n (leqnn n).
  -
    (* forall n : nat, n <= 0 -> P n *)
    admit.
  -
    (* forall n : nat,
       (forall n0 : nat, n0 <= n -> P n0) -> forall n0 : nat, n0 <= n.+1 -> P n0 *)
    admit.

Admitted.

(* 使用例 *)

Variable (T:Type).
Variable (R:rel T).

Lemma qsort_ind (P:seq T -> Prop) :
  P [::] ->
  (forall x s, P [seq y <- s | R y x] ->
               P [seq y <- s | ~~ R y x] ->
               P (x :: s)) ->
  forall s, P s.
Proof.
  move => Hnil Hcons s.
  elim : s {-2}s (leqnn (size s)) =>[|xs s IHs][]//= xl l Hsize.
  (* by apply : Hcons; exact : IHs (leq_trans (filter_size _ _) Hsize). *)
Admitted.

Lemma qsort_ind' (P:seq T -> Prop) :
  P [::] ->
  (forall x s, P [seq y <- s | R y x] ->
               P [seq y <- s | ~~ R y x] ->
               P (x :: s)) ->
  forall s, P s.
Proof.
  move => Hnil Hcons s.
  elim : (size s) {-2}s (leqnn (size s)) =>[|n IHn][]//= xl l Hsize.
(* by apply : Hcons; exact : IHn (leq_trans (filter_size _ _) Hsize). *)
Admitted.


(**
# Custum Induction
*)

(**
## Funcutonal Scheme

http://www.a-k-r.org/d/2019-04.html#a2019_04_25_1
 *)

Require Import FunInd.

Fixpoint div2 (n:nat) : nat :=
match n with
| O => 0
| S O => 0
| S (S n') => S (div2 n')
end.

Goal forall m, div2 m <= m.
Proof.
  elim.
    by [].
  move=> n.
  (* div2 n <= n -> div2 n.+1 <= n.+1 *)
  simpl.
Abort.

(* 完全帰納法の例 *)
Goal forall m, div2 m <= m.
Proof.
  move=> m.
  pattern m.
  apply Wf_nat.lt_wf_ind => {m}.
  case; first by [].
  case; first by [].
  move=> n IH /=.
  apply ltnW.
  apply IH.
  by apply/ltP.
Qed.


Functional Scheme div2_ind := Induction for div2 Sort Prop.
(*
div2_equation is defined
div2_ind is defined
 *)
Check div2_ind
  : forall P : nat -> nat -> Prop,
    (forall n : nat, n = 0 -> P 0 0) ->
    (forall n n0 : nat, n = n0.+1 -> n0 = 0 -> P 1 0) ->
    (forall n n0 : nat,
        n = n0.+1 ->
        forall n' : nat, n0 = n'.+1 -> P n' (div2 n') -> P n'.+2 (div2 n').+1) ->
    forall n : nat, P n (div2 n).

Goal forall m, div2 m <= m.
Proof.
  move=> m.
  functional induction (div2 m).
    by [].
      by [].
        by apply ltnW.
Qed.

(**
## Funcutonal Scheme の発展形が Function である。

http://www.a-k-r.org/d/2019-05.html#a2019_05_03_1

https://people.irisa.fr/David.Pichardie/papers/flops06.pdf
*)

Function div2'' (n:nat) : nat :=
match n with
| O => 0
| S O => 0
| S (S n') => S (div2'' n')
end.
Check div2''_ind
  : forall P : nat -> nat -> Prop,
    (forall n : nat, n = 0 -> P 0 0) ->
    (forall n : nat, n = 1 -> P 1 0) ->
    (forall n n' : nat, n = n'.+2 -> P n' (div2'' n') -> P n'.+2 (div2'' n').+1) ->
    forall n : nat, P n (div2'' n).

Lemma leq_div2'' m: div2'' m <= m.
Proof.
  functional induction (div2'' m).
    by [].
      by [].
        by apply ltnW.
        
(* END *)
