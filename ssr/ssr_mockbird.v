(* To Mock a Mockingbird, Raymond Smullyan *)
(* https://en.wikipedia.org/wiki/To_Mock_a_Mockingbird *)

From mathcomp Require Import all_ssreflect.
Require Import Coq.Relations.Relations.
Require Import Coq.Relations.Relation_Operators.    (* rt1n_trans の別名問題 *)
Require Import Coq.Setoids.Setoid.
Require Import Coq.Classes.Morphisms.
Locate "_ ==> _".

(* 書き換えを -----> で表し、これで rewrite できるようにする。 *)

Reserved Notation "x '@' y" (at level 50, left associativity).
Inductive birdterm : Set :=
| birdapp of birdterm & birdterm            (* x @ y *)
| birdM                                     (* Mockingbird *)
| birdB.                                    (* Bluebird *)
Notation "x @ y" := (birdapp x y).

Reserved Notation "x '----->' y" (at level 70, no associativity).
Inductive bird_red : relation birdterm :=
| red_refl : forall (t1 : birdterm),
    bird_red t1 t1
| red_sym : forall (t1 t2 : birdterm),
    bird_red t1 t2 -> bird_red t2 t1
| red_trans : forall (t1 t2 t3 : birdterm),
    bird_red t1 t2 -> bird_red t2 t3 -> bird_red t1 t3
(*
| red_left : forall (t1 t2 t3 : birdterm),
    bird_red t1 t2 -> bird_red (t1 @ t3) (t2 @ t3)
| red_right : forall (t1 t2 t3 : birdterm),
    bird_red t1 t2 -> bird_red (t3 @ t1) (t3 @ t2)
*)
| red_lr : forall (t1 t2 t3 t4 : birdterm),
    bird_red t1 t2 -> bird_red t3 t4 -> bird_red (t1 @ t3) (t2 @ t4)
| red_b  : forall x y z,
    bird_red (birdB @ x @ y @ z) (x @ (y @ z)) (* 合成鳥 *)
| red_m  : forall x,
    bird_red (birdM @ x) (x @ x).           (* 物まね鳥 *)
Infix "----->" := bird_red.

Hint Resolve red_refl.

(* 反射、対称、遷移性を満たすこと。 *)
Instance route_equiv_Equiv : Equivalence bird_red.
Proof.
  split.
  - by apply: red_refl.
  - by apply: red_sym.
  - by apply: red_trans.
Qed.

(* @ の中を -----> で置き換えることができる。 *)
Instance app_red_Proper :
  Proper (bird_red ==> bird_red ==> bird_red) birdapp.
Proof.
  move=> x y Hxy u v Huv.
  by apply: red_lr.
Qed.

Section ch_9_to_mock_a_mockingbird.
  
  (* 1. *)
  
  Definition fond x y := x @ y -----> y.    (* X は Y が好き。 *)
  
  Definition birdY := fun a => birdB @ a @ birdM. (* 不動点演算子 *)
  
  (* すべての鳥は、少なくともひとつ好きな鳥がいる。 *)
  Lemma one : forall a, exists x, fond a x.
  Proof.
    move=> a.
    exists (birdY a @ birdY a).
      by rewrite /fond {2}red_b red_m.      (* apply: red_refl *)
  Qed.
  
End ch_9_to_mock_a_mockingbird.

(* END *)
