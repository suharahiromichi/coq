(* マッカーシーの91関数 *)
(* McCarthy 91 function *)

Require Import ZArith.
Require Import Omega.
Open Scope Z_scope.

(* Program Command を使って、停止性を含めて証明しようとすると、とても大変である。 *)

Require Import Program.
Program Fixpoint M91 (x : Z) {measure (Z.to_nat (Zmax 0 (101 - x)))} :
  {n | n = if Z_le_dec x 100 then 91 else x - 10} :=     (* n = g x *)
  if Z_le_dec x 100 then M91 (M91 (x + 11)) else x - 10. (* Fix F *)
Admit Obligations.

(*
 しかし、不動点帰納法の1ステップ分の
F g x = g x.
を証明するのは易しい。
 *)

(* 91関数の意味 *)
Definition g (x : Z) :=
  if Z_le_dec x 100 then 91 else x - 10.

Compute g (-1%Z).                           (* 91 *)
Compute g 10.                               (* 91 *)
Compute g 100.                              (* 91 *)
Compute g 101.                              (* 91 *)
Compute g 102.                              (* 92 *)
Compute g 103.                              (* 93 *)

(* F : (Z -> Z) -> Z -> (Z -> Z) の最小不動点が、91関数になる。 *)
Definition F (f : Z -> Z) (x : Z) :=
  if Z_le_dec x 100 then f (f (x + 11)) else x - 10.

Compute F g (-1%Z).                         (* 91 *)
Compute F g 10.                             (* 91 *)
Compute F g 100.                            (* 91 *)
Compute F g 101.                            (* 91 *)
Compute F g 102.                            (* 92 *)
Compute F g 103.                            (* 93 *)

Goal forall (x : Z), F g x = g x.
Proof.
  intro x.
  unfold F.
  unfold g.
  destruct (Z_le_dec x 100).
  - destruct (Z_le_dec (x + 11) 100); simpl.
    + reflexivity.                          (* 91 = 91 *)
    + destruct (Z_le_dec (x + 11 - 10) 100).
      * reflexivity.                        (* 91 = 91 *)
      * omega.                              (* 前提の矛盾 *)
  - reflexivity.                            (* x - 10 = x - 10 *)
Qed.

(* END *)

(*
Goal forall (x : Z), F g x = g x.
Proof.
  intro x.
  unfold F.
  destruct (Z_le_dec x 100).
  - unfold g at 2.
    destruct (Z_le_dec (x + 11) 100).
    + unfold g; simpl.
      destruct (Z_le_dec x 100).
      * reflexivity.
      * exfalso.
        now apply n.
    + unfold g; simpl.
      destruct (Z_le_dec (x + 11) 100).
      * now exfalso.
      * destruct (Z_le_dec (x + 11 - 10) 100).
        ** destruct (Z_le_dec x 100).
           *** reflexivity.
           *** now exfalso.
        ** destruct (Z_le_dec x 100).
           *** cut (x = 100).
               intro H.
               rewrite H. simpl.
               reflexivity.
           **** omega.
           *** now exfalso.
  - unfold g; simpl.
    destruct (Z_le_dec x 100).
    + exfalso.
      now apply n.
    + reflexivity.
Qed.

 *)
