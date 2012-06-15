(* 2011_01_22 *)


(* 依存積 *)
(* Prop型 *)
Inductive my_ex (A : Type) (P : A -> Prop) : Prop :=
| my_ex_intro : forall x : A, P x -> my_ex A P.
Notation "'exists' x : A, P" := (my_ex (fun A (x : A) => P x)) (at level 190).


(* 関数型 *)
Inductive my_sig (A : Type) (P : A -> Prop) : Type :=
| my_exist : forall x : A, P x -> my_sig A P.
Notation "{ x : A, P }" := (my_sig (fun A (x : A) => P x)) (at level 190).




(* 依存和 *)
(* Prop型 （普通の or） *)
Inductive my_or (A B : Prop) : Prop :=
| my_or_introl : A -> my_or A B
| my_or_intror : B -> my_or A B.
Notation " A \/ B " := (my_or A B).


(* 関数型 *)
Inductive my_sumbool (A B : Prop) : Set :=
| my_left  : A -> my_sumbool A B
| my_right : B -> my_sumbool A B.
Notation "{ A } + { B }" := (my_sumbool A B).


(*
   sumboolで left と rightタクティクスが使える理由：
   
   タクティクス left は、constructor 1
   タクティクス right は、constructor 2
   の略記で、それぞれ1番めと2番めのコンストラクタをapplyする。
   my_right, my_left の順番に書くと
   タクティクス left が、apply my_right になってしまう。
*)


(********)
(* 応用 *)
(********)


(* exists n, 0 <= n : Prop
   と同じものを定義する。
   ただし、my_ex を使ったわけではない。
   *)
Inductive my_le_zero : nat -> Prop :=
| my_le_0 : my_le_zero 0
| my_le_S : forall n : nat,
  my_le_zero n -> my_le_zero (S n).


Goal my_le_zero 1.                          (* 1 *)
Proof.
  apply my_le_S.
  apply my_le_0.
Qed.




(* zerop :
   {n = 0} + {0 < n} と同じものを定義する
   *)
Require Import Arith.                       (* gt_le_S など *)
Definition my_zerop n : my_sumbool (n = 0) (0 < n).
destruct n.
apply my_left; apply refl_equal.
apply my_right; change (1 <= S n);
  apply gt_le_S; change (0 < S n);
    apply lt_O_Sn.
Defined.                                    (* Defined *)


Eval compute in (match my_zerop 1 with
                   | my_left _ => 0
                   | my_right _ => 100 end). (* 100 *)


(* END *)