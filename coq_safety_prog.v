(* coqによるsafe programming *)


(* 仕様を公理として記述する。 *)
Inductive copied : nat -> nat -> Prop :=
  | copied0 : forall x : nat, copied x x.


Goal copied 1 1.
  apply copied0.
Qed.


(* 必要な定理を証明しておく。 *)
Theorem t_copied :                          (* Lemma でもよい。 *)
  forall x : nat, copied x x.
Proof.
  apply copied0.
Qed.


(* 関数を定義する。 *)
Definition safe_copy :                      (* Lamma でもよいが。 *)
  forall x : nat, {y : nat | copied x y}.
Proof.
  intros x.
  exists x.
  apply t_copied.
Defined.                                    (* Qedではいけない！！！！ *)


Definition cp (x : nat) := proj1_sig (safe_copy x).
(* existなので、proj1_sigで値を取り出す。 *)


(* Coq上で動作を確認する。 *)
Eval cbv in cp 120.                         (* 120 : nat *)


(* Camlのコードを生成する。*)
Extraction safe_copy.                       (* let copy x = x *)


(* ***************************** *)
(* ***************************** *)
(* ***************************** *)


(* リストの長さを求める関数 *)
Require Import List.
Require Import ZArith.
Open Scope Z_scope.


(* 仕様 *)
Inductive length : list Z -> nat -> Prop :=
  | length0 : length nil 0
  | length1 : forall (l : list Z) (n : nat) (z : Z),
    length l n -> length (z :: l) (S n).


Hint Resolve length0 length1 : length.


Goal length (1::2::3::nil) 3%nat.
  auto with length.
Qed.


(* プログラム *)
(* 任意のaに対して、(length a n)なるnが存在する。 *)
Definition safe_len :
  forall (a : list Z), {n : nat | length a n}.
Proof.
  intros a.
  induction a.


  (* Goal :: {n : nat | length nil n} *)
  exists 0%nat.
  auto with length.                         (* apply length0. *)
  
  (* {n : nat | length (a :: a0) n} *)
  case IHa.
  intros.
  exists (S x)%nat.
  auto with length.                         (* apply length1. apply l. *)
Defined.                                    (* Definedであること。 *)


Definition len (a : list Z) := proj1_sig (safe_len a).


(* テストする *)
Eval cbv in len (1::2::3::nil).             (* 3%nat *)


(* コード生成 *)
Extraction safe_len.
(*
let rec safe_len = function
  | Nil -> O
  | Cons (a, l0) -> S (safe_len l0)
*)


(* END *)