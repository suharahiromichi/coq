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

Definition cp_proof (x : nat) := proj2_sig (safe_copy x).

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

Definition len_proof (a : list Z) := proj2_sig (safe_len a).

(* コード生成 *)
Extraction safe_len.
(*
let rec safe_len = function
  | Nil -> O
  | Cons (a, l0) -> S (safe_len l0)
*)

(* ***************************** *)
(* ***************************** *)
(* ***************************** *)

(* 
最大公約数の計算
http://www.math.nagoya-u.ac.jp/~garrigue/lecture/2013_SS/coq7.pdf
 *)
Require Import Arith Euclid Ring Omega Recdef.
Check modulo.

(*
引数が 0 でないという条件があり，結果は依存型になっている．
プログラムで使うには，まず引数の条件を削らなければならない．
引数に後者関数 S をかけることで条件が満たせる．引数の順番も普通に戻す．
*)

Definition mod' n m := (modulo (S m) (lt_O_Sn m) n).
(* proj1_sig と proj2_sig を使ってみる。 *)
Definition mod'_safe n m := proj1_sig (modulo (S m) (lt_O_Sn m) n).
Definition mod'_proof n m := proj2_sig (modulo (S m) (lt_O_Sn m) n).

Function gcd (m n : nat) {wf lt m} : nat :=
  match m with
    | O => n
    | S m' => gcd (mod'_safe n m') m
  end.
(* 減少の証明 *)
intros m n m' teq.
destruct (mod'_proof n m'). simpl.
destruct H as [Hn Hm].
apply Hm.
(* 整礎性の証明 *)
Search well_founded.
exact lt_wf.
Defined.

(* 講義ノートのオリジナルな定義 *)
Function gcd_orig (m n : nat) {wf lt m} : nat :=
match m with
| O => n
| S m' => gcd_orig (proj1_sig (mod' n m')) m
end.
(* 減少の証明 *)
intros.
destruct (mod' n m'). simpl.
destruct e as [q [Hn Hm]].
apply Hm.
(* 整礎性の証明 *)
Search well_founded.
exact lt_wf.
Defined.

(* END *)
