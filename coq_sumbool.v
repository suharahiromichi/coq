(***************************)
(* sumbool と it then else *)
(***************************)

(** 帰納型のチュートリアル **)
(** A Tutorial on [Co-]Inductive Types in Coq **)
(* 2.7 Logical connectives. *)

(* {A} + {B} は sumbool A B の意味である。 *)
Locate "{ _ } + { _ }".                     (* sumbool A B : type_scope *)
Print sumbool.
Check sumbool.
Check sumbool_ind.
Check sumbool_rec.
Check left.                                 (* forall A B : Prop, A -> {A} + {B} *)
Check right.                                (* forall A B : Prop, B -> {A} + {B} *)

Require Import Arith.
(* これらを独自に定義したい。 *)
Check le_lt_dec.                            (* forall n m : nat, {n <= m} + {m < n} *)
Print le_lt_dec.
Check eq_nat_dec.                           (* forall n m : nat, {n = m} + {n <> m} *)
Print eq_nat_dec.

Eval compute in eq_nat_dec 1 1.             (* 真：left _ *)
Eval compute in eq_nat_dec 0 1.             (* 偽：right _ *)

Eval compute in le_lt_dec 0 1.              (* 真：left _ *)
Eval compute in le_lt_dec 1 0.              (* 偽：right _ *)

(* match または if-then-else による定義 *)
Definition max (n p : nat) :=
  match le_lt_dec n p with
  | left _ => p
  | right _ => n
  end.
Print max.                                  (* if le_lt_dec n p then p else n *)
Check max.                                  (* nat -> nat -> nat *)
Eval compute in max 1 2.                    (* 2 *)

(* これは、if-then-elseに変換される。 *)
Definition max' (n p : nat) :=
  if le_lt_dec n p then p else n.
Eval compute in max' 1 2.                   (* 2 *)

(* OCaml に変換すると、これは match である *)
Extraction max.

(* coqにおける、it-then-else と match の関係 *)
Eval compute in (if le_lt_dec 1 2 then 2 else 1). (* 2 *)
Eval compute in (match le_lt_dec 1 2 with left _ => 2 | right _ => 1 end). (* 2 *)

(* case による振り分け *)
Theorem le_max : forall n p, n <= p -> max n p = p.
  intros n p H.
  unfold max.
  (* Goal : (if le_lt_dec n p then p else n) = p *)
  case (le_lt_dec n p).
    
  (* Goal : n <= p -> p = p *)
  reflexivity.                              (* 「->」が前についていても、問題ない *)

  (* Goal : p < n -> n = p *)
  intros l.
  absurd (p < p).
  eauto with arith.
  eauto with arith.
Qed.

(* この場合の case は、
  コンストラクタの apply には置き換えられない。
  see. coq_case.v  *)

Require Import Bool.Sumbool.

(* boolを返すeq関数を定義する。 *)
Definition eq_bool (n p : nat) : bool :=
  proj1_sig (bool_of_sumbool (eq_nat_dec n p)).

Eval compute in eq_bool 1 1.                (* 真：left _ *)
Eval compute in eq_bool 0 1.                (* 偽：right _ *)

(* boolを返すle関数を定義する。 *)
Definition le_bool (n p : nat) : bool :=
  proj1_sig (bool_of_sumbool (le_lt_dec n p)).

Eval compute in le_bool 0 1.                (* 真：left _ *)
Eval compute in le_bool 1 0.                (* 偽：right _ *)

Theorem le_max' : forall n p, le_bool n p = true -> max n p = p.
(* これを証明したい。 *)
Admitted.

(* END *)
