From mathcomp Require Import all_ssreflect.

(* 5.8 The generic theory of “big” operators *)

Fixpoint iota m n :=
  if n is u.+1 then
    m :: iota m.+1 u
  else
    [::].
Compute iota 3 5.                           (* = [:: 3; 4; 5; 6; 7] *)

Reserved Notation "\sum''_ ( m <= i < n ) F"
         (at level 41, F at level 41, i, m, n at level 50,
          format "'[' \sum''_ ( m  <=  i  <  n ) '/  '  F ']'").

Reserved Notation "\sum'_ ( m <= i < n | P ) F"
         (at level 41, F at level 41, i, m, n at level 50,
          format "'[' \sum'_ ( m  <=  i  <  n | P ) '/  '  F ']'").

Reserved Notation "\sum'_ ( m <= i < n ) F"
         (at level 41, F at level 41, i, m, n at level 50,
          format "'[' \sum'_ ( m  <=  i  <  n ) '/  '  F ']'").

Reserved Notation "\big [ op / idx ]_ ( i <- r | P ) F"
         (at level 36, F at level 36, op, idx at level 10, i, r at level 50,
          format "'[' \big [ op / idx ]_ ( i  <-  r  |  P ) '/  '  F ']'").

Reserved Notation "\big [ op / idx ]_ ( i <- r ) F"
         (at level 36, F at level 36, op, idx at level 10, i, r at level 50,
          format "'[' \big [ op / idx ]_ ( i  <-  r ) '/  '  F ']'").

Reserved Notation "\big [ op / idx ]_ ( m <= i < n | P ) F"
         (at level 36, F at level 36, op, idx at level 10, m, i, n at level 50,
          format "'[' \big [ op / idx ]_ ( m  <=  i  <  n  |  P )  F ']'").

Reserved Notation "\big [ op / idx ]_ ( m <= i < n ) F"
         (at level 36, F at level 36, op, idx at level 10, m, i, n at level 50,
          format "'[' \big [ op / idx ]_ ( m  <=  i  <  n )  F ']'").

Reserved Notation "\sum_ ( m <= i < n | P ) F"
         (at level 41, F at level 41, i, m, n at level 50,
          format "'[' \sum_ ( m  <=  i  <  n | P ) '/  '  F ']'").

Reserved Notation "\sum_ ( m <= i < n ) F"
         (at level 41, F at level 41, i, m, n at level 50,
          format "'[' \sum_ ( m  <=  i  <  n ) '/  '  F ']'").

(* 1.7 Iterators in mathematics *)
(* もっとも簡単な定義 *)

Notation "\sum''_ ( m <= i < n ) F" :=
  (foldr (fun i a => F + a) 0 (iota m (n - m))).

(* 5.8 The generic theory of “big” operators *)

Definition index_iota m n :=                (* U(i=m, i<n)、n は含まない！ *)
  iota m (n - m).

Compute index_iota 3 5.                     (* = [:: 3; 4] = U(i=3, i<5) ... *)

Definition bigop' {R I : Type}
           (idx : R)                        (* 初期値 *)
           (op : R -> R -> R)               (* big-opに対するsmall-op *)
           (r : seq I)                      (* リスト *)
           (P : pred I)                     (* 取出す条件、引数はi (I -> bool) *)
           (F : I -> R) :                   (* 個別の処理、引数はi *)
  R :=                                      (* 結果 *)
  foldr (fun (i : I) (x : R) => if P i then op (F i) x else x) idx r.

Local Notation "+%N" :=
  addn (at level 0, only parsing).

Notation "\sum'_ ( m <= i < n | P ) F":=
  (bigop' 0%N +%N (index_iota m n) P F%N) : nat_scope.

Notation "\sum'_ ( m <= i < n ) F":=
  (bigop' 0%N +%N (index_iota m n) true F%N) : nat_scope.


(* 5.9 Stable notations for big operators *)
(* To solve these problems 以降を抜粋する。 *)
(* やっていることは同じ。 *)

Inductive bigbody {R I : Type} :=
  BigBody of I & (R -> R -> R) & bool & R.

Definition sum_odd_def_body i :=            (* 例 *)
  BigBody i addn (odd i) i.

Definition applybig {R I} (body : @bigbody R I) acc :=
  let: BigBody _ op b v := body in
  if b then op v acc else acc.

Definition bigop {R I} idx r (body : I -> @bigbody R I) :=
  foldr (applybig \o body) idx r.

Notation "\big [ op / idx ]_ ( i <- r | P ) F" :=
  (bigop idx r (fun i => BigBody i op P F)) : big_scope.

Notation "\big [ op / idx ]_ ( i <- r ) F" :=
  (bigop idx r (fun i => BigBody i op true F)) : big_scope.

Notation "\big [ op / idx ]_ ( m <= i < n | P ) F" :=
  (\big[op/idx]_(i <- index_iota m n | P) F) : big_scope.

Notation "\big [ op / idx ]_ ( m <= i < n ) F" :=
  (\big[op/idx]_(i <- index_iota m n) F) : big_scope.

Local Notation "+%N" :=
  addn (at level 0, only parsing).

Notation "\sum_ ( m <= i < n | P ) F":=
  (\big[+%N/0%N]_(m <= i < n | P) F%N) : nat_scope.
(*
  (bigop 0%N (index_iota m n) (fun i => BigBody i addn P F%N)) : nat_scope.
*)

Notation "\sum_ ( m <= i < n ) F":=
  (\big[+%N/0%N]_(m <= i < n) F%N) : nat_scope.
(*
  (bigop 0%N (index_iota m n) (fun i => BigBody i addn true F%N)) : nat_scope.
*)

(* *********** *)
(* テストと証明 *)
(* *********** *)

Eval compute in \sum_(1 <= i < 5) (i * 2 - 1). (* = 16 : nat *)
Eval compute in \sum_(1 <= i < 5) i.           (* = 10 : nat *)

Lemma big_nat_recr {R : Type} (idx : R) (op : Monoid.law idx)  (n m : nat) (F : nat -> R) :
    m <= n ->
    \big[op/idx]_(m <= i < n.+1) F i =
    op (\big[op/idx]_(m <= i < n) F i) (F n).
(*
    bigop idx (index_iota m n.+1) (fun i => @BigBody R nat i op true (F i)) =
    op (bigop idx (index_iota m n) (fun i => BigBody i op true (F i))) (F n).
*)
Proof.
Admitted.

Lemma big_mkcond {I R : Type} (idx : R) (op : Monoid.law idx)
      (r : seq I) (P : pred I) (F : I -> R) :
  \big[op/idx]_(i <- r | P i) F i =
  \big[op/idx]_(i <- r) (if P i then F i else idx).
 (*
  bigop idx r (fun i => @BigBody R I i op (P i) (F i)) =
  bigop idx r (fun i => @BigBody R I i op true (if P i then F i else idx)).
*)
Proof.
Admitted.

Lemma sum_odd_3 : \sum_(0 <= i < 3.*2 | odd i) i = 3^2.
Proof.
  by rewrite big_mkcond big_nat_recr //=.
Qed.

Lemma test : \sum_(0 <= i < 6) i= (\sum_(0 <= i < 5) i) + 5.
Proof.
    by apply: big_nat_recr.
Qed.


(* Exercise 16. Sum of 2n odd numbers *)

Lemma sum_odd n : \sum_(0 <= i < n.*2 | odd i) i = n^2.
Proof.
  elim: n => [|n IHn].
  - done.
  - rewrite doubleS big_mkcond 2?big_nat_recr // -big_mkcond /=.
    rewrite {}IHn odd_double /= addn0 -addnn -!mulnn; ring.
Qed.

(* END *)
