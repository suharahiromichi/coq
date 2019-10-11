(**
Coq/SSReflect/MathComp による定理証明

第3章 演習問題と追加の問題、回答付き

======

2018_10_11 @suharahiromichi
 *)

From mathcomp Require Import all_ssreflect.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** 問 3.1  *)
(** 赤玉と白玉のふたつの要素からなるball型をInductiveを使って定
    義してください。 *)
(** Exercise 3.1 *)
(** Define the type "ball" that consists of two elements, red (rouge)
    and white (blanc). *)


(** 問 3.2 *)
(** ボールの列の型をlist型(またはseq型)を使って定義してください。 *)
(** Exercise 3.2 *)
(** Using the "list" (or "seq") type, Dinefine the type of sequence of balls. *)



(** 問 3.3 *)
(** 次のうち、正しい型をもつ値はどれでしょうか。Checkコマンドを使って
    確認してください。 *)
(** Exercise 3.3 *)
(** Which of the following values ​​has the correct type? Confirm using
    the "Check" command. *)


(** 問 3.4 *)
(** ボールの列に含まれる赤玉の数を数える関数を定義します。*)
(** Define a function that counts the number of rouge balls in a
    sequenceq of balls in several ways. *)

(** Fixpint コマンドを使って、型 balls -> nat を持つ関数 count_rouges
    を定義してください。以下に動作例を示します。 *)
(** そして、Compute コマンドを使って確認してください。 *)
(** Exercise 3.4 *)
(** Using "Fixpoint" command, Define the function "count_rouges" which
    has the "balls -> nat" type. *)
(** Examples of function values are shown below. *)
(**
   count_rouges nil                           ==> 0
   count_rouges (cons rouge nil)              ==> 1
   count_rouges (cons blanc nil)              ==> 0
   count_rouges (cons rouge (cons rouge nil)) ==> 2
   *)
(* And confirm using the "Compute" command. *)



(** 問 3.5 *)
(** count_rougs_with_map を map と sumn を使って定義してください。
    rougeを1、blancを0に置き換えた自然数列を求め、その総和を求めます。 *)
(** Exercise 3.5 *)
(** Define the function using map and sumn. The natural number
    sequence is obtained by replacing the rouge of the ball sequence
    with 1 and blanc with 0. Then calculate the sum. *)
(** Example
    [:: rouge; blanc; rouge] ==> [:: 1; 0; 1] ==> 1 + 0 + 1 = 2 *)


(** count_rouge と count_rouge_with_map の結果が一致することを証明して
    ください。 *)
(** Prove that the results count_rouge and count_rouge_with_map are
    consistent. *)


(** 問 3.6 *)
(** count_rougs_with_fil を filter と size を使って定義してください。
    rougeだけを残したボールの列を求め、そのサイズを求めます。 *)
(** Exercise 3.6 *)
(** Define the function using filter and size. Create a sequence of
    balls leaving only rouge and calculate its size. *)
(** Example
    [:: rouge; blanc; rouge] ==> [:: rouge; rouge] ==> size is 2 *)


(** count_rouge と count_rouge_with_fil の結果が一致することを証明して
    ください。 *)
(** Prove that the results count_rouge and count_rouge_with_fil are
    consistent. *)


(** 問 3.7 *)
(** ボールの列を反転 rev しても、count_rouge の結果が変わらないことを
    証明してください。 *)
(** Exercise 3.7 *)
(** Prove that reversing the sequence of ball does not change the result of
    count_rouge. *)

(** ヒント：count_rouge_with_map について証明する。 *)
Lemma count_rouges_seq__rev_seq s :
  count_rouges_with_map s = count_rouges_with_map (rev s).
Proof.
  by rewrite /count_rouges_with_map map_rev sumn_rev.
Qed.


(** 問 3.8 *)
(** ボールの列に含まれる白玉の数を数える関数を定義してください。赤玉の
    数お白玉の数を加算したものが、ボールの列全体のサイズと同じことを証
    明してください。 *)
(** Exercise 3.8 *)
(** Define a function that counts the number of blanc balls.
    Prove that the addition of red balls and white balls is
    equal to the size of the sequcence of balls. *)


(** 問 3.9 *)
(** ボールの列と、その赤玉の数を引数にとる命題を Inductive コマンドを
    使って定義してください。 *)
(** Exercise 3.9 *)
(** Using the Inductive command, define a proposition that takes a sequence of balls
    and the number of red balls as arguments. *)


(** 問 3.10 *)
(** 命題 「num_of_red [:: blanc; rouge] 1」 を証明してください。 *)
(** Exercise 3.10 *)
(** Prove the proposition "num_of_red [:: blanc; rouge] 1" *)



(** 問 3.11 *)
(** 命題 「num_of_red [:: blanc; rouge] 0」 の否定を証明してください。 *)
(** Exercise 3.11 *)
(** Prove the nagative of the proposition "num_of_red [:: blanc; rouge] 0" *)


(** 問 3.12 *)
(** 関数 count_rouges の結果と、述語 num_of_red の言明が同値であること
    を証明してください。 *)
(** Exercise 3.12 *)
(** Prove that the result of the function count_rouges and the
    statement of the predicate num_of_red are equivalent. *)


(* END *)
