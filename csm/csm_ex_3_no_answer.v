(**
Coq/SSReflect/MathComp による定理証明

第3章 演習問題と追加の問題

======

2018_10_11 @suharahiromichi
 *)

From mathcomp Require Import all_ssreflect.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(**
第3章では、SSReflect 拡張の主なタクティクやコマンドを勉強しました。章
の最後にある演習問題 (page.124) を解いていきます。問題は、すべて、この
ファイルに転記してあります。追加の問題も用意しました。

In Chapter 3, we studied tactics and commands of the SSReflect
extension. Solve the exercise at the end of the chapter. (page.124)
All problems are posted in this file. Additional issues have also been
prepared.

第4章の予習として、eqType 型クラス (インターフェース）のインスタンスを
定義して、同じ問題を解いてみます（次回以降）。

As a preparation of Chapter 4, define an instance of the eqType type
class (or interface) and try to solve the same problems.
*)


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

Check nil.
Check rouge.
Check cons rouge nil.
Check nil cons rouge nil.
Check cons blanc (cons rouge nil).


(** 問 3.4〜6 では、いくつかの方法で、ボールの列に含まれる赤玉の数を数える関
    数を定義します。*)
(** In exercise 3.4 to 6, define a function that counts the number of rouge
    balls in a sequenceq of balls in several ways. *)

(** 問 3.4 *)
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
    sumn (map (λx. if x is rouge then 1 else 0) [:: rouge; blanc; rouge])
    ==> sumn [:: 1; 0; 1]
    ==> 1 + 0 + 1
    ==> 2
 *)


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
    size (filter (λx. if x is rouge then true else false) [:: rouge; blanc; rouge])
    ==> size [:: rouge; rouge]
    ==> 2
 *)


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


(** 問 3a *)
(** SSReflect/MathComp は、Standard Coqよりもbool型の等式を使います。
    決定性のある等式（bool型の等式）の成り立つ型のクラス (eqType) が用意されています。
    ユーザの定義した型をeqTypeのインスタンスとすることで、eqTypeで定義された関数や定理を
    使うことができます。bool型は真が偽かに決まるため、証明がやさしくなる場合があります。
    SSReflect/MathCompの方法で、もういちど、問題を解いてみましょう。
 *)

(** Exercise 3a *)
(** SSReflect/MathComp uses bool type equations rather than Standard
    Coq.  There is a type class (eqType) that holds deterministic
    equations (equals of type bool).
    By making the user-defined type an instance of eqType, you can use
    the functions and theorems defined by eqType. Since the bool type
    is determined to be true or false, the proof may be easy.
    Let's solve the exercises again with the SSReflect/MathComp way.
 *)

(** なお、今回は証明は単純になりませんが、count_rouge_xxx の定義が簡単になります。 *)
(** Note that this time the proof will not be simple,
    but the definition of count_rouge will be easy. *)

(** 問 3a.1 (1) *)
(** 赤玉と白玉のふたつの要素からなるball型をInductiveを使って定
    義してください。 *)
(** Exercise 3a.1 (1) *)
(** Define the type "ball" that consists of two elements, red (rouge)
    and white (blanc). *)

(** 3.1 と同じ。 *)
(** Same as ex. 3.1 *)


(** 問 3a.1 (2) *)
(** ball型をeqTypeのインスタンス、ball_eqType として定義してみましょう。 *)
(** Exercise 3a.1 (2) *)
(** Define the ball type as an instance of eqType, ball_eqType. *)

(** 最初に、ball型どうしのbool形の等式 eqBall を定義します。 *)
(** First, define a bool equation between ball types. *)

(** 次に、eqBall が Standard Coqの等式 eq （=) と同値であるこを証明しましょう。
    reflect は、以下の意味の述語で、ssrbool.v で定義されています。
    
    eq が証明可能 <-> eqBall が true
    eq の否定が証明可能 <-> eqBall が false
*)
(** Next, let's prove that eqBall is equivalent to the Standard Coq equation (=).
    reflect is a predicate with the following meaning, defined in ssrbool.v.
    
    eq can be proved <-> eqBall is true
    eq negation can be proved <-> eqBall is false
*)

(** 最後に、ball_eqType を定義します。 *)
(** Finally, define ball_eqType. *)

(** eq_op (==) が使えることを確認します。 *)
(** Confirm that you can use eq_op (==) *)

(** 問 3a.2 *)
(** ボールの列の型をlist型(またはseq型)を使って定義してください。 *)
(** Exercise 3a.2 *)
(** Using the "list" (or "seq") type, Dinefine the type of sequence of balls. *)

(** seq形も、eqType のインスタンスなので、eq_op (==) が使えます。 *)
(** The seq form is also an instance of eqType, so you can use eq_op (==) *)


(** 問 3a.3 (略) *)
(** Exercise 3.3 (omitted) *)


(** 問 3a.4 *)
(** Fixpint コマンドを使って、型 balls -> nat を持つ関数 count_rouges
    を定義してください。 *)
(** Exercise 3.4 *)
(** Using "Fixpoint" command, Define the function "count_rouges" which
    has the "balls -> nat" type. *)

(** 3.4 と同じ。 *)
(** Same as ex. 3.4 *)


(** 問 3a.5 *)
(** count_rougs_with_map を map と sumn を使って定義してください。
    rougeを1、blancを0に置き換えた自然数列を求め、その総和を求めます。 *)
(** Exercise 3a.5 *)
(** Define the function using map and sumn. The natural number
    sequence is obtained by replacing the rouge of the ball sequence
    with 1 and blanc with 0. Then calculate the sum. *)

(** count_rouge と count_rouge_with_map の結果が一致することを証明して
    ください。 *)
(** Prove that the results count_rouge and count_rouge_with_map are
    consistent. *)


(** 問 3a.6 *)
(** count_rougs_with_fil を filter と size を使って定義してください。
    rougeだけを残したボールの列を求め、そのサイズを求めます。 *)
(** Exercise 3a.6 *)
(** Define the function using filter and size. Create a sequence of
    balls leaving only rouge and calculate its size. *)

(** count_rouge と count_rouge_with_fil の結果が一致することを証明して
    ください。 *)
(** Prove that the results count_rouge and count_rouge_with_fil are
    consistent. *)



(* END *)
