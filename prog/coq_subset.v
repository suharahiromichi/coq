(**
Subset Type と Program コマンド
 *)

Require Import Bool.
Require Import List.
Require Import Omega.
Require Import Program.
Set Implicit Arguments.

(** * はじめに *)

(**
Coqの「Program」コマンドを使って、
「関数型プログラムの定義と証明を同時に行う」
という問題に取り組んでいます。

そこで使う サブセットタイプ (Subset Type) について説明します。

ソースコードは
#<a href="https://github.com/suharahiromichi/coq/blob/master/prog/coq_subset.v">ここ</a>#
にあります。

また、
#<a href="http://adam.chlipala.net/cpdt/"> CPDT </a># の 6.1節も参考になります。
*)

(** * 概説 *)

(**
自然数を(+ 1)する関数 succ を考えてみます。
 *)

Definition succ' (x : nat) : nat := x + 1.

(**
これは自然数から自然数の関数
 *)

Check succ' : nat -> nat.

(**
でまちがいありませんが、
詳しくみると、値域は自然数全体ではなく、「1 以上の自然数」つまり自然数のサブセットです。

Coqでは、これを次のように書きます。「1 以上の自然数の型」という意味になります。
*)

Check {y : nat | 1 <= y} : Type.

(**
これを使って、(+ 1)する関数 succ を定義しなおすと、次のようになります。

Program コマンドを使うと、nat 型である [x + 1] から、
上記のサブセットへのコアーションが自動的に行われます。

また、[1 <= x + 1] を証明することを求められます（証明責務）ので、[omega] で解きます。
  *)

Program Definition succ (x : nat) : {y : nat | 1 <= y} :=
  x + 1.
Obligation 1.
Proof.
  (* Goal : 1 <= x + 1 *)
  omega.
Defined.

(**
(+ 2)する関数をsuccをふたつ使って定義すると、次のようになります。

ここでもコアーションが行われています。
また、こんども証明責務は [omega] で解けます。
  *)

Program Definition succsucc (x : nat) : {y : nat | 2 <= y} :=
  succ (succ x).
Obligation 1.
Proof.
  (* 2 <= x + 1 + 1 *)
  omega.
Defined.

(**
実行すると、つぎのようになります。演算子「`」については後述します。
 *)

Compute ` (succ 3).                         (** ==> 4 *)

Compute ` (succsucc 3).                     (** ==> 5 *)


(** * Subset タイプ *)

(**
型 A の要素の x うち、述語 P を満たす P x からなる集合で示されるサブタイプは、

[{x : A | P x}]

で示します。
*)

Locate "{ _ : _ | _ }".
(**
は、型コンストラクタ [sig] の構文糖です。
コンストラクトするのは Set でなく Type であることを忘れないでください。

[ "{ x : A  |  P }" := sig (fun x => P)]

x は P の中に出現する変数です。
 *)

Print sig.
(**
[[
Inductive sig (A : Type) (P : A -> Prop) : Type :=
    exist : forall x : A, P x -> {x : A | P x}
]]

また、[sig] は、[exist] を値コンストラクタとする、サブタイプ型です。
 *)

(**
exist は、A型の具体的な値 [a] が [P a] を成り立たせるとき、

[exist P a H]

と書けます。ここで [H] は、[P a] が成り立つ「証明」です。
また、具体的な値 [a] を witness と呼ぶ場合があります。
*)

(**
1 以上の自然数の集合である型 [{x : nat | 1 <= x}] の例に戻ると、
これは、述語 [fun x => 1 <= x] を満たす自然数です。

witness を 3 とすると、3は1より大きいことの証明を用意しておいて、
 *)

Lemma three_ge_1 : 1 <= 3.
Proof.
  omega.
Qed.

(**
この証明を使って、以下のように定義できます。

これは、[{x : nat | 1 <= x}] の型を持っていることがわかります。
  *)

Definition three := exist (fun x => 1 <= x) 3 three_ge_1.

Check three : {x : nat | 1 <= x} : Type.

(**
同じことですが、Proof モードを使用して定義することもできます。
*)

Definition three' : {x : nat | 1 <= x}.
Proof.
  exists 3.
  omega.
Defined.

(**
これから、witness を取り出すには [proj1_sig] というセレクタを使います。

これは、「`」という演算子として定義されています。
 *)

Locate "` _".                               (** " `  t " := proj1_sig t   *)

Check proj1_sig : forall (A : Type) (P : A -> Prop), {x : A | P x} -> A.

Compute ` three.                            (** ==> 3 *)

Compute ` three'.                           (** ==> 3 *)


(** * 「Program」コマンド *)

(**
最初の succ の例にもどってみましょう。

値がサブセット型のとき、普通に Definition すると
[[
Definition succ'' (x : nat) : {y : nat | 1 <= y} := x + 1.

Error:
In environment
x : nat
The term "x + 1" has type "nat" while it is expected to have type
 "{y : nat | 1 <= y}".
]]

というエラーになります。
このままでは、値 x + 1 はサブタイプ型ではないからです。
この型変換（コアーション）をやってくてるのが「Program」コマンドです。
*)

(** * もっとも簡単な例  *)

(**
自然数から自然数の ident関数 [id] の値の型は、 その引数が [n] であるとき、
[{x | x = n}] となります。

これを使って id 関数を定義すると次のようになります。
値のサブタイプ型の部分では、このように引数を参照することができます。
*)

Program Fixpoint id (n : nat) : {x | x = n} := n.

Compute ` (id 3).                           (** ==> 3 *)


(** * もうひとつの例  *)

(**
#<a href="https://coq.inria.fr/refman/Reference-Manual027.html">
Coq Reference Manual Chapter 24"</a>#
にある例です。

自然数を 2 で割る関数を考えます。引数が [n] のとき、値 [x] は

[n = 2 * x] または [n = 2 * x + 1] となります。

値のサブタイプ型は、

[{x : nat | n = 2 * x \/ n = 2 * x + 1}]

となります。これを使って関数を定義すると次のようになります。
*)

Program Fixpoint div2 (n : nat) : 
  { x : nat | n = 2 * x \/ n = 2 * x + 1 } :=
  match n with
    | S (S p) => S (div2 p)
    | _ => 0
  end.
Next Obligation.
Proof.
  (**
[[
p = x + (x + 0) \/ p = x + (x + 0) + 1 ->
S (S p) = S (x + S (x + 0)) \/ S (S p) = S (x + S (x + 0) + 1)
]]
   *)
  case o; intro H.
  - left.
    rewrite H.
    now auto.
  - right.
    rewrite H.
    rewrite plus_0_r.
    pattern (x + S x); rewrite plus_comm.
    rewrite plus_Sn_m.
    now auto.
Defined.
Next Obligation.
  (**
[[
p + 2 <> n -> n = 0 \/ n = 1
]]
   *)
  destruct n ; simpl in * ; intuition.
  destruct n ; simpl in * ; intuition.
  elim (H n) ; auto.
Qed.

Compute ` (div2 4).                         (** ==> 2 *)

Compute ` (div2 5).                         (** ==> 2 *)

Extraction div2.
(**
これから生成される OCaml のコードはつぎのようになります。

[[
val div2 : nat -> nat

let rec div2 = function
| O -> O
| S n0 ->
  (match n0 with
   | O -> O
   | S p -> S (div2 p))
]]
*)

(* END *)
