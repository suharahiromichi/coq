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
#<a "https://github.com/suharahiromichi/coq/blob/master/prog/coq_subset.v">ここ</a>#
にあります。

また、
#<a "http://adam.chlipala.net/cpdt/"> CPDT </a># の 6.1節も参考になります。
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
は、[sig] の構文糖です。x は P の中に出現する変数です。

 [ "{ x : A  |  P }" := sig (fun x => P)]
 *)

Print sig.
(**
[
Inductive sig (A : Type) (P : A -> Prop) : Type :=
    exist : forall x : A, P x -> {x : A | P x}
]
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

Check three : {x : nat | 1 <= x}.

(**
これから、witness を取り出すには [proj1_sig] というセレクタを使います。

これは、「`」という演算子として定義されています。
 *)

Locate "` _".                               (** " `  t " := proj1_sig t   *)

Check proj1_sig : forall (A : Type) (P : A -> Prop), {x : A | P x} -> A.

Compute ` three.                            (** ==> 3 *)


(** * 「Program」コマンド *)

(* END *)
