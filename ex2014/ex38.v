Require Import ssreflect.

(**
# 第8回

http://qnighy.github.io/coqex2014/ex6.html

## 課題38 (種別:A / 締め切り : 2014/06/01)

モノイドを型クラスとして定義する。以下の空欄を埋めよ。
*)

(* モノイド *)
Class Monoid (T : Type) := {
  mult : T -> T -> T
    where "x * y" := (mult x y);
  one : T
    where "1" := one;
  mult_assoc x y z : x * (y * z) = (x * y) * z;
  mult_1_l x : 1 * x = x;
  mult_1_r x : x * 1 = x
}.

Delimit Scope monoid_scope with monoid.
Local Open Scope monoid_scope.

Notation "x * y" := (mult x y) : monoid_scope.
Notation "1" := one : monoid_scope.

(* モノイドのリストの積 *)
Require Import List.
Check @fold_right bool bool.
Check @mult.

Definition product_of {T : Type} {M : Monoid T} : list T -> T :=
  fun (l : list T) => fold_right mult 1 l.
(* @fold_right T T (@mult T M) 1 l *)


(* 自然数の最大値関数に関するモノイド *)
Require Import Arith.
Check max.
Program Instance MaxMonoid : Monoid nat :=
  {|
    mult x y := max x y;
    one := 0
  |}.
Next Obligation.                            (* max x (max y z) = max (max x y) z *)
  by rewrite Max.max_assoc.
Qed.
Next Obligation.                            (* max x 0 = 0 *)
  by rewrite Max.max_0_r.
Qed.

Eval compute in product_of (3 :: 2 :: 6 :: 4 :: nil). (* => 6 *)
Eval compute in product_of (@nil nat). (* => 0 *)

(**
ヒント

Classの実体はRecordです。Classとして宣言すると、型クラスのように自動でインスタンスを探しに
行くようになり、インスタンスを明示する必要がなくなります。SetoidやProperもクラスです。

*)

(* END *)
