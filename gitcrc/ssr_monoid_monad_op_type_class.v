(**
モナドがモノイドであることの証明

@suharahiromichi

2015_01_11
2015_04_29  (operational type class を使用してみる)
*)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
(*
Generalizable All Variables.
個々に、Generalizable Variables で宣言する。
*)
Require Import ssreflect ssrbool ssrnat eqtype seq ssrfun.

Reserved Notation "x * y" (at level 40, left associativity).
Reserved Notation "c >>= f" (at level 42, left associativity).


(**
Monoid モノイド
Monoidの定義は文献[1]など。
- carrier (台) A
- binary, associative operation 'dot' on A
- neutral element 1 ∈ A for 'dot'
 *)
Class monoid_binop (M : Type) := monoid_op : M -> M -> M.
Infix "*" := monoid_op.
Class Monoid {M : Type} (dot : monoid_binop M) (one : M) : Type :=
  {
    dot_assoc : forall x y z : M, x * (y * z) = (x * y) * z;
    one_left  : forall x, one * x = x;
    one_right : forall x, x * one = x
  }.
Print Monoid.        (* 値コンストラクタの指定を省いたので、それがBuild_Monoid になる。 *)
About one_left.      (* Arguments A, dot, one, Monoid are implicit *)
About one_right.

(**
Monad モナド
Monadの定義は文献[2]など。
*)
Class monad_binop {M : Type -> Type} {A B : Type} := monad_op : M A -> (A -> M B) -> M B.
Infix ">>=" := monad_op.
Class monad_return {M : Type -> Type} {A : Type} := monad_ret : A -> M A.
Class Monad {M : Type -> Type}
      (bind : forall {A B}, @monad_binop M A B)
      (ret : forall {A}, @monad_return M A) : Type :=
  {
    monad_1 : forall {A B} (f : A -> M B) (x : A),
                (ret x >>= f) = (f x);
    monad_2 : forall {A} (m : M A),
                (m >>= ret) = m;
    monad_3 : forall {A B C} (f : A -> M B) (g : B -> M C) (m : M A),
                (m >>= f >>= g) = (m >>= (fun x => f x >>= g))
  }.

(**
モナドがモノイドであることを証明する。
証明は文献[3]をもとの単純化した。
 *)

Require Import Coq.Logic.FunctionalExtensionality.
Check @functional_extensionality :
  forall (A B : Type) (f g : A -> B), (forall x : A, f x = g x) -> f = g.

Generalizable Variables M dot one.
Generalizable Variables F bind ret.
(*
普通に型変数を宣言しても、この場合は同じである。
Variable M : Type.
Variable F : Type -> Type.
*)

Program Instance MonMonoid `{MM : @Monoid M dot one} `{MF : @Monad F bind ret} :
  @Monoid (F M)
          (fun m n => m >>= (fun x => n >>= (fun y => monad_ret (x * y))))
          (monad_ret one).
Next Obligation.                            (* 結合則 *)
  rewrite /monoid_op.
  rewrite monad_3.
  congr (x >>= _).
  (* x >>= A ならよいが、A >>= B を分解してはいけない。 *)
  apply functional_extensionality => m.
  rewrite !monad_3.
  congr (y >>= _).
  apply functional_extensionality => m'.
  rewrite monad_1 monad_3.
  congr (z >>= _).
  apply functional_extensionality => m''.
  rewrite monad_1.
  congr (monad_ret _).
  rewrite -![dot _ _]/(monoid_op _ _).      (* fold monoid_op. *)
    by rewrite dot_assoc.
Qed.
Next Obligation.                            (* 左単位元 *)
  rewrite /monad_ret /monoid_op.
  rewrite monad_1 -{2}(monad_2 x).
  congr (x >>= _).
  apply functional_extensionality => y.
  congr (monad_ret _).
  rewrite -[dot _ _]/(monoid_op _ _).       (* fold monoid_op. *)
  by rewrite one_left.
Qed.
Next Obligation.                            (* 右単位元 *)
  rewrite /monad_ret /monoid_op.
  rewrite -{2}(monad_2 x).
  congr (x >>= _).
  apply functional_extensionality => y.
  rewrite monad_1.
  congr (monad_ret _).
  rewrite -[dot _ _]/(monoid_op _ _).       (* fold monoid_op. *)
  by rewrite one_right.
Qed.

(**
文献[1] A Gentle Introduction to Type Classes and Relations in Coq

文献[2] Coq演習2014 第8回 課題39
http://qnighy.github.io/coqex2014/ex8.html

文献[3] Monadモノイドはモノイドである。
http://qiita.com/minpou/items/20ba354b32af89b20c64
https://gist.github.com/minpou/0f4c4a509c253cd7d555
 *)

(* END *)
