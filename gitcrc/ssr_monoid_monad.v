(**
モナドがモノイドであることの証明

@suharahiromichi

2015_01_11
*)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
(*
Generalizable All Variables.
*)
(* Require Import Basics Tactics Coq.Setoids.Setoid Morphisms. *)
Require Import ssreflect ssrbool ssrnat eqtype seq ssrfun.
Require Import div.

Reserved Notation "x * y" (at level 40, left associativity).
Reserved Notation "c >>= f" (at level 42, left associativity).


(**
Monoid モノイド
Monoidの定義は文献[1]
- carrier (台) A
- binary, associative operation 'dot' on A
- neutral element 1 ∈ A for 'dot'
 *)
Class Monoid {M : Type} : Type :=
  {
    dot : M -> M -> M where "x * y" := (dot x y);
    one : M;
    dot_assoc : forall x y z: M, x * (y * z) = (x * y) * z;
    one_left  : forall x, one * x = x;
    one_right : forall x, x * one = x
  }.
Notation "x * y" := (dot x y).

Print Monoid.        (* 値コンストラクタの指定を省くと、Build_Monoid になる。 *)
About one_left.      (* Arguments A, dot, one, Monoid are implicit *)
(* Class ではなく、Record の場合は、dot one は implicit ではない。 *)
About one_right.


(**
Monad モナド
Monadの定義は文献[2]
*)
Class Monad {M : Type -> Type} :=
  {
    bind {A B} : M A -> (A -> M B) -> M B
      where "x >>= f" := (bind x f);
    ret {A} : A -> M A;
    monad_1 : forall {A B} (f : A -> M B) (x : A),
                (ret x >>= f) = (f x);
    monad_2 : forall {A} (m : M A),
                (m >>= ret) = m;
    monad_3 : forall {A B C} (f : A -> M B) (g : B -> M C) (m : M A),
                (m >>= f >>= g) = (m >>= (fun x => f x >>= g))
}.
Notation "x >>= f" := (@bind _ _ _ _ x f).


(**
モナドがモノイドであることを証明する。
証明は文献[3]をもとの単純化した。
 *)

Require Import Coq.Logic.FunctionalExtensionality.
Check @functional_extensionality :
  forall (A B : Type) (f g : A -> B), (forall x : A, f x = g x) -> f = g.

Generalizable Variables M F.                (* この場合が、M Fは自動判定される。 *)
(*
普通に型変数を宣言しても、この場合は同じである。
Variable M : Type.
Variable F : Type -> Type.
*)

Instance MonMonoid `{MM : @Monoid M} `{MF : @Monad F} : @Monoid (F M) :=
  {
    one := ret one;
    dot m n :=
      m >>= (fun x => n >>= (fun y => ret (x * y)))
  }.
Proof.
  (* 結合則 *)
  - move=> x y z.
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
    by rewrite dot_assoc.
  (* 左単位元 *)
  - move=> x.
    rewrite monad_1 -{2}(monad_2 x).
    congr (x >>= _).
    apply functional_extensionality => y.
    by rewrite one_left.
  (* 右単位元 *)
  - move=> x.
    rewrite -{2}(monad_2 x).
    congr (x >>= _).
    apply functional_extensionality => y.
    by rewrite monad_1 one_right.
Qed.    

(* END *)

(**
文献[1] A Gentle Introduction to Type Classes and Relations in Coq

文献[2] Coq演習2014 第8回 課題39
http://qnighy.github.io/coqex2014/ex8.html

文献[3] Monadモノイドはモノイドである。
http://qiita.com/minpou/items/20ba354b32af89b20c64
https://gist.github.com/minpou/0f4c4a509c253cd7d555
 *)
