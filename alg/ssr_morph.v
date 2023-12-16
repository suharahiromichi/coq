From mathcomp Require Import all_ssreflect.
From mathcomp Require Import all_algebra.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Order Order.TTheory.                 (* order.v *)
Import GRing GRing.Theory.                  (* ssralg.v *)
Import Num Num.Def Num.Theory.              (* ssrnum.v *)
Open Scope ring_scope.

(**
coq/theories/ssr/ssrfun.v   (new)
mathcomp/ssreflect/ssrfun.v (old)

Morphisms for functions and relations:
*)

(**
ssrfun.v で定義されている {morph f : x / G x} などの意味をまとめる。

ssreflect（またはCoq本体）で定義されている事項で、
ここには、補題自体の説明はないが、
ssralg.v 以降の補題では、これらが頻出するため、
ここで覚えておくことが望ましい。

2023/10/1 @suharahiromichi
*)

(**
# 例

``- (x + y) = - x - y`` というよく使う補題だが、パターンではサーチできず、
morph の記法がわからないと、探せないし、見つけられない。

``-%R``は opp 関数の表記
 *)
Check opprD : forall V : zmodType, {morph -%R : x y / x + y}.
Check opprD : forall (V : zmodType) (x y : V), - (x + y) = - x + (- y).
Check opprD : forall (V : zmodType) (x y : V), - (x + y) = - x - y.
(* 2項の``_ - _`` は、``_ + (- _)`` の表記である。 *)

Search (- (_ + _)).                         (* 見つからない。 *)
Search ({morph -%R : _ _ / _ + _}).         (* 見つかる。 *)

(**
# morph/homo/mono
*)

Variable U W V : Type.

(**
## morph

Fしてからfしたものも、fしてからGしたものも、等しい。
 *)
(**
    {morph f : x / a >-> r} <-> f is a morphism with respect to functions
                               (fun x => a) and (fun x => r); if r == R#[#x#]#,
                               this states that f a = R#[#f x#]# for all x.
*)
Axiom a1 : forall (f : U -> V) (F : U -> U) (G : V -> V), {morph f : x / F x >-> G x}.
Check a1 : forall (f : U -> V) (F : U -> U) (G : V -> V) (x : U), f (F x) = G (f x).

(**
          {morph f : x / a} <-> f is a morphism with respect to the
                               function expression (fun x => a). This is
                               shorthand for {morph f : x / a >-> a}; note
                               that the two instances of a are often
                               interpreted at different types.
 *)
Axiom a2 : forall (f : V -> V) (G : V -> V), {morph f : x / G x}. (* G x >-> G x *)
Check a2 : forall (f : V -> V) (G : V -> V) (x : V), f (G x) = G (f x).

(**
  {morph f : x y / a >-> r} <-> f is a morphism with respect to functions
                               (fun x y => a) and (fun x y => r).
 *)
Axiom a3 : forall (f : U -> V) (F : U -> U -> U) (G : V -> V -> V), {morph f : x y / F x y >-> G x y}.
Check a3 : forall (f : U -> V) (F : U -> U -> U) (G : V -> V -> V) (x y : U), f (F x y) = G (f x) (f y).

(**
        {morph f : x y / a} <-> f is a morphism with respect to the
                               function expression (fun x y => a).
 *)
Axiom a4 : forall (f : V -> V) (G : V -> V -> V), {morph f : x y / G x y}. (* G x y >-> G x y *)
Check a4 : forall (f : V -> V) (G : V -> V -> V) (x y : V), f (G x y) = G (f x) (f y).

(**
## morph と distribution との関係
*)

Lemma morph_distrl (op : V -> V -> V) (G : V -> V -> V) :
  (forall (v : V), {morph op^~ v : x y / G x y}) <-> left_distributive op G.
Proof.
  split=> H.
  - move=> x y z.
    by apply: H.
  - move=> z x y.
    by apply: H.
Qed.

Lemma morph_distr  (op : V -> V -> V) (G : V -> V -> V) :
  (forall (v : V), {morph op v : x y / G x y}) <-> right_distributive op G.
Proof.
  split=> H.
  - move=> x y z.
    by apply: H.
  - move=> z x y.
    by apply: H.
Qed. 

(**
## morph 補足

``{rmorphism R -> S}`` は ssralg.v で定義されている。
複素数の共役 ``^*`` (conj_op) がこれであるため重要である。
*)
Section Rmorph.
Variable R S : semiRingType.

Axiom a1' : forall (f : {rmorphism R -> S}) (F : R -> R) (G : S -> S), {morph f : x / F x >-> G x}.
Check a1' : forall (f : {rmorphism R -> S}) (F : R -> R) (G : S -> S) (x : R), f (F x) = G (f x).
End Rmorph.

(**
## homo

Fが成り立つなら、fしてからGも成り立つ。
 *)
(**
     {homo f : x / a >-> r} <-> f is a homomorphism with respect to the
                               predicates (fun x => a) and (fun x => r);
                               if r == R#[#x#]#, this states that a -> R#[#f x#]#
                               for all x.
 *)
Axiom h1 : forall (f : U -> V) (F : U -> Prop) (G : V -> Prop), {homo f : x / F x >-> G x}.
Check h1 : forall (f : U -> V) (F : U -> Prop) (G : V -> Prop) (x : U), F x -> G (f x).

(**
           {homo f : x / a} <-> f is a homomorphism with respect to the
                               predicate expression (fun x => a).
*)
Axiom h2 : forall (f : U -> U) (F : U -> Prop), {homo f : x / F x}.
Check h2 : forall (f : U -> U) (F : U -> Prop) (x : U), F x -> F (f x).

(**
   {homo f : x y / a >-> r} <-> f is a homomorphism with respect to the
                               relations (fun x y => a) and (fun x y => r).
 *)
Axiom h3 : forall (f : U -> V) (F : U -> U -> Prop) (G : V -> V -> Prop), {homo f : x y / F x y >-> G x y}.
Check h3 : forall (f : U -> V) (F : U -> U -> Prop) (G : V -> V -> Prop) (x y : U), F x y -> G (f x) (f y).

(**
         {homo f : x y / a} <-> f is a homomorphism with respect to the
                               relation expression (fun x y => a).
*)
Axiom h4 : forall (f : U -> U) (F : U -> U -> Prop), {homo f : x y / F x y}.
Check h4 : forall (f : U -> U) (F : U -> U -> Prop) (x y : U), F x y -> F (f x) (f y).

(**
## mono

Fしたものも、fしてからGしたものも、等しい。
 *)
(**
     {mono f : x / a >-> r} <-> f is monotone with respect to projectors
                               (fun x => a) and (fun x => r); if r == R#[#x#]#,
                               this states that R#[#f x#]# = a for all x.
 *)
Axiom m1 : forall (f : U -> V) (F : U -> Prop) (G : V -> Prop), {mono f : x / F x >-> G x}.
Check m1 : forall (f : U -> V) (F : U -> Prop) (G : V -> Prop) (x : U), G (f x) = F x.

(**
           {mono f : x / a} <-> f is monotone with respect to the projector
                               expression (fun x => a).
 *)
Axiom m2 : forall (f : U -> U) (F : U -> Prop), {mono f : x / F x}.
Check m2 : forall (f : U -> U) (F : U -> Prop) (x : U), F (f x) = F x.

(**
   {mono f : x y / a >-> r} <-> f is monotone with respect to relators
                               (fun x y => a) and (fun x y => r).
 *)
Axiom m3 : forall (f : U -> V) (F : U -> U -> Prop) (G : V -> V -> Prop), {mono f : x y / F x y >-> G x y}.
Check m3 : forall (f : U -> V) (F : U -> U -> Prop) (G : V -> V -> Prop) (x y : U), G (f x) (f y) = F x y.

(**
         {mono f : x y / a} <-> f is monotone with respect to the relator
                               expression (fun x y => a).
*)
Axiom m4 : forall (f : U -> U) (F : U -> U -> Prop), {mono f : x y / F x y}.
Check m4 : forall (f : U -> U) (F : U -> U -> Prop) (x y : U), F (f x) (f y) = F x y.

(* END *)
