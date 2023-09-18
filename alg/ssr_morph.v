From mathcomp Require Import all_ssreflect.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(**
coq/theories/ssr/ssrfun.v   (new)
mathcomp/ssreflect/ssrfun.v (old)

Morphisms for functions and relations:
*)

Variable U W V : Type.
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

(* END *)
