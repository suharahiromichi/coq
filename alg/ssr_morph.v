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
