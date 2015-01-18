Require Import ssreflect ssrbool ssrnat ssrfun.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** 
Exercise 7.2 Partially-ordered sets
*)

Module POSETDef.
(**
Mixinの定義
*)
  Record mixin_of (T : Type) :=
    Mixin
      {
        valid_op : T -> bool;               (* 必要か？ *)
        rel_op : T -> T -> bool;
        refl (x : T) : rel_op x x;
        asym (x y : T) : rel_op x y -> rel_op y x -> x = y;
        trans (y x z : T) : rel_op x y -> rel_op y z -> rel_op x z
      }.
  
(**
Packの定義
*)
  Section Packing.
    Structure pack_type : Type :=
      Pack {
          type : Type;
          _ : mixin_of type
        }.
    Local Coercion type : pack_type >-> Sortclass.
    
    Variable cT: pack_type.
    Definition poset_struct : mixin_of cT := (* Coercion cT *)
      let: Pack _ c := cT return mixin_of cT in c.
    Definition valid := valid_op poset_struct.
    Definition rel := rel_op poset_struct.
  End Packing.
  
(**
Exports の宣言
*)    
  Module Exports.
    Notation poset := pack_type.
    Notation POSETMixin := Mixin.
    Notation POSET T m := (@Pack T m).
    Notation "x <== y" := (rel x y) (at level 70, no associativity).
    (* rel_op ではない！ *)
    Notation valid := valid.
    Coercion type : pack_type >-> Sortclass.

    Section POSETLemmas.
      Variable T : poset.
      
      Lemma poset_refl (x : T) : x <== x.
      Proof.
        case: T x => tp [rel Hv Href Hasym Htrans x].
        by apply: Href.
      Qed.
      
      Lemma poset_asym (x y : T) : x <== y -> y <== x -> x = y.
      Proof.
        case: T x y => tp [rel Hv Href Hasym Htrans x y].
        by apply Hasym.
      Qed.
      
      Lemma poset_trans (y x z : T) : x <== y -> y <== z -> x <== z.
      Proof.
        case: T x y z => tp [rel Hv Href Hasym Htrans x y z].
        by apply Htrans.
      Qed.
    End POSETLemmas.
  End Exports.
End POSETDef.
Export POSETDef.Exports.                    (* Exportsをexportする。 *)

Check poset : Type.

Check POSETMixin.
Check leqnn : forall n : nat, n <= n.
Lemma eqn_leq' : forall m n, m <= n -> n <= m -> m = n.
Proof.
  move=> m n.
  elim: m n => [|m IHm] [|n] //.
  move=> H1 H2; congr (_ .+1); move: H1 H2.
  by apply (IHm n).
Qed.
Check leq_trans : forall n m p : nat, m <= n -> n <= p -> m <= p.
Definition natPOSETMixin :=
  POSETMixin
    (fun _ => id true)                      (* valid *)
    leqnn                                   (* ref *)
    eqn_leq'                                (* asym *)
    leq_trans.                              (* trans *)

Definition NatPOSET := POSET nat natPOSETMixin.
Canonical natPOSET := NatPOSET.
Print Canonical Projections.                (* nat <- POSETDef.type ( natPOSET ) *)

Section PosetExamples.
  Variables x y z : nat.
  
  Check POSETDef.rel_op : forall T : Type, POSETDef.mixin_of T -> T -> T -> bool.
  Check POSETDef.rel : forall cT : poset, cT -> cT -> bool.
  About "_ <== _".                          (* POSETDef.rel。 rel_op ではない！ *)

  Goal x <== x.
  Proof.
    by apply: poset_refl.
  Qed.

  Goal x <== y -> y <== x -> x = y.
  Proof.
    by apply: poset_asym.
  Qed.
  
  Goal x <== y -> y <== z -> x <== z.
  Proof.
    by apply: poset_trans.
  Qed.
End PosetExamples.
  
(* END *)
