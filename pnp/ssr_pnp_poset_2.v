From mathcomp Require Import ssreflect ssrbool ssrnat ssrfun.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** 
Exercise 7.2 Partially-ordered sets

Mathcomp ライブラリに命名規則をあわせた。
 (* see. ssr_pnp_deprecords_2.v *)
*)

Module Poset.
  Module POSET.
(**
Mixinの定義
*)
    Record mixin_of (T : Type) :=
      Mixin {
          valid : T -> bool;
          rel : T -> T -> bool;
          refl (x : T) : rel x x;
          asym (x y : T) : rel x y -> rel y x -> x = y;
          trans (y x z : T) : rel x y -> rel y z -> rel x z
        }.
    Notation class_of := mixin_of (only parsing). (* not used *)    
(**
Packの定義
*)
    Section ClassDef.
      Structure type : Type :=
        Pack {
            sort : Type;
            m : mixin_of sort
          }.
      Local Coercion sort : type >-> Sortclass.
      Print Graph.                          (* [sort] : type >-> Sortclass *)
      
      Variable cT: type.
      Definition poset_struct : mixin_of cT := (* Coercion cT *)
        let: Pack _ c := cT return mixin_of cT in c.
      Definition valid_op := valid poset_struct.
      Definition rel_op := rel poset_struct.
    End ClassDef.
    
(**
Exports の宣言
*)    
    Module Exports.
      Notation posetMixin := mixin_of.
      Notation posetType := type.
      Notation PosetMixin := Mixin.
      Notation PosetType T m := (@Pack T m).
      
      Notation "x <== y" := (rel_op x y) (at level 70, no associativity).
      (* rel ではない！ *)
      Notation Rel := rel_op.
      Notation Valid := valid_op.
      Coercion sort : type >-> Sortclass.

      Section POSETLemmas.
        Variable T : posetType.
        
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
  End POSET.
  Export POSET.Exports.                    (* Exportsをexportする。 *)
  
  Check leqnn : forall n : nat, n <= n.
  Lemma eqn_leq' : forall m n, m <= n -> n <= m -> m = n.
  Proof.
    move=> m n.
    elim: m n => [|m IHm] [|n] //.
    move=> H1 H2; congr (_ .+1); move: H1 H2.
      by apply (IHm n).
  Qed.
  Check leq_trans : forall n m p : nat, m <= n -> n <= p -> m <= p.

  Definition nat_posetMixin :=
    PosetMixin
      (fun _ => id true)                    (* valid *)
      leqnn                                 (* ref *)
      eqn_leq'                              (* asym *)
      leq_trans.                            (* trans *)

  Canonical nat_posetType := PosetType nat nat_posetMixin.
  Print Canonical Projections. (* nat <- POSETDef.sort ( nat_posetType ) *)
  
  Section PosetExamples.
    Variables x y z : nat.
    
    Check Rel : forall cT : posetType, cT -> cT -> bool.
    About "_ <== _".                          (* Rel := POSET.rel_op *)
    
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
End Poset.

(* END *)
