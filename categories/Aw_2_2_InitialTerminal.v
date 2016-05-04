Generalizable All Variables.
Require Import Notations.
Require Import Categories_ch1_3.
Require Import Functors_ch1_4.
Require Import Isomorphisms_ch1_5.

(******************************************************************************)
(* Chapter 2.2: Initial and Terminal Objects                                  *)
(******************************************************************************)

Class InitialObject
`{ C            : Category                         }
 ( initial_obj  : C                                ) :=
{ zero          := initial_obj
; bottom        : forall a,  zero ~> a
; bottom_unique : forall `(f:zero~>a), f ~~ (bottom a)
}.
Notation "? A" := (bottom A)     : category_scope.
Notation "0"   := zero           : category_scope.
Coercion zero : InitialObject >-> ob.
Implicit Arguments InitialObject [[Ob][Hom]].

Class TerminalObject
`{ C             : Category                       }
 ( terminal_obj  : C                              ) :=
{ one         := terminal_obj
; drop        : forall a,  a ~> one
; drop_unique : forall `(f:a~>one), f ~~ (drop a)
}.
Notation "! A" := (drop A)       : category_scope.
Notation "1"   := one            : category_scope.
Coercion one : TerminalObject >-> ob.
Implicit Arguments TerminalObject [[Ob][Hom]].


(* initial objects are unique up to iso *)
Lemma initial_unique_up_to_iso `{C:Category}{io1:C}(i1:InitialObject C io1){io2:C}(i2:InitialObject C io2) : io1 ≅ io2.
  refine {| iso_backward := bottom(InitialObject:=i2) io1 ; iso_forward := bottom(InitialObject:=i1) io2 |}.
  setoid_rewrite (bottom_unique(InitialObject:=i1)); reflexivity.
  setoid_rewrite (bottom_unique(InitialObject:=i2)); reflexivity.
  Qed.

(* terminal objects are unique up to iso *)
Lemma terminal_unique_up_to_iso `{C:Category}{to1:C}(t1:TerminalObject C to1){to2:C}(t2:TerminalObject C to2) : to1 ≅ to2.
  refine {| iso_backward := drop(TerminalObject:=t1) to2 ; iso_forward := drop(TerminalObject:=t2) to1 |}.
  setoid_rewrite (drop_unique(TerminalObject:=t1)); reflexivity.
  setoid_rewrite (drop_unique(TerminalObject:=t2)); reflexivity.
  Qed.

