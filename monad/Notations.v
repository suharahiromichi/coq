(*********************************************************************************************************************************)
(* Notations: miscellaneous notations                                                                                             *)
(*********************************************************************************************************************************)

Require Import Coq.Unicode.Utf8.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Classes.Morphisms.
Require Import Coq.Setoids.Setoid.
Require Setoid.
Export Coq.Unicode.Utf8.
Export Coq.Classes.RelationClasses.
Export Coq.Classes.Morphisms.
Export Coq.Setoids.Setoid.

Set Printing Width 130.       (* Proof General seems to add an extra two columns of overhead *)
Generalizable All Variables.

Reserved Notation "a  ~=>  b"                   (at level 70, right associativity).
Reserved Notation "H ===> C"                    (at level 100).
Reserved Notation "f >>=>> g"                   (at level 45).
Reserved Notation "a ~~{ C }~~> b"              (at level 100).
Reserved Notation "f <--> g"                    (at level 20).
Reserved Notation "! f"                         (at level 2).
Reserved Notation "? f"                         (at level 2).
Reserved Notation "# f"                         (at level 2).
Reserved Notation "f '⁻¹'"                      (at level 1).
Reserved Notation "a ≅ b"                       (at level 70, right associativity).
Reserved Notation "C 'ᵒᴾ'"                      (at level 1).
Reserved Notation "F \ a"                       (at level 20).
Reserved Notation "f >>> g"                     (at level 45).
Reserved Notation "a >>≅>> b"                   (at level 45).
Reserved Notation "a ~~ b"                      (at level 54).
Reserved Notation "a ~> b"                      (at level 70, right associativity).
Reserved Notation "a ≃ b"                       (at level 70, right associativity).
Reserved Notation "a ≃≃ b"                      (at level 70, right associativity).
Reserved Notation "a ~~> b"                     (at level 70, right associativity).
Reserved Notation "F  ~~~> G"                   (at level 70, right associativity).
Reserved Notation "F <~~~> G"                   (at level 70, right associativity).
Reserved Notation "F <~~⊗~~> G"                 (at level 70, right associativity).
Reserved Notation "a ⊗ b"                       (at level 40).
Reserved Notation "a ⊗⊗ b"                      (at level 40).
Reserved Notation "a ⊕  b"                      (at level 40).
Reserved Notation "a ⊕⊕ b"                      (at level 40).
Reserved Notation "f ⋉ A"                       (at level 40).
Reserved Notation "A ⋊ f"                       (at level 40).
Reserved Notation "- ⋉ A"                       (at level 40).
Reserved Notation "A ⋊ -"                       (at level 40).
Reserved Notation "a *** b"                     (at level 40).
Reserved Notation "a ---> b"                    (at level 11, right associativity).
Reserved Notation "a <- b"                      (at level 100, only parsing).
Reserved Notation "a :: b"                      (at level 60, right associativity).
Reserved Notation "a ++ b"                      (at level 60, right associativity).
Reserved Notation "f ○ g"                       (at level 100).
Reserved Notation "f >>>> g"                    (at level 45).
Reserved Notation "a >>⊗>> b"                   (at level 20).
Reserved Notation "f **** g"                    (at level 40).
Reserved Notation "C × D"                       (at level 40).
Reserved Notation "C ×× D"                      (at level 45).
Reserved Notation "C ⁽ºᑭ⁾"                      (at level 1).

Reserved Notation "F -| G"                      (at level 75).
Reserved Notation "'ε'".
Reserved Notation "'η'".

Close Scope nat_scope.  (* so I can redefine '1' *)

Delimit Scope arrow_scope   with arrow.
Delimit Scope biarrow_scope with biarrow.
Delimit Scope garrow_scope  with garrow.

Notation "f ○ g"    := (fun x => f(g(x))).
Notation "a && b"   := (if a then b else false).
Notation "a || b"   := (if a then true else b).

Notation "∀ x y z u q , P" := (forall x y z u q , P)
  (at level 200, q ident, x ident, y ident, z ident, u ident, right associativity)
  : type_scope.
Notation "∀ x y z u q v , P" := (forall x y z u q v , P)
  (at level 200, q ident, x ident, y ident, z ident, u ident, v ident, right associativity)
  : type_scope.
Notation "∀ x y z u q v a , P" := (forall x y z u q v a , P)
  (at level 200, q ident, x ident, y ident, z ident, u ident, v ident, a ident, right associativity)
  : type_scope.
Notation "∀ x y z u q v a b , P" := (forall x y z u q v a b , P)
  (at level 200, q ident, x ident, y ident, z ident, u ident, v ident, a ident, b ident, right associativity)
  : type_scope.
Notation "∀ x y z u q v a b r , P" := (forall x y z u q v a b r , P)
  (at level 200, q ident, x ident, y ident, z ident, u ident, v ident, a ident, b ident, r ident, right associativity)
  : type_scope.
Notation "∀ x y z u q v a b r s , P" := (forall x y z u q v a b r s , P)
  (at level 200, q ident, x ident, y ident, z ident, u ident, v ident, a ident, b ident, r ident, s ident, right associativity)
  : type_scope.
Notation "∀ x y z u q v a b r s t , P" := (forall x y z u q v a b r s t , P)
  (at level 200, q ident, x ident, y ident, z ident, u ident, v ident, a ident, b ident, r ident, s ident, t ident,
    right associativity)
  : type_scope.
