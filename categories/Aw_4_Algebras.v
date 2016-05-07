(******************************************************************************)
(* Chapter 4: Algebras                                                        *)
(*                                                                            *)
(*   This formalizes for arbitrary algebras what Awodey does for groups in    *)
(*   chapter 4                                                                *)
(******************************************************************************)

Generalizable All Variables.
Require Import Notations.

(* very handy *)
(*
Fixpoint listOfTypesToType (args:list Type)(ret:Type) : Type :=
  match args with
  | nil  => ret
  | a::b => a -> listOfTypesToType b ret
  end.
*)
(*
Section Algebras.

Local Notation "a :: b" := (vec_cons a b).
Local Notation "[]"     := (vec_nil).
Local Notation "[ a ]"  := (a::[]).

Structure Signature : Type :=
{ sig_sort       : Type
; sig_op         : Type
; sig_arity_len  :           sig_op -> nat
; sig_result     :           sig_op -> sig_sort
; sig_arity      : forall op:sig_op, vec sig_sort (sig_arity_len op)
}.

Section DerivedOperations.

  Context (sig:Signature).

  Structure Algebra : Type :=
  { alg_carrier : sig_sort sig -> Type
  (*; alg_op      : forall op:sig_op sig, listOfTypesToType (map alg_carrier (sig_arity sig op)) (alg_carrier (sig_result sig op))*)
  (*FIXME*)
  }.

  (* the "arity" of an operation in a multi-sorted signature is a finite list of sorts *)
  Definition Arity := { n:nat & vec (sig_sort sig) n }.
  Definition mkArity {n:nat} : vec (sig_sort sig) n -> Arity.
    intros v; exists n; auto.
    Defined.
  Definition length : Arity -> nat.
    intro a; destruct a; auto.
    Defined.
    
  Definition arity_get (n:nat)(a:Arity)(pf:lt n (length a)) : sig_sort sig.
    destruct a.
    refine (@vec_get (sig_sort sig) _ v n pf).
    Defined.

  (* See Bergman, Invitation to Universal Algebra, Def 8.9.1 *)
  Inductive DerivedOperation : Arity -> sig_sort sig -> Type :=
  | do_op         : forall op:sig_op sig, DerivedOperation (mkArity (sig_arity sig op)) (sig_result sig op)
  | do_projection : forall (a:Arity)(n:nat)(pf:lt n (length a)), DerivedOperation a (arity_get n a pf)
  | do_compose    : forall n a b c, VecOfDerivedOperations n a b -> DerivedOperation (mkArity b) c -> DerivedOperation a c
  with VecOfDerivedOperations : forall n:nat, Arity -> vec (sig_sort sig) n -> Type :=
  | vodo_nil      : forall a, VecOfDerivedOperations 0 a []
  | vodo_cons     : forall a b n v, DerivedOperation a b -> VecOfDerivedOperations n a v -> VecOfDerivedOperations (S n) a (b::v).

  (* an identity is a pair of derived operations, WLOG having the same arity *)
  Record Identity :=
  { id_arity  : Arity
  ; id_result : sig_sort sig
  ; id_op1    : DerivedOperation id_arity id_result
  ; id_op2    : DerivedOperation id_arity id_result
  }.

  Definition Relations := list Identity.

  Inductive Satisfies : Algebra -> Relations -> Prop :=. 

End DerivedOperations.

(* TO DO: an algebra of signature [s] in monoidal category [c] *)
(* FIXME: generators-and-relations *)
(* see also example 9.36 *)

(*
An Algebra-Sorted-Signature consists of an algebra of sorts and a
collection of operations such that each operations's arity is a list
of elements of the sort algebra.
*)
(*
Structure AlgebraSortedSignature `(relations_on_sort_algebra : Relations signature_of_sort_algebra) : Type :=
{ algss_sort_algebra : Algebra signature_of_sort_algebra relations_on_sort_algebra
}.

Structure AlgebraSortedAlgebra {sig}{rel}(algss:@AlgebraSortedSignature sig rel) : Type :=
{
}.
Definition AlgebraSortedSignature_is_Signature : forall sig rel, AlgebraSortedSignature sig rel -> Signature sig rel.
  Defined.
  Coercion AlgebraSortedSignature_is_Signature : AlgebraSortedSignature >-> Signature.
*)

(* algebraically axiomatized monoidal categories *)
Record AMCat :=
{ amcat_ob                   : Type
; amcat_I                    : amcat_ob
; amcat_hom                  : amcat_ob -> amcat_ob -> Type            where "a ~> b"  := (amcat_hom a b)
; amcat_oprod                : amcat_ob -> amcat_ob -> amcat_ob        where "a ⊗  b"  := (amcat_oprod a b)

; amcat_eqv                  : ∀ a b,     a~>b -> a~>b -> Prop         where "f ~~  g" := (amcat_eqv _ _ f g)
; amcat_eqv_eqv              : ∀ a b,     Equivalence (amcat_eqv a b)

; amcat_id                   : ∀ a,       a~>a
; amcat_comp                 : ∀ a b c,   a~>b -> b~>c -> a~>c         where "f >>> g" := (amcat_comp _ _ _ f g)
; amcat_mprod                : ∀ a b c d, a~>b -> c~>d -> (a⊗c)~>(b⊗d) where "a ×  b"  := (amcat_mprod _ _ _ _ a b)
                                                                         and "f ⋉ A"   := (f × (amcat_id A))
                                                                         and "A ⋊ f"   := ((amcat_id A) × f)

; amcat_comp_respects        : ∀ a b c,   Proper (amcat_eqv a b ==> amcat_eqv b c ==> amcat_eqv a c) (amcat_comp _ _ _)
; amcat_left_identity        : forall `(f:a~>b),  (amcat_id a >>> f) ~~ f
; amcat_right_identity       : forall `(f:a~>b), f >>> amcat_id b ~~ f
; amcat_associativity        : forall `(f:a~>b)`(g:b~>c)`(h:c~>d), (f >>> g) >>> h ~~ f >>> (g >>> h)

; amcat_mprod_preserves_id   : forall a b, (amcat_id a) × (amcat_id b) ~~ (amcat_id (a⊗b))
; amcat_mprod_preserves_comp : forall `(f1:a1~>b1)`(g1:b1~>c1)`(f2:a2~>b2)`(g2:b2~>c2), (f1>>>g1)×(f2>>>g2) ~~ (f1×f2)>>>(g1×g2)

; amcat_cancell              : ∀ a,       amcat_I⊗a ~> a
; amcat_cancelr              : ∀ a,     a⊗amcat_I   ~> a
; amcat_assoc                : ∀ a b c,    (a⊗b)⊗c ~> a⊗(b⊗c)
; amcat_uncancell            : ∀ a,              a ~> amcat_I⊗a
; amcat_uncancelr            : ∀ a,              a ~> a⊗amcat_I  
; amcat_unassoc              : ∀ a b c,    a⊗(b⊗c) ~> (a⊗b)⊗c
; amcat_cancell_uncancell    : ∀ a,     amcat_uncancell a   >>> amcat_cancell a   ~~ amcat_id a
; amcat_cancell_uncancelr    : ∀ a,     amcat_uncancelr a   >>> amcat_cancelr a   ~~ amcat_id a
; amcat_assoc_unassoc        : ∀ a b c, amcat_unassoc a b c >>> amcat_assoc _ _ _ ~~ amcat_id _
; amcat_cancell_natural      : forall `(f:a~>b),     amcat_uncancell _ >>> (amcat_id _ × f) ~~ f >>> amcat_uncancell _
; amcat_cancelr_natural      : forall `(f:a~>b),     amcat_uncancelr _ >>> (f × amcat_id _) ~~ f >>> amcat_uncancelr _
; amcat_assoc_natural        : forall `(f:a1~>b1)`(g:a2~>b2)`(h:a3~>b3),
                                      amcat_assoc _ _ _ >>> (f × (g × h)) ~~ ((f × g) × h) >>> amcat_assoc _ _ _
; amcat_pentagon             : forall a b c d,    amcat_assoc a b c ⋉ d >>> amcat_assoc a _ d >>> a ⋊ amcat_assoc b c d
                                             ~~  amcat_assoc _ c d     >>> amcat_assoc a b _
; amcat_triangle             : forall a b, amcat_cancelr a ⋉ _ ~~ amcat_assoc _ _ _ >>> _ ⋊ amcat_cancell b
}.

(* To Do: AMCat is an algebraically-sorted signature *)

(* any given level of the Coq universe hierarchy satisfies the algebraic laws for a monoidal category *)
Definition Coq_AMCat : AMCat.
 refine
 {| amcat_ob        := Type
  ; amcat_I         := unit
  ; amcat_hom       := fun a b => a->b
  ; amcat_oprod     := fun a b => prod a b
  ; amcat_eqv       := fun a b f g => forall q, (f q)=(g q)
  ; amcat_id        := fun a x => x
  ; amcat_comp      := fun a b c f g => g ○ f
  ; amcat_mprod     := fun a b c d f g => fun x => let (x1,x2) := x in ((f x1),(g x2))
  ; amcat_cancell   := fun a     => fun x => let (x1,x2)  := x in x2
  ; amcat_cancelr   := fun a     => fun x => let (x1,x2)  := x in x1
  ; amcat_assoc     := fun a b c => fun x => let (x12,x3) := x in let (x1,x2) := x12 in (x1,(x2,x3))
  ; amcat_uncancell := fun a     => fun x => (tt,x)
  ; amcat_uncancelr := fun a     => fun x => (x,tt)
  ; amcat_unassoc   := fun a b c => fun x => let (x1,x23) := x in let (x2,x3) := x23 in ((x1,x2),x3)
  |}; intros; simpl; auto; try destruct q; auto; try destruct p; auto; try destruct p; auto.
  apply Build_Equivalence; simpl;
      [ unfold Reflexive; intros; auto
      | unfold Symmetric; intros; symmetry; auto
      | unfold Transitive; intros; rewrite H; auto ].
  unfold Proper; unfold respectful; intros; rewrite H; rewrite H0; reflexivity.
  Defined.
  Coercion amcat_ob : AMCat >-> Sortclass.

(* To do: arbitrary algebras internal to an MCat *)

(* hrm, internalization is sort of a (primitive-recursive) operation
   on signatures –- you take a signature for X and produce the signature
   of MCats with an internal X *)

Delimit Scope amcat_scope with amcat.
Open Scope amcat_scope.
Notation "a ~> b"  := (amcat_hom _ a b)            : amcat_scope.
Notation "a ⊗  b"  := (amcat_oprod _ a b)          : amcat_scope.
Notation "f ~~ g"  := (amcat_eqv _ _ _ f g)        : amcat_scope.
Notation "f >>> g" := (amcat_comp _ _ _ _ f g)     : amcat_scope.
Notation "a ×  b"  := (@amcat_mprod _ _ _ _ _ a b) : amcat_scope.
Notation "f ⋉ A"   := (f × (amcat_id _ A))         : amcat_scope.
Notation "A ⋊ f"   := ((amcat_id _ A) × f)         : amcat_scope.
Notation "'I'"     := (amcat_I _)                  : amcat_scope.

(* what we call a category is actually an AMCat-enriched-Cat *)
(*
Record Cat (V:AMCat) :=
{ cat_ob             :   Type
; cat_hom            :   cat_ob -> cat_ob -> V                           where "a ⇒ b"   := (cat_hom a b)
; cat_id             :   ∀ a      , I ~> a ⇒ a
; cat_ecomp          :   ∀ a b c  , (a ⇒ b)⊗(b ⇒ c) ~> (a ⇒ c)
; cat_left_identity  :   ∀ a b    , cat_id a ⋉ (a ⇒ b) >>> cat_ecomp _ _ _ ~~ amcat_cancell _ _
; cat_right_identity :   ∀ a b    , (a ⇒ b) ⋊ cat_id b >>> cat_ecomp _ _ _ ~~ amcat_cancelr _ _
; cat_associativity  :   ∀ a b c d, amcat_unassoc _ _ _ (_ ⇒ _) >>> cat_ecomp _ _ _ ⋉ (c ⇒ d) >>> cat_ecomp _ _ _ ~~
                                                                    (a ⇒ b) ⋊ cat_ecomp _ _ _ >>> cat_ecomp _ _ _
; cat_comp           :=  fun a b c f g => amcat_uncancell V _ >>> (amcat_mprod V I (a⇒ b) I (b⇒ c) f g) >>> cat_ecomp _ _ _
}.

Close Scope amcat_scope.

Delimit Scope cat_scope with cat.
Notation "a ~> b"  := (cat_hom _ a b)            : cat_scope.
Notation "f ~~ g"  := (@amcat_eqv _ _ _ f g)     : cat_scope.
Notation "f >>> g" := (@cat_comp _ _ _ _ _ f g)  : cat_scope.
Close Scope cat_scope.





(* a monoidal category enriched in an AMCat *)
Record MCat (V:AMCat) :=
{ mcat_cat : Cat V
(* plus monoidal structure *)
}.
(*Notation "a ⊗  b"  := (amcat_oprod _ a b)         : cat_scope.
Notation "a ×  b"  := (amcat_mprod _ _ _ _ _ a b) : cat_scope.
Notation "f ⋉ A"   := (f × (amcat_id _ A))        : cat_scope.
Notation "A ⋊ f"   := ((amcat_id A) × f)          : cat_scope.
Notation "'I'"     := (amcat_I _)                 : cat_scope.*)


(*
 * Given an MCat we can derive an AMCat, which can then in turn have
 * internal stuff –- this is essentially the first externalization
 * functor (I₀).
 *)
(*
Definition AMCat_from_MCat `(C:MCat V) : AMCat.
  Defined.
*)

(* need CategoryWithProducts, then use a category enriched in a category with products to get products of categories *)
(* it's really only functors we need to change: get rid of the general notion, and allow only EFunctors *)
(* then we can more easily do functor-categories! *)

*)
End Algebras.
*)

