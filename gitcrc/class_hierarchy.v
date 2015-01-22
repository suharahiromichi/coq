(* 
http://stackoverflow.com/questions/7990301/building-a-class-hierarchy-in-coq
 *)

Class Semigroup {A : Type} (op : A -> A -> A) : Type :=
  {
    op_associative : forall x y z : A, op x (op y z) = op (op x y) z
  }.

Class Monoid `(M : Semigroup) (id : A) : Type :=
  {
    id_ident_left  : forall x : A, op id x = x;
    id_ident_right : forall x : A, op x id = x
  }. 

Class AbelianMonoid `(M : Monoid) : Type :=
  {
    op_commutative : forall x y : A, op x y = op y x
  }.

Class Semiring A mul add `(P : AbelianMonoid A mul) `(M : Monoid A add) :=
  {
  }.

(* END *)
