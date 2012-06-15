(*
   （整数群）可換群で、単位元と逆元の一意性を証明する。
   contribs/view/Groups/v8.3/Groups.Groups.html
   を参考に証明は書いた。
*)


Require Import Setoid.                      (* rewrite H at n *)


Inductive  Z : Set :=
| One : Z
| Zero : Z
| Plus : Z -> Z -> Z
| Mult : Z -> Z -> Z
| Neg  : Z -> Z.


Infix "+" := Plus (at level 50, left associativity).
Infix "*" := Mult (at level 40, left associativity).
Notation "--" := Neg (at level 10).
Check Zero + -- One + Zero.


Axiom l_neutral :
  forall x, Zero + x = x.
Axiom r_neutral :
  forall x, x + Zero = x.
Axiom l_sym :
  forall x, (-- x) + x = Zero.
Axiom r_sym :
  forall x, x + (-- x) = Zero.
Axiom assoc :
  forall x y z, x + (y + z) = x + y + z.


Lemma solve_equation :
  forall x y : Z, x + y = Zero -> y = -- x.
Proof.
  intros x y H.
  transitivity (Zero + y).
  symmetry.
  apply l_neutral.


  transitivity (-- x + (x + y)).
  transitivity ((-- x + x) + y).
  rewrite (l_sym x).
  apply refl_equal.


  apply sym_eq.
  apply assoc.
  
  rewrite H.
  apply r_neutral.
Qed.


Lemma ssx : forall x : Z, x = -- (-- x).
Proof.
  intro x.
  apply solve_equation.
  apply l_sym.
Qed.


Variable a : Z.
Definition onto (f : Z -> Z) := forall y : Z, {x : Z | f x = y}.
(*
   Hypothesis o_onto_r : forall x : Z, onto (fun y : Z => x + y).
   Hypothesis o_onto_l : forall x : Z, onto (fun y : Z => y + x).
*)
Axiom o_onto_r :
  forall a y, {x : Z | a + x = y}.
Axiom o_onto_l :
  forall a y, {x : Z | x + a = y}.


Lemma Ea : {ea : Z | a + ea = a}.
Proof.
  case (o_onto_r a a).
  intros x H.
  exists x.
  exact H.
Qed.


Lemma E'a : {e'a : Z | e'a + a = a}.
Proof.
  case (o_onto_l a a).
  intros x H.
  exists x.
  exact H.
Qed.


Definition Zero' := let (Zero', _) := E'a in Zero'.


Lemma e'_l_neutral : forall x, Zero' + x = x.
Proof.
  unfold Zero'.
  case E'a.
  intros e'0 eg x.
  case (o_onto_r a x).
  intros u eg'.
  rewrite <- eg'.
  rewrite (assoc e'0).
  rewrite eg.
  apply refl_equal.
Qed.


Lemma e_eq_e' : Zero = Zero'.
Proof.
  transitivity (Zero' + Zero).
  symmetry.
  apply e'_l_neutral.
  apply r_neutral.
Qed.


Lemma lsym : forall x : Z, {y : Z | y + x = Zero}.
Proof.
  intro.
  case (o_onto_l x Zero).
  intros u H.
  exists u.
  apply H.
Qed.


Lemma rsym : forall x : Z, {y : Z | x + y = Zero}.
Proof.
  intros.
  case (o_onto_r x Zero).
  intros u H.
  exists u.
  apply H.
Qed.


Definition Neg' (x : Z) := let (y, _) return Z := rsym x in y.


Lemma s_eq_s' : forall x : Z, -- x = Neg' x.
Proof.
  intro x.
  unfold Neg'.
  case (rsym x).
  intros y eg.
  transitivity (-- x).
  apply refl_equal.
  apply sym_eq.
  apply solve_equation.
  apply eg.
Qed.


(* END *)