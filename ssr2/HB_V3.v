(* Accompanying material to https://hal.inria.fr/hal-02478907 *)
From Coq Require Import ssreflect ssrfun ZArith.
From HB Require Import structures.

Declare Scope hb_scope.
Delimit Scope hb_scope with G.
Open Scope hb_scope.

(* Bottom mixin in Fig. 1. *)
HB.mixin Record Monoid_of_Type M := {
  zero : M;
  add : M -> M -> M;
  addrA : associative add;
  add0r : left_id zero add;
  addr0 : right_id zero add;
}.
HB.structure Definition Monoid := { M of Monoid_of_Type M }.
Notation "0" := zero : hb_scope.
Infix "+" := (@add _) : hb_scope.

(* Bottom right mixin in Fig. 1. *)
HB.mixin Record AbelianGroup_of_Monoid A of Monoid A := {
  opp : A -> A;
  addrC : commutative (add : A -> A -> A);
  addNr : left_inverse zero opp add;
}.
HB.structure Definition AbelianGroup := { A of Monoid A & AbelianGroup_of_Monoid A }.
Notation "- x" := (@opp _ x) : hb_scope.
Notation "x - y" := (x + - y) : hb_scope.

(* Top right mixin in Fig. 1. *)
HB.mixin Record Ring_of_AbelianGroup R of AbelianGroup R := {
  one : R;
  mul : R -> R -> R;
  mulrA : associative mul;
  mul1r : left_id one mul;
  mulr1 : right_id one mul;
  mulrDl : left_distributive mul add;
  mulrDr : right_distributive mul add;
}.
HB.about Ring_of_AbelianGroup.
(*
HB: Ring_of_AbelianGroup requires the following mixins:
    - Monoid_of_Type
    - AbelianGroup_of_Monoid
HB: Ring_of_AbelianGroup provides the following mixins:
    - Ring_of_AbelianGroup            ← mixin だと定義される。factory だと定義されない。
*)

HB.structure Definition Ring := { R of AbelianGroup R & Ring_of_AbelianGroup R }.
Notation "1" := one : hb_scope.
Infix "*" := (@mul _) : hb_scope.

(* これは最後のexerciseで使う。 *)
(* 最後に証明してもよい。 *)
Lemma addrN {R : AbelianGroup.type} : right_inverse (zero : R) opp add.
Proof. by move=> x; rewrite addrC addNr. Qed.

(* Left factory in Fig. 1. *)
(* factory と builder は一体であり、 *)
(* 定義されるのは、Ring_of_Monoid である。 *)
HB.factory Record Ring_of_Monoid R of Monoid R := {
  one : R;
  opp : R -> R;
  mul : R -> R -> R;
  addNr : left_inverse zero opp add;
  addrN : right_inverse zero opp add;
  mulrA : associative mul;
  mul1r : left_id one mul;
  mulr1 : right_id one mul;
  mulrDl : left_distributive mul add;
  mulrDr : right_distributive mul add;
}.
HB.about Ring_of_Monoid.
(*
HB: Ring_of_Monoid requires the following mixins:
    - Monoid_of_Type
HB: Ring_of_Monoid provides the following mixins:
*)
(*                                  vvvvvvvvvvvvvv *)
HB.builders Context (R : Type) (f : Ring_of_Monoid R). (* f は _ でもよい。 *)
  Check R : Type.
  Check f : Ring_of_Monoid R.
  
  (* Ring_of_Monoid に addrC がないので、証明する。 *)
  Lemma addrCx : commutative (add : R -> R -> R).
  Proof.
  have innerC (a b : R) : a + b + (a + b) = a + a + (b + b).
    by rewrite -[a+b]mul1r -mulrDl mulrDr !mulrDl !mul1r.
  have addKl (a b c : R) : a + b = a + c -> b = c.
    apply: can_inj (add a) (add (opp a)) _ _ _.
    by move=> x; rewrite addrA addNr add0r.
  have addKr (a b c : R) : b + a = c + a -> b = c.
    apply: can_inj (add ^~ a) (add ^~ (opp a)) _ _ _.
    by move=> x; rewrite /= -addrA addrN addr0.
  move=> x y; apply: addKl (x) _ _ _; apply: addKr (y) _ _ _.
  by rewrite -!addrA [in RHS]addrA innerC !addrA.
  Qed.
  
  (* Builder to the bottom right mixin. *)
  (* テキストの文法だと、Rに属性を追加することがよく判る。 *)
  Definition to_AbelianGroup_of_Monoid := AbelianGroup_of_Monoid.Build R opp addrCx addNr.
  HB.instance R to_AbelianGroup_of_Monoid.
(*
  HB.instance
  Definition to_AbelianGroup_of_Monoid :=
    AbelianGroup_of_Monoid.Build R opp addrCx addNr.
 *)
  (* 実際の書き方では、定義本体さえ不要である。 *)
(*
  HB.instance Definition _ := AbelianGroup_of_Monoid.Build R opp addrCx addNr.
*)  
  (* AbelianGroup_of_Monoid の addrC と addNr に、Ring_of_Monoid での証明を与える。 *)
  (* addrC は直前の証明を使用する。addNr はRing_of_Monoid の定義を使用する。 *)
  
  (* Builder to the top right mixin. *)
  HB.instance
  Definition to_Ring_of_AbelianGroup := Ring_of_AbelianGroup.Build R one mul
    mulrA mul1r mulr1 mulrDl mulrDr.
  
HB.end.                                     (* Contextの終わり。 *)
(* HB.instance がないとエラーになる。 *)
(* addrC は使えなくなる。 *)

HB.about Ring_of_Monoid.
(*
HB: Ring_of_Monoid requires the following mixins:
    - Monoid_of_Type
HB: Ring_of_Monoid provides the following mixins:
    - Ring_of_AbelianGroup      ここで定義
    - AbelianGroup_of_Monoid    ここで定義
*)

(********)
(* TEST *)
(********)
Print Monoid.type.
(* Monoid.type  :=  { sort : Type;  ... }                                *)
Check @add.
(* add          :   forall M : Monoid.type, M -> M -> M                  *)
Check @addNr.
(* addNr        :   forall R : AbelianGroup.type, left_inverse 0 opp add *)
Check @addrC. (* is still an axiom of abelian groups                     *)
(* addrC        :   forall R : AbelianGroup.type, commutative add        *)

(*
HB.instance
Definition Z_Monoid_axioms : Monoid_of_Type Z :=
   Monoid_of_Type.Build Z 0%Z Z.add Z.add_assoc Z.add_0_l Z.add_0_r.
*)
(* テキスト *)
(* テキストの文法だと、Zに属性を追加することがよく判る。 *)
(*
Definition Z_Monoid_axioms : Monoid_of_Type Z :=
   Monoid_of_Type.Build Z 0%Z Z.add Z.add_assoc Z.add_0_l Z.add_0_r.
HB.instance Z Z_Monoid_axioms.
*)
(* 最新 *)
HB.instance Definition _ : Monoid_of_Type Z :=
   Monoid_of_Type.Build Z 0%Z Z.add Z.add_assoc Z.add_0_l Z.add_0_r.

HB.instance
Definition Z_Ring_axioms : Ring_of_Monoid Z :=
  Ring_of_Monoid.Build Z 1%Z Z.opp Z.mul
    Z.add_opp_diag_l Z.add_opp_diag_r Z.mul_assoc Z.mul_1_l Z.mul_1_r
    Z.mul_add_distr_r Z.mul_add_distr_l.

(* HB.instance Definition to_Ring_of_AbelianGroup が無いと、
   Z に Ring の属性が付かないためエラーになる。 *)
Check forall (n : Z), n * 1 = n.
Lemma exercise (m n : Z) : (n + m) - n * 1 = m.
Proof.
  Check @mulr1 : forall s : Ring.type, right_id 1 mul. (* 公理 *)
  Check @addrC : forall s : AbelianGroup.type, commutative add. (* 公理、証明した補題ではない。 *)
  Check @addrA : forall s : Monoid.type, associative add. (* 公理 *)
  Check @addrN : forall R : AbelianGroup.type, right_inverse 0 opp add. (* 証明した補題 *)
  Check @addr0 : forall s : Monoid.type, right_id 0 add. (* 公理 *)
  by rewrite mulr1 (addrC n) -(addrA m) addrN addr0.     (* 公理 *)
Qed.

(* 広義のfactory *)
(* mixin だと自分自身が provide される。     provides *)
HB.about Monoid_of_Type.                  (* Monoid_of_Type *)
HB.about AbelianGroup_of_Monoid.          (* AbelianGroup_of_Monoid *)
HB.about Ring_of_AbelianGroup.            (* Ring_of_AbelianGroup *)
(* factory で定義だと自分はprovide せず、builders で定義されたものがprovideされる。 *)
HB.about Ring_of_Monoid.                  (* Ring_of_AbelianGroup, AbelianGroup_of_Monoid *)

(* strucure *)
(* これは、structure定義で決まり、builderでは変わらない。 *)
(*                           mixin *)
HB.about Monoid.          (* Monoid_of_Type *)
HB.about AbelianGroup.    (* Monoid_of_Type, AbelianGroup_of_Monoid *)
HB.about Ring. (* Monoid_of_Type, AbelianGroup_of_Monoid, Ring_of_AbelianGroup *)

(* canonically equipped *)
(*                                             structure *)
(* 広義のfactoryを使って定義するが、属性としては structure を持つ。 *)
HB.about Z.                                 (* Ring, AbelianGroup, Monoid *)

(*
Z は、Monoid_of_Type と Ring_of_Monoid から作るが、
後者が build で、AbelianGroup_of_Monoid と Ring_of_AbelianGroup をprovide するので、
全体として、Ring と AbelianGroup のstructureを持つことになる。
*)

(* END *)
