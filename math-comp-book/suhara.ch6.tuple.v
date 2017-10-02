(**
tuple_eqType, tuple_choiceType, tuple_countType, tuple_finType を求める。
 *)

From mathcomp Require Import all_ssreflect.
From mathcomp Require Import perm.

(**
## subType
 *)

Section Def.

Variables (n : nat) (T : Type).

Structure tuple_of : Type :=
  Tuple {tval :> seq T; _ : size tval == n}.

Canonical tuple_subType :=
  Eval hnf in [subType for tval].

End Def.

Notation "n .-tuple" := (tuple_of n)
  (at level 2, format "n .-tuple") : type_scope.

Notation "{ 'tuple' n 'of' T }" := (n.-tuple T : predArgType)
  (at level 0, only parsing) : form_scope.


(**
## eqType
 *)

Section EqTuple.

Variables (n : nat) (T : eqType).

Definition tuple_eqMixin := Eval hnf in [eqMixin of n.-tuple T by <:].
Canonical tuple_eqType : eqType := Eval hnf in EqType (n.-tuple T) tuple_eqMixin.

End EqTuple.

(**
## choiceType

Codomain が choice可能 なら、finfunはchoice可能である。
 *)

Definition tuple_choiceMixin n (T : choiceType) :=
  [choiceMixin of n.-tuple T by <:].

Canonical tuple_choiceType n (T : choiceType) : choiceType :=
  Eval hnf in ChoiceType (n.-tuple T) (tuple_choiceMixin n T).

(**
## countType

Codomain が countablee なら、finfunはcountableである。
 *)

Definition tuple_countMixin n (T : countType) :=
  [countMixin of n.-tuple T by <:].

Canonical tuple_countType n (T : countType) : countType :=
  Eval hnf in CountType (n.-tuple T) (tuple_countMixin n T).

Canonical tuple_subCountType n (T : countType) :=
  Eval hnf in [subCountType of n.-tuple T].

(**
## finType

Codomain が finType なら、finfunはfinTypeである。
 *)

Section FinTuple.

Variables (n : nat) (T : finType).

Definition enum : seq (n.-tuple T) :=
  let extend e := flatten (codom (fun x => map (cons x) e)) in
  pmap insub (iter n extend [::[::]]).

Print Finite.axiom.
(* 
Finite.axiom = 
fun (T : eqType) (e : seq T) => forall x : T, (count_mem x) e = 1
     : forall T : eqType, seq T -> Prop
 *)

Lemma enumP : Finite.axiom enum.
Proof.
  case=> /= t t_n; rewrite -(count_map _ (pred1 t)) (pmap_filter (@insubK _ _ _)).
  rewrite count_filter -(@eq_count _ (pred1 t)) => [|s /=]; last first.
    by rewrite isSome_insub; case: eqP=> // ->.
    elim: n t t_n => [|m IHm] [|x t] //= {IHm}/IHm; move: (iter m _ _) => em IHm.
    transitivity (x \in T : nat); rewrite // -mem_enum codomE.
    elim: (fintype.enum T)  (enum_uniq T) => //= y e IHe /andP[/negPf ney].
    rewrite count_cat count_map inE /preim /= {1}/eq_op /= eq_sym => /IHe->.
      by case: eqP => [->|_]; rewrite ?(ney, count_pred0, IHm).
Qed.

Canonical tuple_finMixin :=
  Eval hnf in FinMixin FinTuple.enumP.

Canonical tuple_finType : finType :=
  Eval hnf in FinType (n.-tuple T) tuple_finMixin.

Canonical tuple_subFinType :=
  Eval hnf in [subFinType of n.-tuple T].

End FinTuple.
 
(* END *)
