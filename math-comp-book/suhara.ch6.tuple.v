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

Structure tuple_of : Type := Tuple {tval :> seq T; _ : size tval == n}.

Canonical tuple_subType := Eval hnf in [subType for tval].

End Def.


(**
## eqType
 *)

Section EqTuple.

Variables (n : nat) (T : eqType).

Definition tuple_eqMixin := Eval hnf in [eqMixin of n.-tuple T by <:].
Canonical tuple_eqType := Eval hnf in EqType (n.-tuple T) tuple_eqMixin.

Canonical tuple_predType :=
  Eval hnf in mkPredType (fun t : n.-tuple T => mem_seq t).

(*
Lemma memtE (t : n.-tuple T) : mem t = mem (tval t).
Proof. by []. Qed.
*)
Lemma mem_tnth i (t : n.-tuple T) : tnth t i \in t.
Proof. by rewrite mem_nth ?size_tuple. Qed.

Lemma memt_nth x0 (t : n.-tuple T) i : i < n -> nth x0 t i \in t.
Proof. by move=> i_lt_n; rewrite mem_nth ?size_tuple. Qed.

Lemma tnthP (t : n.-tuple T) x : reflect (exists i, x = tnth t i) (x \in t).
Proof.
apply: (iffP idP) => [/(nthP x)[i ltin <-] | [i ->]]; last exact: mem_tnth.
by rewrite size_tuple in ltin; exists (Ordinal ltin); rewrite (tnth_nth x).
Qed.

Lemma seq_tnthP (s : seq T) x : x \in s -> {i | x = tnth (in_tuple s) i}.
Proof.
move=> s_x; pose i := index x s; have lt_i: i < size s by rewrite index_mem.
by exists (Ordinal lt_i); rewrite (tnth_nth x) nth_index.
Qed.

End EqTuple.


(**
## choiceType

Codomain が choice可能 なら、finfunはchoice可能である。
 *)

Definition tuple_choiceMixin n (T : choiceType) :=
  [choiceMixin of n.-tuple T by <:].

Canonical tuple_choiceType n (T : choiceType) :=
  Eval hnf in ChoiceType (n.-tuple T) (tuple_choiceMixin n T).

(**
## countType

Codomain が countablee なら、finfunはcountableである。
 *)

Definition tuple_countMixin n (T : countType) :=
  [countMixin of n.-tuple T by <:].

Canonical tuple_countType n (T : countType) :=
  Eval hnf in CountType (n.-tuple T) (tuple_countMixin n T).

Canonical tuple_subCountType n (T : countType) :=
  Eval hnf in [subCountType of n.-tuple T].

(**
## finType

Codomain が finType なら、finfunはfinTypeである。
 *)

Module Type FinTupleSig.
Section FinTupleSig.
Variables (n : nat) (T : finType).
Parameter enum : seq (n.-tuple T).
Axiom enumP : Finite.axiom enum.
Axiom size_enum : size enum = #|T| ^ n.
End FinTupleSig.
End FinTupleSig.

Module FinTuple : FinTupleSig.
Section FinTuple.
Variables (n : nat) (T : finType).

Definition enum : seq (n.-tuple T) :=
  let extend e := flatten (codom (fun x => map (cons x) e)) in
  pmap insub (iter n extend [::[::]]).

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

Lemma size_enum : size enum = #|T| ^ n.
Proof.
rewrite /= cardE size_pmap_sub; elim: n => //= m IHm.
rewrite expnS /codom /image_mem; elim: {2 3}(fintype.enum T) => //= x e IHe.
by rewrite count_cat {}IHe count_map IHm.
Qed.

End FinTuple.

Section UseFinTuple.

Variables (n : nat) (T : finType).

Canonical tuple_finMixin := Eval hnf in FinMixin (@FinTuple.enumP n T).
Canonical tuple_finType := Eval hnf in FinType (n.-tuple T) tuple_finMixin.
Canonical tuple_subFinType := Eval hnf in [subFinType of n.-tuple T].

Lemma card_tuple : #|{:n.-tuple T}| = #|T| ^ n.
Proof. by rewrite [#|_|]cardT enumT unlock FinTuple.size_enum. Qed.

(*
Lemma enum_tupleP (A : pred T) : size (enum A) == #|A|.
Proof. by rewrite -cardE. Qed.
Canonical enum_tuple A := Tuple (enum_tupleP A).

Definition ord_tuple : n.-tuple 'I_n := Tuple (introT eqP (size_enum_ord n)).
Lemma val_ord_tuple : val ord_tuple = enum 'I_n. Proof. by []. Qed.

Lemma tuple_map_ord U (t : n.-tuple U) : t = [tuple of map (tnth t) ord_tuple].
Proof. by apply: val_inj => /=; rewrite map_tnth_enum. Qed.

Lemma tnth_ord_tuple i : tnth ord_tuple i = i.
Proof.
apply: val_inj; rewrite (tnth_nth i) -(nth_map _ 0) ?size_tuple //.
by rewrite /= enumT unlock val_ord_enum nth_iota.
Qed.
 *)

End UseFinTuple.
 

(* END *)
