(* 等式論理 *)

Require Import ssreflect ssrbool ssrnat seq.
Require Import ssrfun.

Section Equational_logic.

  Definition eleq (e1 e2 : bool) : bool :=
    if e1 is true then
      if e2 is true then
        true
      else
        false
    else
      if e2 is true then
        false
      else
        true.

  Definition elne (e1 e2 : bool) : bool :=
    if e1 is true then
      if e2 is true then
        false
      else
        true
    else
      if e2 is true then
        true
      else
        false.
  
  Reserved Notation "b === c" (at level 101, left associativity).
  Notation "b === c" := (eleq b c) : bool_scope.

  Reserved Notation "b =!= c" (at level 101, left associativity).
  Notation "b =!= c" := (elne b c) : bool_scope.

  Check true === true.
  Eval compute in true === true.

  Check true === true === false.
  Eval compute in (true === true === false).

  Check true && true === true.
  Eval compute in true && true === true.

  Check true && true === true || false.
  Eval compute in true && true === true || false.
  
(*
  Inductive reflect2 (P: Prop) : bool -> Set :=
  | ReflectT: P -> reflect2 P true
  | ReflectF: ~P -> reflect2 P false.
*)

  Lemma eqP: forall e1 e2, reflect (e1 = e2) (e1 === e2).
  Proof.
    move=> e1 e2.
    rewrite /eleq.
    case: e1; case: e2.
      by apply ReflectT.
        by apply ReflectF.
          by apply ReflectF.
            by apply ReflectT.
  Qed.

  Lemma eqE: forall e1 e2, (e1 = e2) <-> (e1 === e2).
  Proof.
    move=> e1 e2.
    split.
    (* -> *)
    move=> H. rewrite -H.
    by apply/eqP.
    (* <- *)
    by move/eqP => H.
  Qed.

  Lemma refl_eleq : forall e, (e === e).
  Proof.
    move=> e.
    by apply/eqP.
  Qed.

  Lemma sym_eleq : forall e1 e2,
                     (e1 === e2) = (e2 === e1).
  Proof.
    move=> e1 e2.
      by case: e1.
  Qed.

  Lemma sym_eleq' : forall e1 e2,
                      (e1 === e2) <-> (e2 === e1).
  Proof.
    move=> e1 e2.
    split;
      move/(eqP _ _) => H; by apply/(eqP _ _).
  Qed.

  Lemma assoc_eleq : forall e1 e2 e3, 
                       ((e1 === e2) === e3) = (e1 === (e2 === e3)).
  Proof.
    move=> e1 e2 e3.
    by case: e1; case: e2; case e3.
  Qed.

  (* 推移則 trans (e1 === e2 === e3) = (e1 === e3) は成立しない。 *)

  Lemma detrue_eleq' : forall e1 e2, (true === e1 === e2) = (e1 === e2).
  Proof.
    move=> e1 e2.
    rewrite /eleq.
      by case e1; simpl.
  Qed.
  
  Lemma detrue_eleq : forall e e1 e2,
                        e = true -> (e === e1 === e2) = (e1 === e2).
  Proof.
    move=> e e1 e2 H.
    rewrite H /eleq.
      by case e1; simpl.
  Qed.
  
  Lemma defalse_eleq' : forall e e1 e2,
                          e = false -> (e === e1 === e2) = (~~e1 === e2).
  Proof.
    move=> e e1 e2 H.
    rewrite H /eleq.
    simpl.
      by case e1; simpl.
  Qed.

  Lemma defalse_eleq : forall e e1 e2,
                         e = false -> (e === e1 === e2) = (e1 =!= e2).
  Proof.
    move=> e e1 e2 H.
    rewrite H /eleq /elne.
    simpl.
      by case e1; simpl.
  Qed.

  (* 推移則 trans (e1 === e2 === e3) = (e1 === e3) は成立しない。 *)

  Lemma trans_eleq : forall e1 e2 e3,
                       (e1 === e2 === e2 === e3) = (e1 === e3).
  Proof.
    move=> e1 e2 e3.
    rewrite [_ === e2 === e2]assoc_eleq
            refl_eleq
            [e1 === true]sym_eleq.
      by apply/detrue_eleq.
  Qed.

  (* これは、~~(e1 && e2) = (~~ e1 || ~~ e2) を証明するのだから、
   命題論理の証明で、等式論理の証明とはいえない。 *)
  Goal forall e1 e2,
         ~~ (e1 && e2) === (~~ e1 || ~~ e2).
  Proof.
    move=> e1 e2.
    apply/eqP.
    rewrite /andb /orb.
    case: e1; rewrite //=.
  Qed.

End Equational_logic.


Section Sumbool_Equational_logic.

  Hypothesis bool_eq_dec :
    forall a b : bool, {a = b} + {a <> b}.

  Hypothesis bool_ne_dec :
    forall a b : bool, {a <> b} + {a = b}.

  Definition bool_of_sumbool :
    forall A B : Prop, {A} + {B} -> {e | if e then A else B}.
    intros A B H.
    elim H; intro; [exists true | exists false]; assumption.
  Defined.

  Definition eleqp (e1 e2 : bool) : Prop :=
    e1 = e2.

  Definition eleq_dec :
    (forall (x y : bool), {x = y} + {x <> y}) ->
    forall e1 e2, {eleqp e1 e2} + {~ eleqp e1 e2}.
  Proof.
    move=> H e1 e2.
    elim: (H e1 e2) => H12; [left | right];
                       rewrite /eleqp; assumption.
  Defined.

  Definition elne_dec :
    (forall (x y : bool), {x <> y} + {x = y}) ->
    forall e1 e2, {~ eleqp e1 e2} + {eleqp e1 e2}.
  Proof.
    move=> H e1 e2.
    elim: (H e1 e2) => H12; [left | right];
                       rewrite /eleqp; assumption.
  Defined.

  Definition eleq' (x y : bool) : bool :=
    proj1_sig (bool_of_sumbool _ _ (eleq_dec bool_eq_dec x y)).

  Definition elne' (x y : bool) : bool :=
    proj1_sig (bool_of_sumbool _ _ (elne_dec bool_ne_dec x y)).

  Reserved Notation "b === c" (at level 101, left associativity).
  Notation "b === c" := (eleq' b c) : bool_scope.

  Reserved Notation "b =!= c" (at level 101, left associativity).
  Notation "b =!= c" := (elne' b c) : bool_scope.

  Eval compute in (true === true).

  Lemma refl_eleq' : forall e, (e === e).
  Proof.
    unfold eleq'.
    move=> e.
    case: (eleq_dec bool_eq_dec e e);
      by rewrite /eleqp.
    Qed.
  
 Lemma sym_eleq'' : forall e1 e2, (e1 === e2) = (e2 === e1).
  Proof.
    unfold eleq'.
    move=> e1 e2.
    case: (eleq_dec bool_eq_dec e1 e2).
    rewrite /eleqp //. move=> H //=.
    admit.
    rewrite /eleqp //. move=> H //=.
    admit.
  Qed.
  
  Lemma assoc_eleq' : forall e1 e2 e3,
                        ((e1 === e2) === e3) = (e1 === (e2 === e3)).
  Proof.
    unfold eleq'.
    move=> e1 e2 e3.
    case: (eleq_dec bool_eq_dec e1 e2) => H1.
    case: (eleq_dec bool_eq_dec e2 e3) => H2.
    unfold eleqp in *.
    simpl.
  Admitted.
  
End Sumbool_Equational_logic.

(* END *)
