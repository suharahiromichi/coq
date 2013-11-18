(* 等式論理 *)

Require Import ssreflect ssrbool ssrnat seq.
Require Import ssrfun.

Section Equational_logic.

  Inductive elexp : Set :=
  | ELtrue : elexp
  | ELfalse : elexp
  | ELnot : elexp -> elexp
  | ELand : elexp -> elexp -> elexp
  | ELor : elexp -> elexp -> elexp
  | ELimp : elexp -> elexp -> elexp.

  Fixpoint eleval (e : elexp) : bool :=
    match e with
      | ELtrue => true
      | ELfalse => false
      | ELnot e1 => ~~ eleval e1          (* ~~ は negb、boolの否定 *)
      | ELand e1 e2 => eleval e1 && eleval e2
      | ELor e1 e2 => eleval e1 || eleval e2
      | ELimp e1 e2 => ~~ eleval e1 || eleval e2 (* (~E1) \/ E2 *)
    end.

  Definition eleq (e1 e2 : elexp) : elexp :=
    if eleval e1 is true then
      if eleval e2 is true then
        ELtrue
      else
        ELfalse
    else
      if eleval e2 is true then
        ELfalse
      else
        ELtrue.
  
  Definition elne (e1 e2 : elexp) : elexp :=
    match eleval e1, eleval e2 with
      | true, true => ELfalse
      | true, false => ELtrue
      | false, true => ELtrue
      | false, false => ELfalse
    end.

  Reserved Notation "b &&& c" (at level 91, left associativity).
  Notation "b &&& c" := (ELand b c) : bool_scope.

  Reserved Notation "b ||| c" (at level 91, left associativity).
  Notation "b ||| c" := (ELor b c) : bool_scope.

  Reserved Notation "b --> c" (at level 91, left associativity).
  Notation "b --> c" := (ELimp b c) : bool_scope.

  Reserved Notation "b === c" (at level 101, left associativity).
  Notation "b === c" := (eleq b c) : bool_scope.

  Reserved Notation "b =!= c" (at level 101, left associativity).
  Notation "b =!= c" := (elne b c) : bool_scope.

  Check ELtrue === ELtrue.
  Eval compute in ELtrue === ELtrue.

  Check ELtrue === ELtrue === ELfalse.
  Eval compute in (ELtrue === ELtrue === ELfalse).

  Check ELtrue &&& ELtrue === ELtrue.
  Eval compute in ELtrue &&& ELtrue === ELtrue.

  Check ELtrue &&& ELtrue === ELtrue ||| ELfalse.
  Eval compute in ELtrue &&& ELtrue === ELtrue ||| ELfalse.


  Lemma refl_eleq : forall e, (e === e) = ELtrue.
  Proof.
    move=> e.
    rewrite /eleq.
      by case: (eleval e).
  Qed.

 Lemma sym_eleq : forall e1 e2, (e1 === e2) = (e2 === e1).
  Proof.
    move=> e1 e2.
    rewrite /eleq.
      by case: (eleval e1).
  Qed.


  Lemma if_then_else__else_then :
    forall (e e1 e2 : elexp),
      (if eleval (if eleval e then ELtrue else ELfalse) then e1 else e2) =
      (if eleval (if eleval e then ELfalse else ELtrue) then e2 else e1).
  Proof.
    move=> e e1 e2.
    by case: (eleval e).
  Qed.

  Lemma if_ite_ite :
    forall (e e' : elexp),
      (if eleval (if eleval e then ELtrue else ELfalse)
       then if eleval e' then ELfalse else ELtrue
       else if eleval e' then ELtrue else ELfalse) =
      (if eleval
            (if eleval e
             then if eleval e' then ELtrue else ELfalse
             else if eleval e' then ELfalse else ELtrue)
       then ELfalse
       else ELtrue).
  Proof.
  Admitted.                                 (* XXXX *)

  Lemma assoc_eleq : forall e1 e2 e3, ((e1 === e2) === e3) = (e1 === (e2 === e3)).
  Proof.
    move=> e1 e2 e3.
    rewrite /eleq.
    case: (eleval e1).
    case: (eleval e3).
    done.
    rewrite (if_then_else__else_then e2). done.
    rewrite -(if_then_else__else_then e2).
    rewrite if_ite_ite. done.
  Qed.

(* 推移則 trans (e1 === e2 === e3) = (e1 === e3) は成立しない。 *)

  Lemma detrue_eleq' : forall e1 e2, (ELtrue === e1 === e2) = (e1 === e2).
  Proof.
    move=> e1 e2.
    rewrite /eleq.
      by case (eleval e1); simpl.
  Qed.

  Lemma detrue_eleq : forall e e1 e2,
                        e = ELtrue -> (e === e1 === e2) = (e1 === e2).
  Proof.
    move=> e e1 e2 H.
    rewrite H /eleq.
      by case (eleval e1); simpl.
  Qed.
  
  Eval compute in eleval (ELnot ELtrue).
      
(* 推移則 trans (e1 === e2 === e3) = (e1 === e3) は成立しない。 *)

  Lemma trans_eleq : forall e1 e2 e3,
                       (e1 === e2 === e2 === e3) = (e1 === e3).
  Proof.
    move=> e1 e2 e3.
    rewrite [_ === e2 === e2]assoc_eleq
            refl_eleq
            [e1 === ELtrue]sym_eleq.
      by apply/detrue_eleq.
  Qed.

  Lemma defalse_eleq' : forall e e1 e2,
                         e = ELfalse -> (e === e1 === e2) = (ELnot e1 === e2).
  Proof.
    move=> e e1 e2 H.
    rewrite H /eleq.
    simpl.
      by case (eleval e1); simpl.
  Qed.

  Lemma defalse_eleq : forall e e1 e2,
                         e = ELfalse -> (e === e1 === e2) = (e1 =!= e2).
  Proof.
    move=> e e1 e2 H.
    rewrite H /eleq /elne.
    simpl.
      by case (eleval e1); simpl.
  Qed.

  Inductive reflect (P: Prop) : elexp -> Type :=
  | Reflect_true: P -> reflect P ELtrue
  | Reflect_false: ~P -> reflect P ELfalse.

(*
  Inductive reflect (P: elexp) : bool -> Type :=
  | Reflect_true: (P = ELtrue) -> reflect P true
  | Reflect_false: (P = ELfalse) -> reflect P false.
*)

  (* 「=」で結ぶには evalが必要であることに注意！ *)
  Lemma eqP: forall e1 e2, reflect (eleval e1 = eleval e2) (e1 === e2).
  Proof.
    move=> e1 e2.
    rewrite /eleq.
    case: (eleval e1); case: (eleval e2).
      by apply Reflect_true.
        by apply Reflect_false.
          by apply Reflect_false.
            by apply Reflect_true.
  Qed.

  Lemma eqE: forall e1 e2, (eleval e1 = eleval e2) <-> (e1 === e2) = ELtrue.
  Proof.
    move=> e1 e2.
    split.
    (* -> *)
    move=> H. rewrite /eleq -H.
      by case: (eleval e1).
    (* <- *)
      rewrite /eleq.
        by case (eleval e1); case (eleval e2).
  (* 途中で、ゴールに ELfalse = ELtrue -> true = false になるが、inverseしなくても、doneできる。 *)
Qed.

End Equational_logic.


Section Sumbool_Equational_logic.

  Hypothesis elexp_eq_dec :
    forall a b : elexp, {eleval a = eleval b} + {eleval a <> eleval b}.

  Hypothesis elexp_ne_dec :
    forall a b : elexp, {eleval a <> eleval b} + {eleval a = eleval b}.

  Definition elexp_of_sumbool :
    forall A B : Prop, {A} + {B} -> {e | if e is ELtrue then A else B}.
    intros A B H.
    elim H; intro; [exists ELtrue | exists ELfalse]; assumption.
  Defined.

  Definition eleqp (e1 e2 : elexp) : Prop :=
    eleval e1 = eleval e2.

  Definition eleq_dec :
    (forall (x y : elexp), {eleval x = eleval y} + {eleval x <> eleval y}) ->
    forall e1 e2, {eleqp e1 e2} + {~ eleqp e1 e2}.
  Proof.
    move=> H e1 e2.
    elim: (H e1 e2) => H12; [left | right];
                       rewrite /eleqp; assumption.
  Defined.

  Definition elne_dec :
    (forall (x y : elexp), {eleval x <> eleval y} + {eleval x = eleval y}) ->
    forall e1 e2, {~ eleqp e1 e2} + {eleqp e1 e2}.
  Proof.
    move=> H e1 e2.
    elim: (H e1 e2) => H12; [left | right];
                       rewrite /eleqp; assumption.
  Defined.

  Definition eleq' (x y : elexp) : elexp :=
    proj1_sig (elexp_of_sumbool _ _ (eleq_dec elexp_eq_dec x y)).

  Definition elne' (x y : elexp) : elexp :=
    proj1_sig (elexp_of_sumbool _ _ (elne_dec elexp_ne_dec x y)).

  Reserved Notation "b === c" (at level 101, left associativity).
  Notation "b === c" := (eleq' b c) : bool_scope.

  Reserved Notation "b =!= c" (at level 101, left associativity).
  Notation "b =!= c" := (elne' b c) : bool_scope.

  Eval compute in (ELtrue === ELtrue).

  Lemma refl_eleq' : forall e, (e === e) = ELtrue.
  Proof.
    unfold eleq'.
    move=> e.
    case: (eleq_dec elexp_eq_dec e e);
      by rewrite /eleqp.
(*    simpl. unfold not in H1. exfalso. apply H1. done. *)
    Qed.
  
 Lemma sym_eleq' : forall e1 e2, (e1 === e2) = (e2 === e1).
  Proof.
    unfold eleq'.
    move=> e1 e2.
    case: (eleq_dec elexp_eq_dec e1 e2).
    rewrite /eleqp //. move=> H //=.
    admit.
    rewrite /eleqp //. move=> H //=.
    admit.
  Qed.
  
  Lemma assoc_eleq' : forall e1 e2 e3, ((e1 === e2) === e3) = (e1 === (e2 === e3)).
  Proof.
    unfold eleq'.
    move=> e1 e2 e3.
    case: (eleq_dec elexp_eq_dec e1 e2) => H1.
    case: (eleq_dec elexp_eq_dec e2 e3) => H2.
    unfold eleqp in *.
    simpl.
  Admitted.
  
End Sumbool_Equational_logic.

(* おまけ *)

Goal forall (P Q R S T : Prop),
       P = Q /\ Q = R /\ R = S /\ T -> P = R /\ R = S /\ T.
Proof.
  move=> P Q R S T H.
  split.
  case: H => HPQ HQRS.
  case: HQRS => HQR HRS.
  rewrite -HQR. done.

  case: H => HPQ HQRS.
  case: HQRS => HQR HRS.
  split.
  destruct HRS.
  apply H.
  destruct HRS. done.
Qed.

Lemma quanimity : forall (P Q : Prop),
       P -> (P = Q) -> Q.
Proof.
  move=> P Q Hp Hpq.
  rewrite -Hpq.
  done.
Qed.

(* END *)
