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
        ELtrue                              (* true = true *)
      else
        ELfalse                             (* true = false *)
    else if eleval e2 is true then
           ELfalse                          (* false = true *)
         else
           ELtrue.                          (* false = false *)

  Definition elne (e1 e2 : elexp) : elexp :=
    if eleval e1 is true then
      if eleval e2 is true then
        ELfalse
      else
        ELtrue
    else if eleval e2 is true then
           ELtrue
         else
           ELfalse.
             
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

End Equational_logic.


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
