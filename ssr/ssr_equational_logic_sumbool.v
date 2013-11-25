(*
等式論理 (===) : elexp -> elexp -> elexp を使う論理体系。
2013_11_25 @suharahiromichi

=== についてassocが働くので（はず）、A === B === C という書き方ができる。
それを sumbool を使って定義する。

@hatsugai さんの等式論理の証明チェッカ を参考にした。
http://www.principia-m.com/ts/0072/index-jp.html
*)

Require Import ssreflect ssrbool ssrnat seq.
Require Import ssrfun.

Section Sumbool_Equational_logic.

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

  Definition eleq (x y : elexp) : elexp :=
    proj1_sig (elexp_of_sumbool _ _ (eleq_dec elexp_eq_dec x y)).

  Definition elne (x y : elexp) : elexp :=
    proj1_sig (elexp_of_sumbool _ _ (elne_dec elexp_ne_dec x y)).

  Reserved Notation "b === c" (at level 101, left associativity).
  Notation "b === c" := (eleq b c) : bool_scope.

  Reserved Notation "b =!= c" (at level 101, left associativity).
  Notation "b =!= c" := (elne b c) : bool_scope.

  Reserved Notation "b &&& c" (at level 91, left associativity).
  Notation "b &&& c" := (ELand b c) : bool_scope.

  Reserved Notation "b ||| c" (at level 91, left associativity).
  Notation "b ||| c" := (ELor b c) : bool_scope.

  Reserved Notation "b ===> c" (at level 91, left associativity).
  Notation "b ===> c" := (ELimp b c) : bool_scope.

  Lemma refl_eleq : forall e, (e === e) = ELtrue.
  Proof.
    unfold eleq.
    move=> e.
    case: (eleq_dec elexp_eq_dec e e);
      by rewrite /eleqp.
  Qed.
  
  Lemma sym_eleq : forall e1 e2,
                     (e1 === e2) = (e2 === e1).
  Proof.
    unfold eleq.
    move=> e1 e2.
    case: (eleq_dec elexp_eq_dec e1 e2) => H1;
    case: (eleq_dec elexp_eq_dec e2 e1) => H2;
    try done;
    simpl; unfold eleqp in *; unfold not in *;
    exfalso; [apply H2| apply H1]; done.
  Qed.
  
  Lemma assoc_eleq : forall e1 e2 e3,
                       ((e1 === e2) === e3) = (e1 === (e2 === e3)).
  Proof.
    unfold eleq.
    move=> e1 e2 e3.
    case: (eleq_dec elexp_eq_dec e1 e2) => H1;
    case: (eleq_dec elexp_eq_dec e2 e3) => H2.
    Admitted.

End Sumbool_Equational_logic.

(* END *)
