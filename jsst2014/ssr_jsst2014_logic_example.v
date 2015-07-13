Module minimal_Gallina_introduction.

Variable x : Prop.
Variables A B : Prop.
Variable t2 : Prop.

Check A -> B : Prop.
(* NB: we will see later why this holds *)
Check A -> B : Set.                         (* 補足説明：Set でもある。 *)

Check (fun y => y -> y) : Prop -> Prop.
Definition t1_oops := fun y => y -> y.
Check t1_oops.
Definition t1 := fun y : Prop => y -> y.
Check t1.
Check t1 A : Prop.

Fail Check (fun y : Prop => y -> y) -> B.
(* NB: we will see later why this does not hold *)

End minimal_Gallina_introduction.

Require Import ssreflect.

Module propositions_as_types_example.

Lemma hilbertS (A B C : Prop) : 
  (A -> B -> C) -> (A -> B) -> A -> C.
Show Proof.
move=> H1.
Show Proof. (* observe the effect of move=> on the proof-term *)
move=> H2.
move=> H3.
cut B. (* NB: this is a traditional Coq tactic, seldom used in practice *)
cut A.
assumption.
assumption.
cut A.
assumption.
assumption.
Show Proof.
Qed.

Definition hilbertS_proof := 
  fun (A B C : Prop) (H1 : A -> B -> C) (H2 : A -> B) (H3 : A) =>
    (fun H : B => (fun H0 : A => H1 H0) H3 H) ((fun H : A => H2 H) H3).

Lemma hilbertS_direct_proof (A B C : Prop) : 
  (A -> B -> C) -> (A -> B) -> A -> C.
exact (hilbertS_proof A B C).
Qed.

Lemma hilbertS_in_practice (A B C : Prop) : 
  (A -> B -> C) -> (A -> B) -> A -> C.
move=> H1.
move=> H2.
move=> H3.
apply H1.
exact H3.
apply H2.
exact H3.
Show Proof.
Qed.

Definition hilbertS_in_practice_proof := 
  fun (A B C : Prop) (H1 : A -> B -> C) (H2 : A -> B) (H3 : A) =>
    H1 H3 (H2 H3).

Goal hilbertS_proof = hilbertS_in_practice_proof.
reflexivity.
Qed.

End propositions_as_types_example.

Module move_and_apply_tactics.

Lemma modus_ponens : forall P Q : Prop, (P -> Q) -> P -> Q.
Show Proof.
move=> P.
Show Proof.
move: P.
Show Proof.
move=> P Q PQ p.
apply: PQ.
done.
Qed.

Goal forall P Q : Prop, (forall R : Prop, R -> Q) -> P -> Q.
Proof.
move=> P Q rq p.
Fail apply rq.
apply: rq p.
(*
compare with:
refine (rq _ _).
exact p.
*)
Qed.

Lemma exo0 : forall P : Prop, P -> P.
Proof.
  by [].
Qed.

Lemma exo1 : forall P Q : Prop, P -> (P -> Q) -> Q.
Proof.
  move=> P Q HP.
  by apply.
Qed.

Lemma exo2 : forall P : Prop, (P -> P) -> P -> P.
Proof.
  Check modus_ponens.
  move=> P.
  by apply: (modus_ponens P P).
Qed.

(* transitivity of implication *)
Lemma exo3 P Q R : (P -> Q) -> (Q -> R) -> P -> R.
Proof.
  move=> HPQ HQR HP.
  
  apply: HQR.
  by apply: HPQ.
  Undo 2.
  Check HQR (HPQ HP).
  by apply: (HQR (HPQ HP)).
Qed.

End move_and_apply_tactics.

Section logical_connectives.

Print True.
Check True.
Check I.

Goal True.
apply: I.
Qed.

Print False.

Goal True -> False.
case.
Abort.                                      (* OK *)

Check False_ind.

Goal False -> 1 = 0.
case.
Qed.

Print and.
Print and_ind.
Print and_rect.

Goal forall P Q, P /\ Q -> Q /\ P.
move=> P Q.
case.
move=> p q.
split.
exact q.
exact p.
Qed.

Print or.
Print or_ind.

Check (or_intror False I).
About or_intror.
Check (@or_intror False True I).
Check (@or_intror False _ I).
Check (@or_intror _ _ I).
Check (@or_intror _ _ I) :  False \/ True.

Goal forall A B, A \/ B -> B \/ A.
move=> A B.
  case=> [a | b].
  right.
  exact a.
left.
exact b.
Qed.

End logical_connectives.

Lemma exo4 : False \/ True.
Proof.
  by right.
Qed.

Lemma exo5 : forall A B C : Prop, A /\ B <-> B /\ A.
Proof.
  move=> A B C.
  by split; case.
Qed.  

Lemma exo6 (A B C : Prop) : A /\ B /\ C -> 
  (A /\ B) /\ C.
Proof.
  move=> HABC.
  case: HABC=> HA HBC.
  case: HBC=> HB HC.
  by split; [split|].
Qed.

Section Set_Prop.

Check nat.

Goal 0 = 1 -> False.
move=> abs.
discriminate.
Qed.

Goal (exists n : nat, True) -> nat.
Fail case.
(*  Error: Case analysis on sort Set is not allowed for inductive definition ex *)
Abort.

Goal {n : nat | True} -> nat.
case.
move=> m _.
exact m.
Undo 1.
by apply: m.                                (* 補足 *)
Qed.

Goal forall n m : nat, n = m /\ n <> m -> nat.
move=> n m.
case => nm nm'.
exact O.
Undo 1.
by apply: O.                                (* 補足 *)
Qed.

(* 追加 *)
Goal nat.
apply: 10.
Qed.

End Set_Prop.

Section product_formation.

(* Prop, Set, Type 自体は、Type の型を持つ。 *)
Fail Check Prop : Prop.
Fail Check Set : Prop.
Fail Check Type : Prop.

Fail Check Prop : Set.
Fail Check Set : Set.
Fail Check Type : Set.

Check Prop : Type.
Check Set : Type.
Check Type : Type.
Set Printing Universes.
Check Prop : Type.                          (* Top.43 *)
Check Set : Type.                           (* Top.44 *)
Check Type : Type.                          (* Top.45 *)
Unset Printing Universes.

(* rule Prop-Prop *)
Fail Check Prop -> Prop : Prop.
Fail Check Prop -> Prop : Set.
Check Prop -> Prop : Type.
(* rule Set-Prop *)
Fail Check Set -> Prop : Prop.
Fail Check Set -> Prop : Set.
Check Set -> Prop : Type.
(* rule Type-Prop *)
Fail Check Type -> Prop : Prop.
Fail Check Type -> Prop : Set.
Check Type -> Prop : Type.

(* rule Prop-Set *)
Fail Check Prop -> Set : Prop.
Fail Check Prop -> Set : Set.
Check Prop -> Set : Type.
(* rule Set-Set *)
Fail Check Set -> Set : Prop.
Fail Check Set -> Set : Set.
Check Set -> Set : Type.
(* rule Type-Set *)
Fail Check Type -> Set : Prop.
Fail Check Type -> Set : Set.
Check Type -> Set : Type.

(* rule Prop-Type *)
Fail Check Prop -> Type : Prop.
Fail Check Prop -> Type : Set.
Check Prop -> Type : Type.
(* rule Set-Type *)
Fail Check Set -> Type : Prop.
Fail Check Set -> Type : Set.
Check Set -> Type : Type.
(* rule Type-Type *)
Fail Check Type -> Type : Prop.
Fail Check Type -> Type : Set.
Check Type -> Type : Type.


(* Prop, Set, Type の要素の関係 *)
(* Prop <= Set <= Type *)
Variable P0 : Prop.
Variable S0 : Set.
Variable T0 : Type.

Check P0 : Prop.
Check P0 : Set.
Check P0 : Type.

Fail Check S0 : Prop.
Check S0 : Set.
Check S0 : Type.

Fail Check T0 : Prop.
Fail Check T0 : Set.
Check T0 : Type.

Variables P1 : Prop.
(* rule Prop-Prop *)
Check P0 -> P1 : Prop.
Check P0 -> P1 : Set.
Check P0 -> P1 : Type.
(* rule Set-Prop *)
Check S0 -> P1 : Prop.
Check S0 -> P1 : Set.
Check S0 -> P1 : Type.
(* rule Type-Prop *)
Check T0 -> P1 : Prop.
Check T0 -> P1 : Set.
Check T0 -> P1 : Type.

Variables S1 : Set.
(* rule Prop-Set *)
Fail Check P0 -> S1 : Prop.
Check P0 -> S1 : Set.
Check P0 -> S1 : Type.
(* rule Set-Set *)
Fail Check S0 -> S1 : Prop.
Check S0 -> S1 : Set.
Check S0 -> S1 : Type.
(* rule Type-Set *)
Fail Check T0 -> S1 : Prop.
Fail Check T0 -> S1 : Set.
Check T0 -> S1 : Type.

Variables T1 : Type.
(* rule Prop-Type *)
Fail Check P0 -> T1 : Prop.
Fail Check P0 -> T1 : Set.
Check P0 -> T1 : Type.
(* rule Set-Type *)
Fail Check S0 -> T1 : Prop.
Fail Check S0 -> T1 : Set.
Check S0 -> T1 : Type.
(* rule Type-Type *)
Fail Check T0 -> T1 : Prop.
Fail Check T0 -> T1 : Set.
Check T0 -> T1 : Type.

(* nat は、S0 と同じ。 *)
Fail Check (nat -> nat) : Prop.
Check (nat -> nat) : Set.
Check (nat -> nat) : Type.

(* forall A : Prop なるAは、P0 の場合と同じ。 *)
(* forall A : Set なるAは、S0 の場合と同じ。 *)
(* forall A : Type なるAは、T0 の場合と同じ。 *)
Check (forall A : Prop, A -> A) : Prop.
Check (forall A : Prop, A -> A) : Set.
Check (forall A : Prop, A -> A) : Type.
Fail Check (forall A : Set, A -> A) : Prop.
Fail Check (forall A : Set, A -> A) : Set.
Check (forall A : Set, A -> A) : Type.
Fail Check (forall A : Type, A -> A) : Prop.
Fail Check (forall A : Type, A -> A) : Set.
Check (forall A : Type, A -> A) : Type.

(* ふつうにPropであるもの。 *)
Check (forall x : nat, 0 <= x) : Prop.
Check (forall x : nat, x = x)  : Prop.
Check (forall A : Prop, A -> A) : Prop.
Check (forall P : nat -> Prop, P O -> exists n : nat , P n) : Prop.

(* これより複雑なものは、Typeの型を持つ。 *)
Check (nat -> Prop) : Type.
Check ((Prop -> Prop) -> Prop) : Type.
Check (forall P : nat -> Prop, Prop) : Type.

End product_formation.

(* まとめ *)
(* Propであるものは、Propである。 *)

(* Propであるものは、Setである。 *)
(* 依存型で、以下のものはSetである。 *)
Variable A : Set.                           (* A : Propでもよい。 *)
Variable B : Set.
Check (forall x : A, B) : Set.
Check A -> B : Set.

(* これ以外のものは、Type である *)

(* 以上 *)
