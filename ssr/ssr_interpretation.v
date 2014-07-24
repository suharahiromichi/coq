(**
Coq SSReflect の Interpretation について

http://hal.inria.fr/docs/00/55/53/79/PDF/main-rr.pdf
*)
Require Import ssreflect ssrbool.

(**
- Bool型の式とProp型の式とを書き換えることをInterpretationという。
- Inductive reflect ... による書き換えだけではない。
- move/V と apply/V だけではない。
*)

(**
## Interpreting assumptions.
*)
Section Interpreting_Assumptions.
Variable P Q : bool -> Prop.
Hypothesis P2Q : forall a b, P (a || b) -> Q a.

Goal forall a, P (a || a) -> Q a.
Proof.
  move=> a HPa.
  move: {HPa} (P2Q _ _ HPa).                (* ├ Q a -> Q a *)
  by [].
Qed.

Goal forall a, P (a || a) -> Q a.
Proof.
  move=> a HPa.
  apply P2Q in HPa.                         (* HPa : Q a ├ Q a *)
  move: HPa.                                (* ├ Q a -> Q a *)
  by [].
Qed.

Goal forall a, P (a || a) -> Q a.
Proof.
  move=> a HPa; move/P2Q : HPa.             (* ├ Q a -> Q a *)
  (* move=> a HPa; move : HPa; move/P2Q. *)
  by [].
Qed.

Goal forall a, P (a || a) -> Q a.
Proof.
  move=> a; move/P2Q.                       (* ├ Q a -> Q a *)
  by [].
Qed.
End Interpreting_Assumptions.

(**
## Specializing assumptions.
*)
Section Specializing_Assumptions.

Goal forall z, (forall x y, x + y = z -> z = x) -> z = 0.
Proof.
  move=> z.
  move/(_ 0 z).                             (* 前提に 0 z をapplyする。「_」は前提を指す。 *)
  apply.
  by [].
Qed.

Goal forall z, (forall x y, x + y = z -> z = x) -> z = 0.
Proof.
  move=> z H.
  move: {H} (H 0 z).
  apply.
  by [].
Qed.
End Specializing_Assumptions.

(**
## Interpreting goals.
*)
Section Interpreting_Goals.
Variable P Q : bool -> Prop.
Hypothesis Q2P : forall a b, Q a -> P (a || b).

Goal forall a, Q a -> P (a || a).
Proof.
  move=> a HPa.
  by apply: (Q2P _ _ HPa).
Qed.

Goal forall a, Q a -> P (a || a).
Proof.
  move=> a HPa.
  apply Q2P.
  by [].
Qed.

Goal forall a, Q a -> P (a || a).
Proof.
  (* move=> a HPa; move : HPa; apply/Q2P. *)
  by move=> a HPa; apply/Q2P : HPa.
Qed.

Goal forall a, Q a -> P (a || a).
Proof.
  by move=> a; apply/Q2P.
Qed.
End Interpreting_Goals.

(**
## The reflect predicate.
*)
Section use_reflect_predicates.

Lemma andP : forall b1 b2 : bool, reflect (b1 /\ b2) (b1 && b2).
Proof.
  by case; case; constructor=> //; case.
Qed.

Goal forall a b : bool, a && b -> a /\ b.
Proof.
  by move=> a b; apply/andP.
Qed.

Goal forall a b : bool, a /\ b -> a && b.
Proof.
  move=> a b; move/andP.
  by [].
Qed.

End use_reflect_predicates.

(**
## Interpreting equivalences.
*)
Section Interpreting_Equivalences.

Lemma idP : forall b1 b2 : bool, reflect b1 b1.
Proof.
  move=> b1 b2.
  by case b1; constructor.
Qed.

Goal forall b1 b2 : bool, (b1 <-> b2) -> b1 = b2.
Proof.
  move=> b1 b2 H.
  apply/idP/idP;
    by rewrite //=; apply H.
Qed.
End Interpreting_Equivalences.

(**
## Proving reflect equivalences.
*)
Section Proving_reflect_Equivalences.

Lemma iffP : forall (P Q : Prop) (b : bool),
               reflect P b -> (P -> Q) -> (Q -> P) -> reflect Q b.
Proof.
  move=> P Q b Pb.
  by case: Pb; constructor; auto.
Qed.

Goal forall (P : Prop) (b : bool), reflect P b.
Proof.
  move=> P b.
(*  apply: (iffP (idP b)). *)
  eapply (iffP _ _ _ (idP _ _)).
(* Goal : b -> P *)
(* Goal : P -> b *)
  Admitted.
End Proving_reflect_Equivalences.

(* END *)
