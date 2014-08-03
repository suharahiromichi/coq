(**
An introduction to small scale reflection in Coq

4. Small scale reflection, first examples

http://hal.inria.fr/docs/00/55/53/79/PDF/main-rr.pdf

4.1 The two sides of deduction
*)
Require Import ssreflect ssrbool.
(**
- Bool型の式とProp型の式とを書き換えることをInterpretationという。
- Inductive reflect ... による書き換えだけではない。
- move/V と apply/V だけではない。
*)

(**
4.1.1 Interpreting assumptions.
*)
(* 参考： P Q は、P2QとGoalで同じものでないと、意図どおりにならない。 *)
Hypothesis P2Q : forall (P Q : bool -> Prop) (a : bool), P a -> Q a.
Goal forall (P Q : bool -> Prop) (a : bool), P a -> Q a.
Proof.
  move=> P Q a.
  move/P2Q.
  (* Goal : (forall P0 : bool -> Prop, P0 a) -> Q a *)
  apply.
Qed.

Section Basic.
  Variable P Q : bool -> Prop.
  (* P2QとGoalのP,Qは同じものを指す。 *)
  Hypothesis P2Q : forall a, P a -> Q a.
  
  Goal forall a, P a -> Q a.
  Proof.
    move=> a HPa.
    move: (P2Q a HPa).
    apply.
  Qed.
  (* これと同じ。 *)
  Goal forall a, P a -> Q a.
  Proof.
    move=> a HPa.
    apply P2Q in HPa.
    apply HPa.
  Qed.
  (* これと同じ。 *)  
  Goal forall a, P a -> Q a.
  Proof.
    move=> a.
    move/P2Q.
    apply.
  Qed.

  (* ゴールに適用する場合 *)
  Goal forall a, P a -> Q a.
  Proof.
    move=> a HPa.
    apply P2Q.
    apply HPa.
  Qed.
  (* これと同じ。 *)  
  Goal forall a, P a -> Q a.
  Proof.
    move=> a.
    apply/P2Q.
  Qed.
End Basic.

Section Interpreting_Assumptions.
  Variable P Q : bool -> Prop.

  (** 基本の例 *)
  Hypothesis P2Q : forall a b, P (a || b) -> Q a.
  (* P2QとGoalのP,Qは同じものを指す。 *)
  
  Goal forall a, P (a || a) -> Q a.
  Proof.
    move=> a HPa.
    move: {HPa} (P2Q _ _ HPa).              (* ├ Q a -> Q a *)
      by [].
  Qed.
  (* これと同じ。 *)
  Goal forall a, P (a || a) -> Q a.
  Proof.
    move=> a HPa.
    apply P2Q in HPa.                       (* HPa : Q a ├ Q a *)
    move: HPa.                              (* ├ Q a -> Q a *)
      by [].
  Qed.
  (* これと同じ。 *)
  Goal forall a, P (a || a) -> Q a.
  Proof.
    move=> a HPa; move/P2Q : HPa.           (* ├ Q a -> Q a *)
      (* move=> a HPa; move : HPa; move/P2Q. *)
      by [].
  Qed.
  (* これと同じ。 *)
  Goal forall a, P (a || a) -> Q a.
  Proof.
    move=> a; move/P2Q.                     (* ├ Q a -> Q a *)
      by [].
  Qed.

  (** 場合わけする *)
  Hypothesis Q2P : forall a b, Q (a || b) -> P a \/ Q b.
  (* GoalのP,Qは同じものを指す。 *)

  Goal forall a b, Q (a || b) -> P a \/ Q b.
  Proof.
    move=> a b.
    move/Q2P => [HPa | HPb]; by [left | right].
  Qed.

  (** Viewに <-> のある場合 *)
  Hypothesis PQequiv : forall a b, P (a || b) <-> Q a.
  (* GoalのP,Qは同じものを指す。 *)

  Goal forall a b, P (a || b) -> True.
  Proof.
    move=> a b.
    move/PQequiv.
    by [].
  Qed.
  (* これと同じ。 *)
  Goal forall a b, P (a || b) -> True.
  Proof.
    move=> a b HPab.
    (* 基本の例のように、(PQequiv a b HPab) とはできない。 *)
    Check iffLR (PQequiv a b).
    Check iffLR (PQequiv a b) HPab.
    move: (iffLR (PQequiv a b) HPab).
    by [].
  Qed.
  (* これと同じ。 *)
  Goal forall a b, P (a || b) -> True.
  Proof.
    move=> a b.
    move/(iffLR (PQequiv a b)).
    by [].
  Qed.
End Interpreting_Assumptions.

(**
4.1.2 Specializing assumptions.
*)
Section Specializing_Assumptions.

  Goal forall z, (forall x y, x + y = z -> z = x) -> z = 0.
  Proof.
    move=> z.
    move/(_ 0 z).                        (* 前提に 0 z をapplyする。「_」は前提を指す。 *)
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
4.1.3 Interpreting goals.
*)
Section Interpreting_Goals.
  Variable P Q : bool -> Prop.
  Hypothesis Q2P : forall a b, Q a -> P (a || b).

  Goal forall a, Q a -> P (a || a).
  Proof.
    move=> a HPa.
    Check (Q2P _ _ HPa).
      by apply: (Q2P _ _ HPa).
  Qed.
  (* これと同じ。 *)  
  Goal forall a, Q a -> P (a || a).
  Proof.
    move=> a HPa.
    apply Q2P.
      by [].
  Qed.
  (* これと同じ。 *)  
  Goal forall a, Q a -> P (a || a).
  Proof.
      (* move=> a HPa; move : HPa; apply/Q2P. *)
      by move=> a HPa; apply/Q2P : HPa.
  Qed.
  (* これと同じ。 *)  
  Goal forall a, Q a -> P (a || a).
  Proof.
      by move=> a; apply/Q2P.
  Qed.

  (** Viewに <-> のある場合 *)
  Hypothesis PQequiv : forall a b, P (a || b) <-> Q a.
  (* GoalのP,Qは同じものを指す。 *)
  
  Goal forall a, P ((~~ a) || a).
  Proof.
    move=> a.
    apply/PQequiv.
    (* Goal : Q (~~ a) *)
    admit.
  Qed.
  (* これと同じ。 *)  
  Goal forall a, P ((~~ a) || a).
  Proof.
    move=> a.
    Check (PQequiv (~~ a) a).
    Check iffRL (PQequiv (~~ a) a).
    apply: (iffRL (PQequiv (~~ a) a)). 
    (* Goal : Q (~~ a) *)
    admit.
  Qed.
End Interpreting_Goals.

(**
4.1.4 The reflect predicate.
*)
Section use_reflect_predicates.
  
  (* Exercise 4.1.1  *)
  Lemma andP : forall {b1 b2 : bool}, reflect (b1 /\ b2) (b1 && b2).
  Proof.
      by case; case; constructor=> //; case.
  Qed.

  Lemma orP : forall {b1 b2 : bool}, reflect (b1 \/ b2) (b1 || b2).
  Proof.
    case; case; constructor;
      by [left | left | right | case].
  Qed.

  Goal forall a b : bool, a -> b -> a /\ b.
  Proof.
    move=> a b Ha Hb; apply/andP.           (* Goal: a && b *)
    by apply/andP.                          (* もどす。 *)
  Qed.
  
  Goal forall a b : bool, a /\ b -> a.
  Proof.
    move=> a b; move/andP.                  (* Goal: a && b -> a *)
    move/andP; by case.                     (* もどす。 *)
  Qed.

  Goal forall a b : bool, a /\ b -> a && b.
  Proof.
    move=> a b; move/andP.
      by [].
  Qed.

  Goal forall a b : bool, a && b -> a /\ b.
  Proof.
      by move=> a b; apply/andP.
  Qed.

  

End use_reflect_predicates.

(**
4.1.5 Interpreting equivalences.
*)
Section Interpreting_Equivalences.

  Lemma idP : forall {b1 : bool}, reflect b1 b1.
  Proof.
    move=> b1.
      by case b1; constructor.
  Qed.
  
  Goal forall b1 b2 : bool, (b1 <-> b2) -> b1 = b2.
  Proof.
    move=> b1 b2 H.
    apply/idP/idP;
      by rewrite //=; apply H.
  Qed.

  (** norを変換しない例 *)
  Goal forall b1 b2 b3 : bool, ~~ (b1 || b2) = b3.
  Proof.
    move=> b1 b2 b3.
    apply/idP/idP.
    admit.                                  (* Goal : ~~ (b1 || b2) -> b3 *) 
    admit.                                  (* Goal : b3 -> ~~ (b1 || b2) *)
  Qed.

  (** norを変換をする例 *)
  Goal forall b1 b2 b3 : bool, ~~ (b1 || b2) = b3.
  Proof.
    move=> b1 b2 b3.
    apply/norP/idP.
    admit.                                  (* Goal : ~~ b1 /\ ~~ b2 -> b3 *) 
    admit.                                  (* Goal : b3 -> ~~ b1 /\ ~~ b2) *)
  Qed.

  Goal forall b1 b2 b3 : bool, ~~ (b1 || b2) = b3.
  Proof.
    move=> b1 b2 b3.
    apply/idP/idP.
    move/norP.
    admit.                                  (* Goal : ~~ b1 /\ ~~ b2 -> b3 *) 
    move=> Hb3. apply/norP. move: Hb3.
    admit.                                  (* Goal : b3 -> ~~ b1 /\ ~~ b2) *)
  Qed.
End Interpreting_Equivalences.

(**
4.1.6 Proving reflect equivalences.
*)
Section Proving_reflect_Equivalences.

  (* Exercise 4.1.2  *)
  Lemma iffP : forall {P Q : Prop} {b : bool},
                 reflect P b -> (P -> Q) -> (Q -> P) -> reflect Q b.
  Proof.
    move=> P Q b Pb.
      by case: Pb; constructor; auto.
  Qed.

  Goal forall (P : Prop) (b : bool), reflect P b.
  Proof.
    move=> P b.
    Check @iffP b P b (@idP b).             (* (b -> P) -> (P -> b) -> reflect P b *)
    apply: (iffP idP).                      (* apply: (@iffP b P b (@idP b)). *)
  (* Goal : b -> P *)
  (* Goal : P -> b *)
  Admitted.
  
  Goal forall (P1 P2 : Prop) (b1 b2 : bool),
         reflect (P1 /\ P2) (b1 && b2).
  Proof.
    move=> P1 P2 b1 b2.
    Check (@andP b1 b2).                    (* reflect (b1 /\ b2) (b1 && b2) *)
    Check (@iffP (b1 /\ b2) (P1 /\ P2) (b1 && b2)).
    Check (@iffP (b1 /\ b2) (P1 /\ P2) (b1 && b2) (@andP b1 b2)).
    Check (iffP andP).
    apply: (iffP andP).
  (* apply: (@iffP (b1 /\ b2) (P1 /\ P2) (b1 && b2) (@andP b1 b2)). *)
  (* Goal : b1 /\ b2 -> P1 /\ P2 *)
  (* Goal : P1 /\ P2 -> b1 /\ b2 *)
  Admitted.
End Proving_reflect_Equivalences.

(**
4.2 Exercises: sequenences
 *)

(**
4.3 Exercises: Boolean equations
 *)
(* END *)
