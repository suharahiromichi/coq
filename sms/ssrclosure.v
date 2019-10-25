Section Closure.
  
  (* SF Rel.v *)
  
  Definition relation (X : Type) := X -> X -> Prop.  
  
  Inductive refl_step_closure {X : Type} (R : relation X)  : X -> X -> Prop :=
  | rsc_refl  : forall (x : X), refl_step_closure R x x
  | rsc_step : forall (x y z : X),
      R x y ->
      refl_step_closure R y z ->
      refl_step_closure R x z.
  
  Lemma rsc_R : forall {X : Type} (R : relation X) (x y : X),
      R x y -> refl_step_closure R x y.
  Proof.
    intros X R x y r.
    apply rsc_step with y.
    apply r.
    now apply rsc_refl.
  Qed.
  
  Lemma rsc_trans : forall {X : Type} (R : relation X) (x y z : X),
      refl_step_closure R x y ->
      refl_step_closure R y z ->
      refl_step_closure R x z.
  Proof.
    intros X R x y z.
    intros HRxy HRyz.
    induction HRxy as [|z' x y Rxy].
    - now apply HRyz.
    - apply (rsc_step R z' x z).
      apply Rxy.
      apply IHHRxy.
      now apply HRyz.
  Qed.

End Closure.

(* END *)
