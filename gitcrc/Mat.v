Require Export Ring.
Set Implicit Arguments. 
Section mat.                                (* matrices. *)
 Variables (A:Type)
           (zero one : A) 
           (plus mult minus : A -> A -> A)
           (sym : A -> A).
 Notation "0" := zero.  Notation "1" := one.
 Notation "x + y" := (plus x y).  
 Notation "x * y " := (mult x y).
 

 Structure M2 : Type := {c00 : A;  c01 : A;
                         c10 : A;  c11 : A}.


Definition Zero2 : M2 := Build_M2 0 0 0 0.
Definition Id2 : M2 := Build_M2  1 0 0 1.

Definition M2_mult (m m':M2) : M2 :=
 Build_M2 (c00 m * c00 m' + c01 m * c10 m')
          (c00 m * c01 m' + c01 m * c11 m')
          (c10 m * c00 m' + c11 m * c10 m')
          (c10 m * c01 m' + c11 m * c11 m').


Definition M2_plus (m m' : M2) : M2 :=
  @Build_M2 (c00 m + c00 m')
            (c01 m + c01 m')
            (c10 m * c10 m')
            (c11 m * c11 m').

Lemma M2_eq_intros :
  forall m m':M2, c00 m = c00 m' ->
                  c01 m = c01 m' ->
                  c10 m = c10 m' ->
                  c11 m = c11 m' -> m = m'.
destruct m;destruct m';simpl.
intros H H1 H2 H3;rewrite H ,H1, H2, H3;trivial.
Qed.
End mat.                                    (* matrices. *)


