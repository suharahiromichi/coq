Section ExistsUnique.

  Variables (A : Type) (P : A -> Prop).
  
  (*                
Example 3.6.1

1. ∃x(P(x) ∧ ∀y(P(y) → y = x))                (= ∃!x P(x))
2. ∃x∀y(P(y) ↔ y = x).
3. ∃x P(x) ∧ ∀y∀z((P(y) ∧ P(z)) → y = z).
   *)
  
  (* 1 -> 2 *)
  Goal (exists ! x, P x) -> (exists x, forall y, P y <-> x = y).
  Proof.
    unfold unique.
    intros.
    destruct H as [x0].
    destruct H as [H1 H2].
    (* Givens and Goal p.147 *)
    exists x0.
    intros.
    split.
    - now apply H2.
    - intros Hx0y.
      now rewrite <- Hx0y.
  Qed.
  
  (* 2 -> 3 *)
  Goal (exists x, forall y, P y <-> x = y) ->
  (exists x, P x /\ (forall y z, P y /\ P z -> y = z)).
  Proof.
    intros.
    destruct H as [x0].
    exists x0.
    split.
    - destruct (H x0).
      now apply H1.
    - intros y z [H1 H2].
      (* Givens and Goal p.148 *)
      destruct (H y) as [H3 H4].
      destruct (H z) as [H5 H6].
      now rewrite <- H3, <- H5.
  Qed.
  
  (* 3 -> 1 *)
  Goal (exists x, P x /\ (forall y z, P y /\ P z -> y = z)) ->
  (exists ! x, P x).
  Proof.
    unfold unique.
    intros H.
    destruct H as [x0].
    destruct H as [H1 H2].
    exists x0.
    (* Givens and Goal p.148 *)
    split.
    - easy.
    - intros y H3.
      now apply (H2 x0 y).
  Qed.
  
End ExistsUnique.
