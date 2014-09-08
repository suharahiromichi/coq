(* Prop is predicative *)

Definition DupProp : forall (P : Prop), P -> P /\ P := 
  fun P p => conj p p.

Lemma DupPropSelf : 
  (forall (P : Prop), P -> P /\ P) /\ 
  (forall (P : Prop), P -> P /\ P).
Proof.
Check (forall (P : Prop), P -> P /\ P).
apply DupProp.
exact DupProp.
Show Proof.
Check (DupProp _ DupProp).
Qed.

(* Type is impredicative *)

Definition DupType : forall (P : Type), P -> P * P := 
  fun P p => (p, p).

Lemma DupTypeSelf : 
  (forall (P : Type), P -> P * P) * 
  (forall (P : Type), P -> P * P).
Proof.
Check (forall (P : Type), P -> P * P).
apply DupType.
exact DupType.
Fail Qed.
Fail Check (DupType _ DupType).
Set Printing Universes.
Check DupType.
Check (forall (P : Type), P -> P * P).
Fail Check (DupType _ DupType).

(* example of the identity function *)

Definition myidProp : forall (A : Prop), A -> A := 
  fun (A : Prop) (a : A) => a.
Check (myidProp _ myidProp).

Definition myidType : forall (A : Type), A -> A := 
  fun (A : Type) (a : A) => a.
Check myidType.
Check (forall (A : Type), A -> A).
Fail Check (myidType _ myidType).
