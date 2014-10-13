(**
日本ソフトウェア科学会
チュートリアル(1) 定理証明支援系Coq入門
講師：アフェルト レナルド 先生
https://staff.aist.go.jp/reynald.affeldt/ssrcoq/coq-jssst2014.pdf
*)

(**
首記の講演から興味のもとに抜粋し、例題を追加したものです。
内容の責任は  @suharahiromichi にあります。
 *)

(**
Prop impredicative / Type predicative
predicative_example.v
スライド p.36〜
 *)

(** Prop is predicative *)
Definition DupProp : forall (P : Prop), P -> P /\ P := 
  fun P p => conj p p.

Lemma DupPropSelf : 
  (forall (P : Prop), P -> P /\ P) /\ (forall (P : Prop), P -> P /\ P).
Proof.
  apply DupProp.
  exact DupProp.
  Show Proof.
Qed.

Check DupProp : forall P : Prop, P -> P /\ P : Prop.
Check (forall (P : Prop), P -> P /\ P) : Prop.
Check (DupProp (forall P : Prop, P -> P /\ P) DupProp) :
  (forall P : Prop, P -> P /\ P) /\ (forall P : Prop, P -> P /\ P).
Check (DupProp _ DupProp) : 
  (forall P : Prop, P -> P /\ P) /\ (forall P : Prop, P -> P /\ P).

(* Type is impredicative *)
Definition DupType : forall (P : Type), P -> P * P := 
  fun P p => (p, p).

Lemma DupTypeSelf : 
  (forall (P : Type), P -> P * P) * (forall (P : Type), P -> P * P).
Proof.
  apply DupType.
  exact DupType.
Fail Qed.

Set Printing Universes.                     (* Coqの推論したTypeNを表示する。 *)
Check DupType : forall P : Type (* Top.28 *), P -> P * P.
Check forall P : Type (* Top.31 *), P -> P * P : Type (* Top.32 *).
Check DupType (forall P : Type (* Top.47 *), P -> P * P) DupType :
  (forall P : Type (* Top.36 *), P -> P * P) * (forall P : Type (* Top.39 *), P -> P * P).
Fail Check (DupType _ DupType). (* Error: Universe inconsistency (cannot enforce Top.2 < Top.2). *)

(* Set is impredicative *)
Definition DupSet : forall (P : Set), P -> P * P := 
  fun P p => (p, p).

Set Printing Universes.
Check DupSet : forall P : Set, P -> P * P.
Check forall P : Set, P -> P * P : Type (* Top.56 *).
Fail Check DupSet (forall P : Set, P -> P * P) DupSet.
Fail Check (DupSet _ DupSet).

(* example of the identity function *)
Definition myidProp : forall (A : Prop), A -> A := 
  fun (A : Prop) (a : A) => a.
Check myidProp : forall A : Prop, A -> A.
Check forall (A : Prop), A -> A : Prop.
Check (myidProp (forall (A : Prop), A -> A) myidProp) : forall A : Prop, A -> A.
Check (myidProp _ myidProp) : forall A : Prop, A -> A.

Definition myidType : forall (A : Type), A -> A := 
  fun (A : Type) (a : A) => a.
Set Printing Universes.
Check myidType : forall A : Type (* Top.63 *), A -> A.
Check forall (A : Type (* Top.65 *)), A -> A : Type (* Top.64 *).
Check myidType (forall A : Type (* Top.68 *), A -> A) :
  (forall A : Type (* Top.66 *), A -> A) -> forall A : Type (* Top.67 *), A -> A.
Fail Check (myidType _ myidType). (* Error: Universe inconsistency (cannot enforce Top.61 < Top.61). *)

Definition myidSet : forall (A : Set), A -> A := 
  fun (A : Set) (a : A) => a.
Set Printing Universes.
Check myidSet : forall A : Set, A -> A.
Check (forall (A : Set), A -> A) : Type (* Top.72 *).
Fail Check (myidSet (forall (A : Set), A -> A) myidSet).
Fail Check (myidSet _ myidType).

(* END *)
