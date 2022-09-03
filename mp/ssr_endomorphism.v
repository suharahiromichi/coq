From mathcomp Require Import all_ssreflect.

(* 数学的現象を追う *)

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Variable M : Type.

(* 既約なベクトル空間 *)
Definition VS := M -> Prop.
Parameter X : VS.
Parameter o : VS.

Definition belong (V : VS) (x : M) : Prop := V x.

Definition Subset (W V : VS) := forall (x : M), W x -> V x.
Axiom FullSpace : forall (V : VS), Subset V X.
Axiom ZeroSpace : forall (V : VS), Subset o X.

(* 自己準同型 *)
(* Endomorphism の像 : 本当は準同型の条件も付加するべきであるが使わないので略 *)
Definition ImgOf (f : M -> M) (V : VS) :=
  fun (y : M) => (exists (x : M), y = f x /\ V x).

Definition Img (f : M -> M) :=  ImgOf f X.
Notation "f @ V" := (ImgOf f V) (at level 40, left associativity).

(* ベクトル空間の直和 *)
Definition DirectSum (V W : VS) := fun (x : M) => V x \/ W x.
Notation "V + W" := (DirectSum V W) (at level 50, left associativity).

Axiom DirectSumC : forall (V W : VS) (f : M -> M),
    V + W = W + V.

Axiom DirectSumDist : forall (V W : VS) (f : M -> M),
    f @ (V + W) = f @ V + f @ W.

Axiom DirectSum0V : forall (V : VS),
    o + V = V.


Lemma DirectSumV0 : forall (V : VS),
    V + o = V.
Proof.
Admitted.

Axiom DirectSumXV : forall (V : VS),
    X + V = X.

Lemma DirectSumVX : forall (V : VS),
    V + X = X.
Proof.
  Admitted.


(* 準同型定理 : 証明される事実だが, 準同型性として使います. *)
Parameter Ker : (M -> M) -> VS.
Axiom ImgKer : forall (f : M -> M), f @ (Ker f) = o.

Hypothesis Endomorphism : forall (f : M -> M) (V W : VS),
    f @ V = f @ W -> V = W + Ker f. 

Lemma ProjectionExisits : forall (f : M -> M),
    X = Img f + Ker f <-> f @ (f @ X) = f @ X.
Proof.
  split=> Hf.
  - have H : f @ (f @ X + Ker f) = f @ X by rewrite -Hf.
    rewrite DirectSumDist in H.
    rewrite ImgKer in H.
    by rewrite DirectSumV0 in H.
  - apply: Endomorphism.
    by rewrite Hf.
Qed.

Definition ZeroComponent (V : VS) (f : M -> M) := f @ V = o.
Definition InvariantComponent (V : VS) (f : M -> M) := f @ V = V.
Definition IrreducibleComponent (V : VS) (f : M -> M) :=
  (forall (W : VS), Subset W V -> f @ W = W -> W = V \/ W = o).


