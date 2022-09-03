From mathcomp Require Import all_ssreflect.
Require Import Coq.Logic.FunctionalExtensionality.

(* 数学的現象を追う *)

(* suahra 修正 20220903 *)

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Variable M : finType.

(* 既約なベクトル空間 *)
Definition VS := M -> bool.
Parameter X : VS.
Parameter o : VS.

Definition belong (V : VS) (x : M) := V x.
(* 以下では不使用で、直接 V x の形で使う。 *)

Definition Subset (W V : VS) := forall (x : M), W x -> V x.

(*
csm と同じように、こちらの定義のほうが、使いやすい。
*)
Axiom MotherSet : forall x, X x = true.
Axiom EmptySet : forall x, o x = false.

(*
Axiom FullSpace : forall (V : VS), Subset V X.
Axiom ZeroSpace : forall (V : VS), Subset o V.  (* 誤記修正 *)
*)

Lemma FullSpace : forall V, Subset V X.  (* csmのSub_Motherと同じ。 *)
Proof.
  move=> X H.
  by rewrite MotherSet.
Qed.

Lemma ZeroSpace : forall V, Subset o V.   (* csmのSub_Emptyと同じ。 *)
Proof.
  move=> V H.
  by rewrite EmptySet.
Qed.


(* Endomorphism の像 : 本当は準同型の条件も付加するべきであるが使わないので略 *)
Definition ImgOf (f : M -> M) (V : VS) : M -> bool :=
  fun (y : M) => [exists x : M, (y == f x) && V x].
Notation "f @ V" := (ImgOf f V) (at level 40, left associativity).

(* ベクトル空間の直和 *)
(* Definition DirectSum (V W : VS) := fun (x : M) => V x \/ W x. *)
Definition DirectSum (V W : VS) := fun (x : M) => V x || W x.
Notation "V + W" := (DirectSum V W) (at level 50, left associativity).

Check functional_extensionality
  : forall f g : _ -> _, (forall x : _, f x = g x) -> f = g.

Lemma DirectSumC : forall (V W : VS) (f : M -> M),
    V + W = W + V.
Proof.
  move=> V W f.
  rewrite /DirectSum.
  apply: functional_extensionality => x.
  by rewrite orbC.
Qed.

Lemma DirectSumDist : forall (V W : VS) (f : M -> M),
    f @ (V + W) = f @ V + f @ W.
Proof.
  move=> V W f.
  apply: functional_extensionality => y.
  rewrite /ImgOf /DirectSum.
  apply/idP/idP.
  - case/existsP => x.
    case/andP => H1 /orP [] H2.
    + apply/orP/or_introl/existsP.
      exists x.
      apply/andP.
      by split.
    + apply/orP/or_intror/existsP.
      exists x.
      apply/andP.
      by split.
  - case/orP => /existsP [x /andP [H1 H2]].
    + apply/existsP.
      exists x.
      apply/andP.
      split=> //.
      by apply/orP/or_introl.
    + apply/existsP.
      exists x.
      apply/andP.
      split=> //.
      by apply/orP/or_intror.
Qed.      

Lemma DirectSum0V : forall (V : VS),
    o + V = V.
Proof.
  move=> V.
  apply: functional_extensionality => y.  
  rewrite /ImgOf /DirectSum.
  by rewrite EmptySet orFb.
Qed.

Lemma DirectSumV0 : forall (V : VS),
    V + o = V.
Proof.
  move=> V.
  apply: functional_extensionality => y.  
  rewrite /ImgOf /DirectSum.
  by rewrite EmptySet orbF.
Qed.

Lemma DirectSumXV : forall (V : VS),
    X + V = X.
Proof.
  move=> V.
  apply: functional_extensionality => y.  
  rewrite /ImgOf /DirectSum.
  by rewrite MotherSet orTb.
Qed.

Lemma DirectSumVX : forall (V : VS),
    V + X = X.
Proof.
  move=> V.
  apply: functional_extensionality => y.  
  rewrite /ImgOf /DirectSum.
  by rewrite MotherSet orbT.
Qed.

(********)

Definition Img (f : M -> M) :=  ImgOf f X.

(* 準同型定理 : 証明される事実だが, 準同型性として使います. *)
Parameter Ker : (M -> M) -> VS.
Axiom ImgKer : forall (f : M -> M), f @ (Ker f) = o.

Lemma fex f X Y : f @ X = f @ Y -> X = Y.
Proof.
  rewrite /ImgOf => H.
  apply: functional_extensionality => x.
  have EQ (f' g' : M -> bool) y : f' = g' -> f' y = g' y by move=> ->.
Admitted.

Lemma Endomorphism : forall (f : M -> M) (V W : VS),
    f @ V = f @ W -> V = W + Ker f. 
Proof.
  move=> f V W H.
  apply: (@fex f).
  rewrite DirectSumDist.
  rewrite ImgKer DirectSumV0.
  done.
Qed.

(* これは無変更で証明できる。 *)
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

(* END *)
