From mathcomp Require Import all_ssreflect.
Require Import Coq.Logic.FunctionalExtensionality.

(* 数学的現象を追う *)

(* suahra 修正 20220903 *)
(* suhara 修正 20220919 finType で finSet ではない。 *)

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Variable M : finType.                       (* ここが重要 *)

(* 既約なベクトル空間 *)
(* Definition VS := M -> Prop. *)
(* Definition VS := {set M}. *)
Definition VS := M -> bool.

Section Test.
  Parameter X : VS.
  Parameter o : VS.


(* Definition belong (V : VS) (x : M) := V x. *)
(* 以下では不使用で、x \in V の形で使う。 *)
(*
Definition Subset (W V : VS) := forall (x : M), x \in W -> x \in X.
 *)

  Variables V W : VS.
  Variables x : M.

  Check x \in V : bool.
  Check W \subset V : bool.
  Locate "_ \subset _".

  (* MoterSet *)
  Check setT : {set M}.
  (* Empty *)
  Check set0 : {set M}.
End Test.

Axiom MotherSet : forall (x : M), x \in X.
Axiom EmptySet  : forall (x : M), x \notin o.
  
Section SUBSET.
(*
MathComp の場合は、

- ssrbool.v ``{subset A <= B} <-> A is a (collective) subpredicate of B``
  Notation "{ 'subset' A <= B }" := (sub_mem (mem A) (mem B))
*)
  Print sub_mem.
(*
  fun (T : Type) (mp1 mp2 : mem_pred T) => forall x : T, in_mem x mp1 -> in_mem x mp2
  : forall T : Type, mem_pred T -> mem_pred T -> Prop
*)
  
(*
- fintype.v ``A \subset <-> all x \in A satisfy x \in B``
   Notation "A \subset B" := (subset (mem A) (mem B))
*)
  Print subset.
(*
違いはよくわからないが、reflect述語がある。
*)
  Check subsetP : reflect {subset _ <= _} (_ \subset _).
  
  Lemma FullSpace : forall (V : VS), V \subset X.  (* csmのSub_Motherと同じ。 *)
  Proof.
    move=> V.
    apply/subsetP => x H.
    by rewrite MotherSet.
  Qed.
  
  Lemma ZeroSpace : forall (V : VS), o \subset V.   (* csmのSub_Emptyと同じ。 *)
  Proof.
    move=> V.
    apply/subsetP => x.
    move/negPn.
    by rewrite EmptySet.
  Qed.
(*
  以降では使いません。
  *)
End SUBSET.

(* Endomorphism の像 : 本当は準同型の条件も付加するべきであるが使わないので略 *)
Definition ImgOf (f : M -> M) (V : VS) : M -> bool :=
  fun (y : M) => [exists x : M, (y == f x) && (x \in V)].
Notation "f @ V" := (ImgOf f V) (at level 40, left associativity).

(* ベクトル空間の直和 *)
(**
- Prop で定義する例
Definition DirectSum (V W : VS) := fun (x : M) => V x \/ W x.

- VS = {set M} で定義する例。
Definition DirectSum (V W : VS) := fun (x : M) => (x \in V :|: W).

今回は、VS : M -> bool で定義したうえで、V x = (x \in V) を使ってみる。
*)
Definition DirectSum (V W : VS) := fun (x : M) => (x \in V) || (x \in W).
Notation "V + W" := (DirectSum V W) (at level 50, left associativity).

(* これは自明である。 *)
Lemma inP (x : M) (V : VS) : V x = (x \in V).
Proof.
  done.
Qed.

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
  rewrite [y \in o]Bool.negb_involutive_reverse.
  by rewrite EmptySet orFb.
Qed.

Lemma DirectSumV0 : forall (V : VS),
    V + o = V.
Proof.
  move=> V.
  apply: functional_extensionality => y.  
  rewrite /ImgOf /DirectSum.
  rewrite [y \in o]Bool.negb_involutive_reverse.
  by rewrite EmptySet orbF.
Qed.

Lemma DirectSumXV : forall (V : VS),
    X + V = X.
Proof.
  move=> V.
  apply: functional_extensionality => y.
  rewrite /ImgOf /DirectSum.
  rewrite inP.
  by rewrite MotherSet.
Qed.

Lemma DirectSumVX : forall (V : VS),
    V + X = X.
Proof.
  move=> V.
  apply: functional_extensionality => y.  
  rewrite /ImgOf /DirectSum.
  rewrite inP.
  by rewrite MotherSet orbT.
Qed.

(********)

Definition Img (f : M -> M) :=  ImgOf f X.

(* 準同型定理 : 証明される事実だが, 準同型性として使います. *)
Parameter Ker : (M -> M) -> VS.
Axiom ImgKer : forall (f : M -> M), f @ (Ker f) = o.

(* exists の equal に関する補題 *)
Check eq_existsb
  : forall (T : finType) (P1 P2 : pred T),
    P1 =1 P2 -> [exists x, P1 x] = [exists x, P2 x].
Check eq_existsb_in
  : forall (T : finType) (D P1 P2 : pred T),
    (forall x : T, D x -> P1 x = P2 x) ->
    [exists (x | D x), P1 x] = [exists (x | D x), P2 x].

Lemma eq_existsb_in'
  : forall (T : finType) (D P1 P2 : pred T),
    [exists (x | D x), P1 x] = [exists (x | D x), P2 x] ->
    (forall x : T, D x -> P1 x = P2 x).
Proof.
Admitted.

(*
Lemma test (x : M) (f : M -> M) X Y :
  [exists x0, (x == f x0) && X x0] = [exists x0, (x == f x0) && Y x0] -> X = Y.
Proof.
  move/eq_existsb_in' => H.
  apply: functional_extensionality => y.
  move: (H y) => H'.
  apply: H'.
Admitted.
*)

(* eq_existsb_in の逆が成り立つとしても。 *)
(* これは証明できないだろう。 *)
(* forall x,P(x) -> exists x,P(x) だが、逆は成り立たない。 *)
Lemma fex f X Y : f @ X = f @ Y -> X = Y.
Proof.
  rewrite /ImgOf => H.
  apply: functional_extensionality => x.
  have EQ (f' g' : M -> bool) y : f' = g' -> f' y = g' y by move=> ->.
  move: (@EQ _ _ x H).
  move/eq_existsb_in' => H'.
  rewrite 2!inP.
  rewrite H' //.
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

(* *** *)

(* これは、オリジナルから無変更で証明できる。 *)
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
  (forall (W : VS), W \subset V -> f @ W = W -> W = V \/ W = o).

(* END *)
