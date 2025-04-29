From mathcomp Require Import all_ssreflect.
From mathcomp Require Import all_classical.
Require Import Coq.Logic.Classical.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Definition set (A : Type) := A -> Prop.

Definition surjective {A B : Type} (f : A -> B) :=
  forall b : B, exists a : A, f a = b.

(* Rocq *)
(**
GPT-4-turbo モデル（2025年4月時点）の出力を動くようにしたもの。
*)
Theorem Cantor : forall (A : Type) (f : A -> set A), ~ surjective f.
Proof.
  intros A f H.
  
  (* 対角線集合を定義する。 *)
  set (D := fun x : A => (f x) x).          (* 対角線 *)
  Check D : set A.
  set (notD := fun x : A => ~ (f x) x).     (* 対角線の否定 *)
  Check notD : set A.
  
  (* H によれば、notDに対しても存在する a がある *)
  Check H notD : exists a : A, f a = notD.
  destruct (H notD) as [a Ha].              (* 前提のexistは場合分する。 *)
  
  (* a について考える *)
  unfold notD in Ha.
  (* Ha : f a = fun x => ~ (f x) x *)
  Check f_equal (fun g => g a) Ha
    : f a a = (~ f a a). (* Ha の両辺に a を適用する。 *)
  
  specialize (f_equal (fun g => g a) Ha).
  intro H1.
  unfold not in H1.
  (* H1 : (f a) a = ~ (f a) a *)
  Check (classic ((f a) a)) : f a a \/ ~ f a a.
  destruct (classic ((f a) a)) as [Hfaa | Hfaa].
  - (* (f a) a が真の場合 *)
    rewrite H1 in Hfaa.
    apply Hfaa.
    now rewrite H1.
  - (* (f a) a が偽の場合 *)
    apply Hfaa.
    rewrite H1.
    now apply Hfaa.
Qed.


(* MathComp風 *)
(**
GPT-4-turbo モデル（2025年4月時点）の出力を動くようにしたもの。
*)
Theorem Cantor' : forall (A : Type) (f : A -> set A), ~ surjective f.
Proof.
  move=> A f H.
  
  (* 対角線集合を定義する。 *)
  set (D := fun x : A => (f x) x).          (* 対角線 *)
  Check D : set A.
  set (notD := fun x : A => ~ (f x) x).     (* 対角線の否定 *)
  Check notD : set A.
  
  (* H によれば、notDに対しても存在する a がある *)
  Check H notD : exists a : A, f a = notD.
  case: (H notD) => a Hfa.              (* 前提のexistは場合分する。 *)
  (* a について考える *)
  rewrite /notD in Hfa.
  Check Hfa : f a = fun x => ~ (f x) x.
  Check f_equal (fun g => g a) Hfa : f a a = (~ f a a). (* Hfa の両辺に a を適用する。 *)
  move: (f_equal (fun g => g a) Hfa) => {Hfa} H1. (* ここの箇所が単純になる。 *)
  Check H1 : (f a) a = ~ (f a) a.
  
  Check (classic ((f a) a)) : f a a \/ ~ f a a.
  case: (classic ((f a) a)) => [Hfaa | Hnotfaa].
  - (* (f a) a が真の場合 *)
    rewrite H1 in Hfaa.
    apply Hfaa.
    now rewrite H1.
  - (* (f a) a が偽の場合 *)
    apply Hnotfaa.
    rewrite H1.
    now apply Hnotfaa.
Qed.

(* END *)
