From mathcomp Require Import all_ssreflect.
From mathcomp Require Import all_classical.
Require Import Coq.Logic.Classical.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(**
カントールの定理：
 *)
(**
集合αの冪集合の濃度は、もとの集合αの濃度よりの真に大きい。
そのことを「集合αからαの冪集合への関数fは全射ではない」で示す。
*)

Definition set (A : Type) := A -> Prop.

Definition surjective {A B : Type} (f : A -> B) :=
  forall b : B, exists a : A, f a = b.

(* Rocq *)
(**
GPT-4-turbo モデル（2025年4月時点）の出力を動くようにしたもの。
*)
Theorem Cantor : forall (A : Type) (f : A -> set A), ~ surjective f.
Proof.
  intros A f Hsurj.
  
  (* 対角線集合を定義する。 *)
  set (D := fun x : A => (f x) x).          (* 対角線 *)
  Check D : set A.
  set (B := fun x : A => ~ (f x) x).        (* 対角線の否定 *)
  Check B : set A.
  
  (* Hsurj によれば、B に対しても存在する a がある *)
  Check Hsurj B : exists a : A, f a = B.
  destruct (Hsurj B) as [a Ha].              (* 前提のexistは場合分する。 *)
  
  (* a について考える *)
  unfold B in Ha.
  (* Ha : f a = fun x => ~ (f x) x *)
  Check f_equal (fun g => g a) Ha
    : (f a) a = ~ (f a) a.            (* Ha の両辺に a を適用する。 *)
  
  specialize (f_equal (fun g => g a) Ha).
  intro H1.
  unfold not in H1.
  (* H1 : (f a) a = ~ (f a) a *)
  Check (classic ((f a) a)) : (f a) a \/ ~ (f a) a.
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
  move=> A f Hsurj.
  
  (* 対角線集合を定義する。 *)
  set (D := fun x : A => (f x) x).          (* 対角線 *)
  Check D : set A.                          (* D = {a ⊂ A | a ∈ f(a)} *)
  set (B := fun x : A => ~ (f x) x).        (* 対角線の否定 *)
  Check B : set A.                          (* B = {a ⊂ A | a ∉ f(a)} *)
  
  (* H によれば、B に対しても存在する a がある *)
  Check Hsurj B : exists a : A, f a = B.
  case: (Hsurj B) => a Hfa.            (* 前提のexistは場合分する。 *)
  (* a について考える *)
  rewrite /B in Hfa.
  Check Hfa : f a = fun x => ~ (f x) x.
  Check f_equal (fun g => g a) Hfa : (f a) a = ~ (f a) a. (* Hfa の両辺に a を適用する。 *)
  move: (f_equal (fun g => g a) Hfa) => {Hfa} H1. (* ここの箇所が単純になる。 *)
  Check H1 : (f a) a = ~ (f a) a.
  
  Check (classic ((f a) a)) : (f a) a \/ ~ (f a) a.
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

(**
集合A の濃度が、その冪集合2^A の濃度より小さいことを示す。
全単射である関数 f : A -> 2^A が存在するなら、A と 2^A の濃度は等しい。
全射である関数 f : A -> 2^A が存在しないなら、A の濃度は 2^A より小さい。

対角線論法で、全射であることの反例を作る。
次の表の行を集合(冪集合2^Aの要素と)見て、1が要素がある、0は要素がないことを示す。

         |--------- A --------->
-          a1  a2  a3  a4
|   f(a1)  1   0   0   0   .    |  f(a1) = {a1}    
|   f(a2)  0   0   1   0   .    |  f(a2) = {a3}    
2^A f(a3)  0   1   0   0   .    |  f(a3) = {a2}    
|   f(a4)  0   0   0   1   .    |  f(a4) = {a4}    ここまでは単射である。
|          .   .   .   .   .    ↓ ....................
----------------------------------------------------
     D     1   0   0   1   .       対角線、存在するかもしれない。
     B     0   1   1   0   .       対角線の否定、存在し得ない。


まず、関数 f が単射である。その理由は以下による。
a1 ∈ f(a1) ⊂ 2^A であるところの a1 ∈ A が存在する。f(a1) = { a1 } と考えられる。
一般に、
a  ∈ f(a ) ⊂ 2^A であるところの a  ∈ A が存在する。f(a)  = { a  } と考えられる。

対角線Dを考える。a  ∈ f(a) であるところの a  ⊂ A
D = {a ⊂ A | a ∈ f(a)}


対角線 D の否定を考える。a ∉ f(a) であるところの a  ⊂ A
B = {a ⊂ A | a ∉ f(a)}
これは、存在し得ない。

B ⊂ 2^A だが、f の値としてとり得ないものが存在する。
よって、f は単射であっても、全射ではない。つまり全単射ではない。
*)

(* END *)
