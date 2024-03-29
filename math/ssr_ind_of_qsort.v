(**
Quick Sort (クイックソート）の帰納法

- クイックソートは半順序でもソート可能であることをCoq/SSReflectで証明する

https://qiita.com/nekonibox/items/eabcbc1bb11b1a472a63


- Coq/SSReflectで{}を使わずに完全帰納法を適用する

https://qiita.com/nekonibox/items/8147291e9fd483e3d579
*)

From mathcomp Require Import all_ssreflect.
From common Require Import ssromega.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Import Recdef.

Section filter.
  Variable T : Type.

(**
## filer関数についての補題
*)
(*
  Lemma filter_size {x : T} {s : seq T} (R' : rel T) :
    size [seq y <- s | R' y x] <= size s.
  Proof.
    elim: s => //= y s IHs.
    case H : (R' y x) => //=.
      by ssromega.
  Qed.
*)
  Lemma filter_size {x : T} {s : seq T} (R : rel T) :
    size [seq y <- s | R y x] <= size s.
  Proof.
    by rewrite size_filter count_size.
  Qed.

End filter.

Section qsort.
  Variable T : Type.
  Variable R : rel T.

(**
## Quick Sort 関数
*)
  Function qsort (s : seq T) {measure size s} :=
    if s is x :: s' then
      qsort [seq y <- s' | R y x] ++ x :: qsort [seq y <- s' | ~~ R y x]
    else
      [::].
  Proof.
    - move => _ x s _ /=. apply /ltP.
      by rewrite ltnS size_filter count_size.
    - move => _ x s _ /=. apply /ltP.
      by rewrite ltnS size_filter count_size.
  Defined.

(**
## Function コマンドのつくる qsort_ind は複雑なので、自作する。
*)
  Lemma ubnP m : {n | m < n}.     (* 最新の ssrnat.v で導入された。 *)
  Proof. by exists m.+1. Qed.
  
  Lemma my_qsort_ind (P : seq T -> Prop) :
    P [::]
    ->
    (forall x s,
        P [seq y <- s | R y x] -> P [seq y <- s | ~~ R y x] -> P (x :: s))
    ->
    forall s, P s.
  Proof.
    move=> Hnil Hcons s.
(*
  シノニムを使う例（避けるべき）：
    elim : s {-2}s (leqnn (size s)) => [|xs s IHs] [] //= xl l Hsize.
    Undo 1.
    elim : (size s) {-2}s (leqnn (size s)) => [|n IHn] [] //= xl l Hsize.
    Undo 1.
*)
    (* リストの長さに対する帰納法をおこなう。 *)
    have [n] := ubnP (size s).
    elim: n s => [| n IHn] [| xs s] //= Hsize.
    apply: Hcons.
    Check leq_ltn_trans (filter_size R).
    - exact: IHn (leq_ltn_trans (filter_size R) Hsize).
    - exact: IHn (leq_ltn_trans (filter_size (fun x y => ~~ R x y)) Hsize).
  Qed.
  
(**
## ソートされている状態かどうかを判定する述語
*)
  Fixpoint mysorted (s : seq T) :=
    if s is x :: s' then
      all (fun y => ~~ R y x || R x y) s' && mysorted s'
    else
      true.

(**
## 補題
*)
  Lemma all_qsort p s : all p (qsort s) = all p s.
  Proof.
    elim/my_qsort_ind : s => [| x s] //=.
    rewrite [qsort (_ :: _)]qsort_equation all_cat /= => -> ->.
    case: (p x) =>/=; last exact: andbF.
    elim: s =>[| y s] //=.
    case: ifP => _ /= <-; case: (p y) => //=.
    exact: andbF.
  Qed.

  Lemma mysorted_cat s1 s2 :
    mysorted s1 -> mysorted s2 ->
    all (fun x => all (fun y => ~~ R y x || R x y) s2) s1 ->
    mysorted (s1 ++ s2).
  Proof.
    elim: s1 => [| x s1 IHs1] //=.
    rewrite all_cat => /andP [->] Hs1 Hs2 /andP [->] /=.
    exact: IHs1.
  Qed.

(**
## qsort関数によって、ソートされることの証明
 *)
  Hypothesis (Htrans : transitive R).

  Lemma qsort_sorted s : mysorted (qsort s).
  Proof.
    elim/my_qsort_ind : s => [| x s IHs1 IHs2] //.
    rewrite qsort_equation.
    apply: mysorted_cat => //=.
    - rewrite IHs2 andbT all_qsort.
      by apply: (sub_all _ (filter_all _ _)) => y ->.
    - rewrite all_qsort.
      apply: (sub_all _ (filter_all _ _)) => y Hyx.
      rewrite Hyx orbT all_qsort /=.
      apply: (sub_all _ (filter_all _ _)) => z.
      case Hzy : (R z y)=>//.
      by rewrite (Htrans Hzy Hyx).
  Qed.

End qsort.

(* END *)
