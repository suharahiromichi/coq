(**
An introduction to small scale reflection in Coq

6. Finite objects in SSReflect

http://hal.inria.fr/docs/00/55/53/79/PDF/main-rr.pdf
*)

Require Import ssreflect ssrfun ssrbool eqtype ssrnat div seq.
Require Import path choice fintype tuple finfun finset.

(* Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.
*)

(**
6.1 Finite types
6.1.1 Finite types constructions
*)

Lemma bool_enumP : Finite.axiom [:: false; true].
(* テキストは [:: true, false] だが、変えてみた。 *)
Proof.
    by case.
Qed.
Definition bool_finMixin :=
  FinMixin bool_enumP.
Canonical Structure bool_finType :=         (* finType の定義 *)
  FinType bool bool_finMixin.

Print Finite.axiom.
(**
Finite.axiom (T : eqType) (e : seq e) :=
forall x, count (@pred1 T x) e = 1.

T型を要素とする配列eは、Tの任意の要素が1つだけある。
つまり、T型の要素を列挙した配列。
*)

(**
Exercise 6.1.1 finType on the unit type
*)
Lemma unit_enumP : Finite.axiom [:: tt].
Proof.
    by [].
Qed.
Definition unit_finMixin :=
  FinMixin unit_enumP.
Canonical Structure unit_finType :=         (* finType の定義 *)
  FinType unit unit_finMixin.

(**
Exercise 6.1.2 opt.
*)

Definition tuto_option_enum (T : finType) :=
  None :: [seq Some i | i <- Finite.enum T].
(* テキストの定義は、 None :: map some (Finite.enum T). だが *)

Lemma tuto_option_enumP : forall T : finType,
                       Finite.axiom (tuto_option_enum T).
Proof.
  move=> T.
  rewrite /Finite.axiom => x.
  case H : x.                               (* by x. *)
  - rewrite /= count_map /=.                (* x = Some a *)
            nat_norm.
    rewrite enumP.
      (*
    rewriteの様子を詳しく見る。
    have H' := enumP.
    rewrite /Finite.axiom in H'.
    rewrite /pred1 in H'.
    rewrite /preim /=.
            rewrite H'.
     *)
      by [].
  - rewrite /= count_map /=.                (* x = None *)
            nat_congr.
    rewrite count_pred0.
      (*
    rewriteの様子を詳しく見る。
    have H' := count_pred0.
    rewrite /pred0 in H'.
    rewrite /preim /=.
    rewrite H'.
    *)
      by [].
Qed.
(* このふたつの rewrite はまとめて、(count_pred0, enumP) と書ける。 *)

Definition tuto_option_finMixin (T : finType) :=
  FinMixin (tuto_option_enumP T).

Canonical Structure tuto_option_finType (T : finType) :=
  FinType (option T) (tuto_option_finMixin T).

(**
Exercise 6.1.3
*)
Definition tuto_sum_enum (T1 T2 : finType) : seq (T1 + T2) :=
  [seq @inl T1 T2 x | x <- Finite.enum T1]
    ++ [seq @inr T1 T2 y | y <- Finite.enum T2].
(*
(Finite.enum T1) ++ (Finite.enum T2)
では、++の左右で型が違うので、appendできない。
また、@inl T1 T2 は、inl でよい。inrも。
*)

Lemma tuto_sum_enum_uniq : forall T1 T2, uniq (tuto_sum_enum T1 T2).
Proof.
  move=> T1 T2.
  rewrite cat_uniq -!enumT.
  rewrite !(enum_uniq, map_inj_uniq);       (* よくわかならい。 *)
    try by move=> ? ? [].                   (* _にするとinjective が残ってしまう。 *)
  rewrite andbT andTb.                      (* true をとる。 *)
  apply/hasP => [] [H1 H2 H3].
  move/mapP in H2.
  case: H2 => x H21 H22.
  move/mapP in H3.
  case: H3 => y H31 H32.
  rewrite H22 in H32.
    (* Goal : inr x = inl y *)
  by [].
Qed.  

Definition tuto_sum_finMixin (T1 T2 : finType) :=
  Eval hnf in UniqFinMixin (tuto_sum_enum_uniq T1 T2) (@mem_sum_enum T1 T2).

Canonical Structure sum_finType (T1 T2 : finType) :=
  Eval hnf in FinType (T1 + T2) (tuto_sum_finMixin T1 T2).

(**
Exercise 6.1.4 
*)

(**
6.1.2 Cardinality, set operations
*)
Section OpsTheory.
Variable T : finType.
Implicit Types A B C P Q : pred T.
Implicit Types x y : T.
Implicit Type s : seq T.

Lemma card0 : #|@pred0 T| = 0.
Proof.
    by rewrite cardE enum0.
Qed.

Lemma cardT : #|T| = size (enum T).
Proof.
    by rewrite cardE.
Qed.

Lemma card1 : forall x, #|pred1 x| = 1.
Proof.
    by move=> x; rewrite cardE enum1.
Qed.

(**
Exercise 6.1.5
*)
Definition pred0b (T : finType) (P : pred T) := #|P| == 0.

Lemma tuto_eq_card0 : forall A,
                        A =i pred0 -> #|A| = 0.
Proof.
  move=> A.
  rewrite -card0.                           (* #|A| = #|pred0| *)
  move=> H.
  rewrite !cardE.
  rewrite (eq_enum H).
  by [].
Qed.

Lemma tuto_card0_eq : forall A,
                        #|A| = 0 -> A =i pred0.
Proof.
  move=> A.
  move=> H.
  move=> x.                                 (* ゴールが "=i"なら、強引に！ *)
  rewrite !cardE in H.
  rewrite /in_mem /mem /=.
  apply/negP. rewrite /not => Hc.
  admit.
Qed.
  
Lemma tuto_pred0P : forall P, reflect (P =1 pred0) (pred0b T P).
Proof.
  move=> P.
  apply (iffP idP).
(*
これよりも簡単！
  apply/(@iffP (pred0b T P)).
  - by apply/idP.
*)
  - rewrite /pred0b => /eqP H.
    by apply: tuto_card0_eq.
  - move=> H.
    apply (@eq_card0 T P) in H.
    rewrite /pred0b.
    by apply/eqP.
Qed.

(**
Exercise 6.1.6
*)
Lemma tuto_cardUI : forall A B,
                      #|[predU A & B]| + #|[predI A & B]| = #|A| + #|B|.
Proof.
  move=> A B.
  rewrite !cardE.
  rewrite -!count_filter.
  rewrite count_predUI.
    by [].
Qed.

Lemma tuto_eq_card : forall A B, A =i B -> #|A| = #|B|.
Proof.
  move=> A B H.
  rewrite !cardE.
  rewrite (eq_enum H).
  by [].
Qed.

(* END *)
