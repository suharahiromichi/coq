(**
Coq/SSReflect/MathComp による定理証明

第4章 MathComp ライブラリの基本ファイル

4.5 fintype.v --- 有限型のライブラリ

======

2018_12_10 @suharahiromichi
 *)

From mathcomp Require Import all_ssreflect.
From mathcomp Require Import perm.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(**
# はじめに

本節はテキストを参照しながら、MathComp のソースコードに沿って説明していきます。
ソースコードが手元にあるならば、それも参照してください。
opamでインストールしている場合は、ソースは、たとえば以下にあります。

~/.opam/4.07.1/lib/coq/user-contrib/mathcomp/ssreflect/fintype.v
*)

(**
# finType とは

要素の列挙(enum)のリストと、enumの要素に重複がないことを公理とする。
具体的なインスタンスを生成するときに、この公理は証明済みの命題に置き換える。
*)

(**
## balle_finType
*)

Inductive balle :=
| rouge  (* red ball, la balle rouge, 紅玉 *)
| blanc. (* white ball, la balle blanc, 白玉 *)

Definition balle2bool (b : balle) : bool :=
  match b with
  | rouge => true
  | blanc => false
  end.

Definition bool2balle (b : bool) : balle :=
  match b with
  | true => rouge
  | false => blanc
  end.

Lemma inj_b2b : injective balle2bool.
Proof. by case; case. Qed.

Lemma can_b2b : cancel balle2bool bool2balle.
Proof. by case. Qed.

Definition balle_eqMixin := InjEqMixin inj_b2b.
Canonical balle_eqType := EqType balle balle_eqMixin.
Definition balle_choiceMixin := CanChoiceMixin can_b2b.
Canonical balle_choiceType := ChoiceType balle balle_choiceMixin.
Definition balle_countMixin := CanCountMixin can_b2b.
Canonical balle_countType := CountType balle balle_countMixin.


(**
balle の本来の定義を使ってfinTypeを定義する。
 *)
Definition balle_enum := [:: rouge; blanc].

Lemma balle_uniq : forall x, count_mem x balle_enum = 1.
Proof. by case. Qed.

Definition balle_finMixin' := @FinMixin balle_countType balle_enum balle_uniq.
Canonical balle_finType' := FinType balle balle_finMixin'.

(**
balle2bool の単射性をつかってfinTypeを定義する。
 *)
Definition balle_finMixin := CanFinMixin can_b2b.
Canonical balle_finType := FinType balle balle_finMixin.

(**
# その他の finType のインスタンス
*)

Check bool_finType       : finType.         (* bool型 *)
Check ordinal_finType 5  : finType.         (* 濃度5の順序数 *)

Check tuple_finType 3 (ordinal_finType 5)
  : finType.                (* 濃度5の順序数を要素とする寸法3のリスト *)

Check finfun_finType (ordinal_finType 5) (ordinal_finType 6)
  : finType. (* 濃度5の順序数を引数、濃度6の順序数を値とする関数である。 *)
(* finfun は、一般に値は任意の型でよいので、finfun が finType とは限らない。 *)

Check set_finType (ordinal_finType 5) : finType. (* 濃度5の順序数を要素とする集合 *)
(* finset は、finType型を引数、bool型を値とする関数 finfun である。 *)

Check perm_finType (ordinal_finType 5) : finType. (* 濃度5の順序数の順列 *)

(**
# 濃度 Cardinal が定義されている。
*)

Goal #| 'I_5  | = 5.
Proof.
    by rewrite cardE size_enum_ord.
Qed.

Check cardE : forall (T : finType) (A : predPredType T), #|A| = size (enum A).
Check eq_card : forall (T : finType) (A B : predPredType T), A =i B -> #|A| = #|B|.
Check eq_card_trans : forall (T : finType) (A B : predPredType T) (n : nat),
    #|A| = n -> B =i A -> #|B| = n.
Check card0 : forall T : finType, #|pred0| = 0.
Check card1 : forall (T : finType) (x : T), #|pred1 x| = 1.
Check eq_card0 : forall (T : finType) (A : predPredType T), A =i pred0 -> #|A| = 0.
Check eq_card1
  : forall (T : finType) (x : T) (A : predPredType T), A =i pred1 x -> #|A| = 1.
Check cardUI : forall (T : finType) (A B : predPredType T),
    #|[predU A & B]| + #|[predI A & B]| = #|A| + #|B|.
Check cardID : forall (T : finType) (B A : predPredType T),
    #|[predI A & B]| + #|[predD A & B]| = #|A|.
Check cardC : forall (T : finType) (A : predPredType T), #|A| + #|[predC A]| = #|T|.      Check cardU1 : forall (T : finType) (x : T) (A : predPredType T),
    #|[predU1 x & A]| = (x \notin A) + #|A|.

(**
濃度が存在することの証明：

https://github.com/suharahiromichi/coq/blob/master/pearl/ssr_ex_card.v
 *)

(**
# forall と exists
*)

Goal [forall x in 'I_5, x < 5].
Proof.
  apply/forallP.
    (* forall x, (x \in 'I_5) ==> (x < 5) *)
    by case=> m i.
Qed.  

Definition p0 : 'I_5. Proof. by apply: (@Ordinal 5 0). Defined.
Definition p4 : 'I_5. Proof. by apply: (@Ordinal 5 4). Defined.

Goal [exists x in 'I_5, x == p0].
Proof.
  apply/existsP.
    (* exists x, (x \in 'I_5) && (x == p0) *)
    by exists p0.
Qed.

(**
# \subset と \proper
*)

Goal 'I_5 \proper 'I_5.
Proof.
  apply/properP.
  (* I_5 \subset 'I_5 /\ (exists2 x : ordinal_finType 5, x \in 'I_5 & x \notin 'I_5) *)
Admitted.

Goal 'I_5 \subset 'I_5.
Proof.
  apply/subsetP.
  (* {subset 'I_5 <= 'I_5} *)
Admitted.

Goal 'I_5 \subset 'I_5.
Proof. done. Qed.

(**
## A \subset B

- A \subset B の定義は fintype.v にある。 #| predD A B | == 0 と定義。

- predD A B の定義は ssrbool.v にある。 fun x => ~~ A x && B x と定義。
*)
Goal #| predD 'I_5 'I_5 | == 0.
Proof.
  Admitted.


(**
## {subset A <= B}

- {subset A <= B} の定義は ssrbool.v にある。
  forall x : T, in_mem x p1 -> in_mem x p2.
*)

Goal forall x, in_mem x (mem 'I_5) -> in_mem x (mem 'I_5).
Proof.
  done.
Qed.


(**
## ほしいもの
 *)
Goal [forall x, (x \in 'I_5) ==> (x \in 'I_5)].
Proof.
  Admitted.


Section Test.
  Variable T : finType.
  
  Lemma mySubsetP (s1 s2 : pred T) :
    s1 \subset s2 <-> (forall x, x \in s1 -> x \in s2).
  Proof.
    rewrite subset_disjoint /disjoint.
    split.
    - move/pred0P => H.
      move=> x Hs1.
      move: (H x) => {H} /= /eqP.
      rewrite inE eqbF_neg negb_and /=.
      move/orP => [Hn1 | Hnn2].
      + by move/negP : Hn1.
      + by rewrite Bool.negb_involutive in Hnn2.

    - move=> H.
      apply/pred0P => x.
      apply/andP => [[H1 Hn2]].
      rewrite inE /= in Hn2.
      move/negP in Hn2.
        by apply/Hn2/H.
  Qed.
  
(**
## boolean な論理式での証明
 *)

  Lemma mySubsetE (s1 s2 : pred T) :
    s1 \subset s2 = [forall x, (x \in s1) ==> (x \in s2)].
  Proof.
    apply/idP/idP.
    - move=> H.
      apply/forallP => x.
      apply/implyP.
      by apply/mySubsetP : x.

    - move=> H.
      apply/mySubsetP => x.
      move/forallP in H.
      by move: (H x) => {H} /implyP H /=.
  Qed.

End Test.

Definition s1 (x : 'I_5) := nat_of_ord x == 0.
Definition s2 (x : 'I_5) := x < 4.

Goal s1 \subset s2.
Proof.
  rewrite mySubsetE.
  apply/forallP=> x.
  apply/implyP.
  move=> H.
Admitted.  



(**
# Ordinal
 *)

(**
## val または  nat_of_ord で自然数の値を取り出す。後者はコアーション。
*)
Check val : 'I_5 -> nat.
Check @nat_of_ord 5  : 'I_5 -> nat.

Compute val p0.                             (* = 0 *)
Compute nat_of_ord p0.                      (* = 0 *)

Compute val p4.                             (* = 4 *)
Compute nat_of_ord p4.                      (* = 4 *)

Compute p0 < 4.                     (* 不等式はコアーションが効く。 *)


(**
## 補題 val と nat_of_ord が単射である。
*)

Check @val_inj : forall (T : Type) (P : pred T) (sT : subType P), injective val.
Check ord_inj : forall n : nat, injective (nat_of_ord (n:=n)).

(**
## Ordinal についての補題：
*)

Check ltn_ord : forall (n : nat) (i : 'I_n), i < n.
Check leq_ord : forall (n' : nat) (i : 'I_n'.+1), i <= n'.

Check card_ord : forall n : nat, #|'I_n| = n.

Check widen_ord_proof : forall (n m : nat) (i : 'I_n), n <= m -> i < m.
Check cast_ord_proof : forall (n m : nat) (i : 'I_n), n = m -> i < m.

(* END *)
