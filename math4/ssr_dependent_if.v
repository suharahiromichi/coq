(**
Lean で多用されている Dependent if-then-else を Coq/MathComp で定義してみた

# Lean 側の文献

## dependent if-then-else

- https://leanprover.github.io/theorem_proving_in_lean/type_classes.html

- https://github.com/leanprover/lean4/blob/master/src/Init/Prelude.lean

- https://github.com/leanprover/lean4/blob/master/src/Init/Core.lean

## 古典公理

- https://github.com/leanprover/lean4/blob/master/src/Init/Classical.lean

- Mathematics in Lean

4.2 Functions

# MathComp 側の文献

## 古典公理

- proj1_sig について ssrcoq.pdf
Dependent Pairs

- choice について Karate-coq.pdf
4.1.4 Consequences of Classical Axioms

- https://gitlab.com/proofcafe/karate/-/blob/main/4.1_Axioms.v 個人メモ
 *)
From mathcomp Require Import all_ssreflect.
From mathcomp Require Import all_classical.
Require Import ProofIrrelevance.            (* proof_irrelevance *)

Require Import Epsilon.                     (* epsilon_statement *)
Require Import FunctionalExtensionality.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* 全射 *)
Definition surjective {B A : Type} (f : A -> B) := forall b : B, exists a : A, f a = b.
Check @surjective : forall B A : Type, (A -> B) -> Prop.

(**
# Dependent if-then-else の定義

``dite c t e``

命題 c は決定可能であるとする。
命題 c が成立するときに、その証明 h を then節に適用して (t h) を得る。
命題 ~ c が成立するときに、その証明 hc を else節に適用して (e hc) を得る。
 *)
Definition dite {a : Type} (c : Prop) (t : c -> a) (e : ~ c -> a) : a.
Proof.
  case: (pselect c).                      (* 排中律で場合分けする。 *)
  - by apply: t.
  - by apply: e.
Defined.
Arguments dite {a} c t e.
Notation "'if' h 'of' c 'then' t 'else' e" :=
  (dite c (fun h => t) (fun h => e)) (at level 200).
(**
if-then-else らしい構文糖衣を用意する。h は単なる束縛変数であり、
c の真偽を決めたときの証明そのものではないことに注意すること。
もっとも ``h : c`` または ``h : ~ c`` であることに間違いはない。
*)

(**
## Lean にある補題

- dif_pos c t e == c が成立する場合、``hc : c`` として ``dite c t e = t hc`` である。
- dif_neg c t e == ~ c が成立する場合、``hnc : ~ c`` として ``dite c t e = e hnc`` である。

どちらも、条件が成立しない場合は前提矛盾 (absure) とする。
ProofIrrelevance が証明に必要になる。なぜなら、
c が成立するの証明項 hc と、t に与えられる hc は同じものでなく、
c が成立しないの証明項 hnc と、e に与えられる hnc は同じものでないため。
*)
Lemma dif_pos {a : Type} (c : Prop) (hc : c) (t : c -> a) (e : ~ c -> a) : dite c t e = t hc.
Proof.
  rewrite /dite.
  case: pselect => h //=.
  by rewrite (proof_irrelevance c h hc).
Qed.

Lemma dif_neg {a : Type} (c : Prop) (hnc : ~ c) (t : c -> a) (e : ~ c -> a) : dite c t e = e hnc.
Proof.
  rewrite /dite.
  case: pselect => h //=.
  by rewrite (proof_irrelevance (~ c) h hnc).
Qed.

(**
# 使用例：左逆写像を定義する。
*)
Section a.
(**
定義域 A と値域 B を考える。A は空集合でないものとする。
*)
  Variable A B : Type.
  Variable hnonempty : inhabited A.
  
(**
## 関数 f の左逆写像を得る。

関数 ``f : A -> B`` に対して、任意の ``b : B`` について、
``f a = b`` なる ``a : A`` が存在する場合は、``exists a : A, f a = b`` を満たす a を取り出す。選択公理。
``a : A`` が存在しない場合は、A に含まれる適当な要素を返す。
これは逆写像 ``B -> A`` が A を返せばよく、無理矢理全域化するためである。

Notationのif-then-elseを使った例
*)
  Definition linv (f : A -> B) (b : B) : A :=
    if H of exists a : A, f a = b then proj1_sig (cid H) (* lean の Classical.choose h *)
    else inhabited_witness hnonempty.       (* lean の default *)
  
  Section d.
    Variable f : A -> B.
    Variable y : B.
    Check linv f y : A.
  End d.
  
(**
## 左逆写像が仕様を満たすことの証明
*)
  Lemma linv_spec (f : A -> B) (y : B) : (exists x, f x = y) -> f (linv f y) = y.
  Proof.
    case=> x fx_y.
    rewrite /linv /dite.
    case: pselect => H //=.               (* 排中律で場合分けする。 *)
    (* ``h : exists x, f x = y`` が成立する場合 *)
    - by rewrite (proj2_sig (cid H)). (* lean の Classical.choose_spec h *)
    (* ``~ (exists x, f x = y)`` が成立する場合 *)
    - exfalso.                              (* default は使わない。 *)
      apply: H.
      by exists x.                          (* 前提矛盾 *)
  Qed.
  
(**
## 補題を使って証明した例
*)
  Lemma linv_spec' (f : A -> B) (y : B) : (exists x, f x = y) -> f (linv f y) = y.
  Proof.
    case=> x fx_y.
    rewrite /linv dif_pos // => [| H].
    - by exists x.
    - by rewrite (proj2_sig (cid H)).
  Qed.

End a.

(**
# おまけ 1 : 左逆写像 を直接求める
*)
Section b.

  Variable A B : Type.

  Definition linv' (hnonempty : inhabited A) (f : A -> B) : B -> A.
  Proof.
    move=> b.
    case: (pselect (exists a, f a = b)) => H.
    - by apply: (proj1_sig (cid H)).
    - by apply: inhabited_witness.
  Defined.

End b.

Goal linv = linv'.
Proof.
  done.
Qed.

(**
# 問2: 単射から逆方向の全射

次に `f : A → B` が単射であれば、逆方向の全射 `g : B → A` も存在することを示しましょう。
*)
Section c.
  
  Variable A B : Type.
  
  Lemma inj_to_surj (f : A -> B) :
    inhabited A -> injective f -> exists g : B -> A, surjective g.
  Proof.
    move=> hnonempty hinj.
    pose g := linv hnonempty f.
    
    have gdef : forall a, g (f a) = a.
    {
      move=> a.
      rewrite /g /linv /dite.
      
      case: (pselect (exists a0, f a0 = f a)) => H.
      (* H が成り立つ場合 *)
      - apply: hinj.
        by rewrite (projT2 (cid H)).
        
      (* H が成り立たない場合。 *)
      - exfalso.
        apply: H.
        by exists a.
    }.
    exists g.
    rewrite /surjective => a.
    exists (f a).
    by apply: gdef.
  Qed.

End c.

(* END *)
