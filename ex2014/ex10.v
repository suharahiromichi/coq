Require Import ssreflect.

(**
# 第2回 証明済みの定理の利用・量化や等式を含む命題に関する証明 (2014/04/13)

http://qnighy.github.io/coqex2014/ex2.html

## 課題10 (種別:C / 締め切り : 2014/05/04)

次の定理を証明せよ。
*)

Parameter G : Set.
Parameter mult : G -> G -> G.
Notation "x * y" := (mult x y).
Parameter one : G.
Notation "1" := one.
Parameter inv : G -> G.
Notation "/ x" := (inv x).
(* Notation "x / y" := (mult x (inv y)). *) (* 使ってもよい *)

Axiom mult_assoc : forall x y z, x * (y * z) = (x * y) * z.
Axiom one_unit_l : forall x, 1 * x = x.
Axiom inv_l : forall x, / x * x = 1.

(*
証明の内容は、以下に忠実なものである。

[Coq][Math] From left unit and left inverse to right unit and inverse.

http://study-func-prog.blogspot.jp/2014/04/coqmath-from-left-unit-and-left-inverse.html
*)

Lemma inv_r : forall x, x * / x = 1.
Proof.
  move=> x.
  rewrite -{1}(one_unit_l x).
  rewrite -{1}(inv_l (inv x)).
  rewrite -[/ / x * / x * x]mult_assoc.
  rewrite (inv_l).
  rewrite -mult_assoc.
  rewrite one_unit_l.
  rewrite inv_l.
  by [].
Qed.

Lemma one_unit_r : forall x, x * 1 = x.
Proof.
  move=> x.
  rewrite -{1}(one_unit_l x).
  rewrite -{1}(inv_l (inv x)).
  rewrite -{1}(inv_l x).
  rewrite mult_assoc.
  rewrite -[/ / x * / x * x]mult_assoc.
  rewrite (inv_l).
  rewrite -mult_assoc.
  rewrite -mult_assoc.
  rewrite one_unit_l.
  rewrite mult_assoc.
  rewrite (inv_l (/ x)).
  by [].
Qed.

(* END *)
