Require Import ssreflect ssrnat.

(**
# 第7回 ソースファイルの分割とコンパイル/SectionとModule (2014/05/18)

http://qnighy.github.io/coqex2014/ex7.html

## 課題33 (種別:B / 締め切り : 2014/06/01)

2で定義したlist boolのモジュールと、3で定義した冪乗のモジュールを合成して、新たなモジュールを
作成せよ。

ヒント

モジュールへの機能の追加の練習です。標準ライブラリのCoq.Structuresの記述を参考にするとよいでしょう。
*)

(**
### 1.

課題32の半群モジュール型を参考にして、モノイドを表すモジュール型 Monoid を定義せよ。
 *)
Require Import Arith List.

Module Type Monoid.
  Parameter G : Type.
  Parameter Id : G.                         (* 単位元 *)
  Parameter mult : G -> G -> G.
  Axiom mult_assoc :                        (* 結合則 *)
    forall x y z : G, mult x (mult y z) = mult (mult x y) z.
  Axiom left_id :                           (* 左単位元 *)
    forall x : G, mult Id x = x.
  Axiom right_id :                          (* 右単位元 *)
    forall x : G, mult x Id = x.
End Monoid.

(**
### 2.

list boolに自然なモノイドの構造を入れ、Monoid型をもつモジュールとして定義せよ。
*)

Check list bool.
Check @nil bool.
Check @app bool.

Module BoolList_Monoid <: Monoid.
  Definition G := list bool.
  Definition Id := @nil bool.               (* [] *)
  Definition mult := @app bool.             (* append. *)
  Theorem mult_assoc :
    forall x y z : G, mult x (mult y z) = mult (mult x y) z.
  Proof.
    by apply: app_assoc.
  Qed.
  Theorem left_id : forall x : G, mult Id x = x.
  Proof.
    by [].
  Qed.
  Theorem right_id : forall x : G, mult x Id = x.
  Proof.
    elim.
      by [].
    by move=> a l /= ->.
  Qed.
End BoolList_Monoid.

(*
### 3.

モノイドの元の冪乗(指数は自然数)を定義し、指数法則を証明せよ。これを定義する際、定義済みの
Monoidモジュールを直接変更するのではなく、MonoidモジュールMを引数にとる新たなモジュールを定
義すること。
*)

Module Type Exponent (M : Monoid).
  Parameter exp : M.G -> nat -> M.G.
  Axiom exp_law_add : forall (x : M.G) (n m : nat),
    M.mult (exp x n) (exp x m) = exp x (n + m).
  Axiom exp_law_mul : forall (x : M.G) (n m : nat),
    exp (exp x n) m = exp x (n * m).
End Exponent.

Fixpoint app_exp (x : list bool) (n : nat) :=
  match n with
    | 0 => nil
    | n'.+1 => app x (app_exp x n')
  end.
Eval compute in app_exp (true :: nil) 0.    (* [] *)
Eval compute in app_exp (true :: false :: nil) 6.
Eval compute in app_exp (app_exp (true :: false :: nil) 2) 3.
Eval compute in app_exp (app_exp (true :: false :: nil) 3) 2.

Lemma app_add_exp_law :
  forall (x : list bool) (n m : nat),
    (app_exp x n) ++ (app_exp x m) = app_exp x (n + m).
Proof.
  move=> x n m.
  elim n.
    by rewrite /= add0n.
  move=> n' IHn /=.
  rewrite -app_assoc.
  by rewrite IHn.
Qed.

Lemma app_exp_null :
  forall (n : nat), app_exp nil n = nil.
Proof.
  elim.
    by [].
  move=> n IHn.
  by rewrite /= IHn.
Qed.

Lemma app_mul_exp_law :
  forall (x : list bool) (n m : nat),
    app_exp (app_exp x n) m = app_exp x (n * m).
Proof.
  move=> x n m.
  elim: n.
    by rewrite /= app_exp_null.

  elim: m.
    move=> n.
    by rewrite /= !muln0 /=.
  move=> m IHm n.
  admit.                                    (* XXXX *)
Qed.  

Module Exponent_exp <: Exponent BoolList_Monoid.
  Definition exp := app_exp.
  Theorem exp_law_add : forall (x : BoolList_Monoid.G) (n m : nat),
    BoolList_Monoid.mult (exp x n) (exp x m) = exp x (n + m).
  Proof.
    apply: app_add_exp_law.
  Qed.
  Theorem exp_law_mul : forall (x : BoolList_Monoid.G) (n m : nat),
    exp (exp x n) m = exp x (n * m).
  Proof.
    apply: app_mul_exp_law.
  Qed.
End Exponent_exp.

(* END *)
