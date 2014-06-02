Require Import ssreflect.

(**
# 第8回

http://qnighy.github.io/coqex2014/ex6.html

## 課題39 (種別:B / 締め切り : 2014/06/08)

モナドを定義する。以下の空欄を埋めよ。
*)

(* bindの記法を予約 *)
Reserved Notation "x >>= y" (at level 110, left associativity).

(* モナド *)
Class Monad (M : Type -> Type) :=
  {
    bind {A B} : M A -> (A -> M B) -> M B
      where "x >>= f" := (bind x f);
    ret {A} : A -> M A;
    (* モナド則をここに書く *)
    monad_1 : forall A B (f : A -> M B) (x : A),
                (ret x >>= f) = (f x);
    monad_2 : forall A (m : M A),
                (m >>= ret) = m;
    monad_3 : forall A B C (f : A -> M B) (g : B -> M C) (m : M A),
                (m >>= f >>= g) = (m >>= (fun x => f x >>= g))
}.

Notation "x >>= f" := (@bind _ _ _ _ x f).

Require Import List.

(* 補足説明：
Program Instanceの中で直接定義するよりも、外で定義したほうが、楽だろう。
 *)
Fixpoint bind_list {A B : Type} (m : list A) (f : A -> list B) : list B :=
  match m with
    | nil => nil
    | x :: xs => (f x) ++ (bind_list xs f)
  end.

(* 補足説明：
分配則も証明しておく。
 *)
Lemma bind_list_distr : 
  forall {A B : Type} (m n : list A) (f : A -> list B),
    bind_list (m ++ n) f = bind_list m f ++ bind_list n f.
Proof.
  move=> A B m n f.
  elim: m.
    by [].
  move=> a m.
  elim: n.
    move=> IHn.
    by rewrite /= 2!app_nil_r.
  move=> b n IHm /= ->.
  by apply: app_assoc.
Qed.

Program Instance ListMonad : Monad list :=
  {|
    bind A B m f :=                         (* ここを埋める *)
      bind_list m f;
    ret A x :=                              (* ここを埋める *)
      x :: nil
  |}.
Next Obligation.                            (* 補足説明：モナド則 1 *)
  (* ここに証明を書く *)
  apply: app_nil_r.
Qed.
(* 以下、ListMonadが定義できるまでNext Obligation -> Qed を繰り返す *)
Next Obligation                             (* 補足説明：モナド則 2 *).
  elim: m.
    by [].
  by rewrite /bind_list; move=> a l ->.
Qed.
Next Obligation.                            (* 補足説明：モナド則 3 *)
  elim m.
    by [].
  move=> a l /= <-.
  apply: bind_list_distr.
Qed.

(* モナドの使用例 *)

Definition foo : list nat := 1 :: 2 :: 3 :: nil.

(* 内包記法もどき *)
(*
補足説明：
SSReflectのタクティカルと重ならないように「DO」とし、
結合方向に悩まなくてすむようにDO...OD形式とした。
 *)
Notation "s1 >> s2" :=
  (s1 >>= fun _ => s2)
    (at level 110, left associativity).
Notation "'DO' a <- A ; b <- B ; C 'OD'" :=
  (A >>= fun a => B >>= fun b => C)
    (at level 120, no associativity).
Notation "'DO' A ; B ; C 'OD'" :=
  (A >> B >> C)
    (at level 120, no associativity).

Definition baz := Eval lazy in
   DO
     x <- foo;
     y <- foo;
     ret (x, y)
   OD.
Print baz.

Definition bar := Eval lazy in
  foo >>= (fun x =>
  foo >>= (fun y =>
  ret (x, y))).
Print bar.

(* 
補足説明：
bindの定義をInstanceの中で与える場合は以下である。
モナド則 3 の証明が大変になるのではないか。

Program Instance ListMonad' : Monad list :=
  {|
    bind A B m f :=                         (* ここを埋める *)
      (fix bind' (m : list A) : list B :=
         match m with
          | nil => nil
          | x :: xs => (f x) ++ (bind' xs)
        end) m;
    ret A x :=                              (* ここを埋める *)
      x :: nil
  |}.
 *)

(* END *)
