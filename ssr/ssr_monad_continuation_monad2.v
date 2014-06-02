(**
Coqで継続モナド
=========================

2014_05_15 @suharahiromichi

2014_06_01 @suharahiromichi Classを使用して定義しなおした。

モナドと継続の話を一度で片付けてしまおうと思う。
継続モナドについて解説したページは多いけれど、
大部分がHaskellであるから、Coq SSReflect で書いてみた。
もっとも、本資料の内容もHaskellについて解説した
文献2.を多く参考にさせていただいた。

また、フィボナッチ関数の証明は文献3.
のCoqによる証明をSSReflectに修正したものである。

Coqのモナドのパッケージは文献1.にあるが、
これは使用していない。ただし「>>=」演算子の優先順位はあわせた。

本資料のソースコードは以下にあります。

https://github.com/suharahiromichi/coq/blob/master/ssr/ssr_monad_continuation_monad2.v
*)

Require Import ssreflect ssrbool ssrnat seq.

Reserved Notation "c >>= f"
         (at level 42, left associativity).      (* 文献1. *)

Class Monad (M : Type -> Type -> Type) :=
  {
    bind {R A} : M R A -> (A -> M R A) -> M R A
      where "x >>= f" := (bind x f);
    ret {R A} : A -> M R A;
    monad_1 : forall (R A : Type) (a : A) (f : A -> M R A),
                ret a >>= f = f a;
    monad_2 : forall (R A : Type) (m : M R A),
                m >>= ret = m;
    monad_3 : forall (R A : Type) (f g : A -> M R A) (m : M R A),
                (m >>= f) >>= g = m >>= fun x => f x >>= g
(* 左結合なので、実際は、この括弧は不要である。 *)
  }.

(**
# 継続モナド

## 定義

A->Rの型の関数が「継続」である。その「継続」を受け取るのが継続モナド
であり、(A->R)->Rの型をもつ。
モナドであることを強調するために、大文字のMContとラベルする。
*)
Definition MCont R A := (A -> R) -> R.

Program Instance : Monad MCont :=
  {|
    bind R A c f :=
      fun (k : A -> R) => c (fun (a : A) => f a k);
    ret R A a :=
      fun k => k a
  |}.
(**
モナド則の証明は、自動で終わってしまった。
以上 Classを使った定義は、文献4.を参考にした。
ただし、演算子の優先順位と結合方向は改めた。
 *)

(* call/cc *)
Definition callcc {R A B : Type}
           (f : (A -> MCont R B) -> MCont R A) : MCont R A :=
  fun (k : A -> R) => f (fun (a : A) => fun _ => k a) k.

(**
演算子と、do記法も定義しておく。
*)
Notation "x >>= f" :=
  (@bind _ _ _ _ x f).

Notation "s1 >> s2" :=
  (s1 >>= fun _ => s2)
    (at level 42, left associativity).

Notation "'DO' a <- A ; b <- B ; C 'OD'" :=
  (A >>= fun a => B >>= fun b => C)
    (at level 100, no associativity).

Notation "'DO' A ; B ; C 'OD'" :=
  (A >> B >> C)
    (at level 100, no associativity).

(**
# 階乗の計算
*)
Section factorial.
(**
## 定義

階乗を再帰で計算する関数と、CPSで計算する関数を定義する。
*)
Fixpoint fact (n : nat) : nat :=
  match n with
    | 0     => 1
    | n'.+1 => n * fact n'
  end.

Fixpoint fact_cps (n : nat) : MCont nat nat :=
  match n with
    | 0     => ret 1
    | n'.+1 => fact_cps n' >>= fun (m : nat) => ret (m * n)
  end.

(**
## 実行例
*)
Eval cbv in fact_cps 0 id.                  (* 1 *)
Eval cbv in fact_cps 2 id.                  (* 2 *)
Eval cbv in fact_cps 3 id.                  (* 6 *)
Eval cbv in fact_cps 4 id.                  (* 24 *)

(**
## 証明

任意の自然数に対して、両者が同じ結果になることを証明する。

補題として、fact_cpsの計算の一段階分の証明しておく。
*)
Lemma fact_cps_Sn :
  forall n f,
    fact_cps n.+1 f =
    fact_cps n (fun (m : nat) => f (m * n.+1)).
Proof.
    by [].
Qed.

(**
任意の継続fについて証明する。
*)
Lemma eq_f_fact_fact_cps_f :
  forall (n : nat),
    (forall f, f (fact n) = fact_cps n f).
Proof.
  elim.
    by [].
  move=> n IHn f.
  by rewrite fact_cps_Sn -IHn mulnC.
Qed.

(**
証明したい定理
*)
Theorem eq_fact_fact_cps :
  forall (n : nat), fact n = fact_cps n id.
Proof.
  move=> n.
  apply (eq_f_fact_fact_cps_f n id).
Qed.

End factorial.

(**
# フィボナッチ関数
*)
Section fibonacci.
(**
## 定義

フィボナッチ数を再帰で計算する関数と、CPSで計算する関数を定義する。
後者の中でdo記法を使ってみた。
*)
Fixpoint fib (n : nat) : nat :=
  match n with
    | 0 => 1
    | 1 => 1
    | (m.+1 as sm).+1 => fib sm + fib m
  end.

Fixpoint fib_cps (n : nat) : MCont nat nat :=
  match n with
    | 0 => ret 1
    | 1 => ret 1
    | (m.+1 as sm).+1 =>
      DO
        a <- fib_cps sm;
        b <- fib_cps m;
        ret (a + b)
      OD
  end.

(**
## 実行例
*)
Eval cbv in fib_cps 0 id.                  (* 1 *)
Eval cbv in fib_cps 1 id.                  (* 1 *)
Eval cbv in fib_cps 2 id.                  (* 2 *)
Eval cbv in fib_cps 3 id.                  (* 3 *)
Eval cbv in fib_cps 4 id.                  (* 5 *)
Eval cbv in fib_cps 6 id.                  (* 13 *)

(**
## 証明

任意の自然数に対して、両者が同じ結果になることを証明する。
この証明は文献3.を参考にした。
*)

(**
補題: fib_cpsの定義の三番目の節を取り出したもので、fib_cpsの
計算を一段進めるのに使う。
 *)
Lemma fib_cps_SSn : forall n f,
  fib_cps n.+2 f =
  fib_cps n.+1 (fun r1 => fib_cps n (fun r2 => f (r1 + r2))).
Proof.
  by [].
Qed.

(**
より強い定理
 *)
Lemma eq_fib_fib_cps_aux :
  forall n,
    (forall f, f (fib n) = fib_cps n f) /\
    (forall g, g (fib n.+1) = fib_cps n.+1 g).
Proof.
  elim.
  (* fib 0 = fib_cps 0 /\ fib 1 = fib_cps 1 を証明する。 *)
    by [].

  (* fib n = fib_cps n /\ fib n+1 = fib_cps n+1 ならば、
     fib n+1 = fib_cps n+1 /\ fib n+2 = fib_cps n+2 を証明する。 *)
  case=> n.

  (* fib 0 = fib_cps 0 /\ fib 1 = fib_cps 1 ならば、
     fib 1 = fib_cps 1 /\ fib 2 = fib_cps 2 を証明する。 *)
    by [].

  (* fib n+1 = fib_cps n+1 /\ fib n+2 = fib_cps n+2 ならば、
     fib n+2 = fib_cps n+2 /\ fib n+3 = fib_cps n+3 を証明する。 *)
  case=> Hf Hg.
  split; move=> f; rewrite fib_cps_SSn.
  (* ゴールの/\の左を証明する。 *)
    by rewrite Hg.
  (* ゴールの/\の右を証明する。 *)
  by rewrite -Hg -Hf.
Qed.

(**
任意の継続fについて証明する。
*)
Lemma eq_f_fib_fib_cps_f : forall n f, f (fib n) = fib_cps n f.
Proof.
  move=> n f.
  apply (eq_fib_fib_cps_aux n).
Qed.

(**
証明したい定理
*)
Theorem eq_fib_fib_cps : forall n, fib n = fib_cps n id.
Proof.
  move=> n.
  apply (eq_f_fib_fib_cps_f n id).
Qed.

End fibonacci.

(**
# 文献

1. Library lc.Monad
   http://coq.inria.fr/pylons/contribs/files/lc/trunk/lc.Monad.html

2. お気楽 Haskell プログラミング入門 ●継続渡しスタイル
   http://www.geocities.jp/m_hiroi/func/haskell38.html

3. CPS変換されたフィボナッチ関数の証明をしてみた
   http://d.hatena.ne.jp/yoshihiro503/20100830#p2

4. Coq演習2014 第8回 課題39
   http://qnighy.github.io/coqex2014/ex6.html
*)

(* END *)
