(**
Coqで継続モナド

2014_05_15 @suharahiromichi
*)

Require Import ssreflect ssrbool ssrnat seq.

(**
# 継続モナド
## 定義
*)
Definition MCont R A := (A -> R) -> R.

Definition ret {R A : Type} (a : A) : MCont R A :=
  fun k => k a.

Definition bind {R A : Type} (c : MCont R A)
           (f : A -> MCont R A) : MCont R A :=
  fun (k : A -> R) => c (fun (a : A) => f a k).

Infix ">>=" := bind (left associativity, at level 42). (* 文献1. *)

Notation "'DO' a <- A ; b <- B ; C 'OD'" :=
  (A >>= fun a => B >>= fun b => C)
    (at level 100, right associativity).

(**
## モナド則の証明
*)

Lemma monad_1 : forall (R A : Type) (a : A) (f : A -> MCont R A),
                  ret a >>= f = f a.
Proof.
  by [].
Qed.

Lemma monad_2 : forall (R A : Type) (m : MCont R A),
                  m >>= ret = m.
Proof.
  by [].
Qed.

Lemma monad_3 : forall (R A : Type) (f g : A -> MCont R A) (m : MCont R A),
                  (m >>= f) >>= g = m >>= fun x => f x >>= g.
(* 右結合なので、実際は、この括弧は不要である。 *)
Proof.
  by [].
Qed.

(**
# 階乗の計算
*)
Section factorial.
(**
## 定義
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
## 証明
*)
Lemma fact_cps_Sn :
  forall n f,
    fact_cps n.+1 f =
    fact_cps n (fun (m : nat) => f (m * n.+1)).
Proof.
    by [].
Qed.

Lemma eq_f_fact_fact_cps_f :
  forall (n : nat),
    (forall f, f (fact n) = fact_cps n f).
Proof.
  move=> n f.
  elim: n f.
    by [].
  move=> n IHn f.
  by rewrite fact_cps_Sn; rewrite <-IHn, mulnC.
Qed.

Theorem eq_fact_fact_cps :
  forall (n : nat), fact n = fact_cps n id.
Proof.
  move=> n.
  apply (eq_f_fact_fact_cps_f n id).
Qed.

End factorial.

(**
# フィボナッチ数の計算
*)
Section fibonacci.
(**
## 定義
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
## 証明

文献3.を参考にしました。
*)

(**
補題: fib_cpsの定義の三番目の節を取り出したもので、
   fib_cpsの計算を一段進めるのに使う。
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
    (forall g, g (fib (S n)) = fib_cps (S n) g).
Proof.
  elim.
  (* n = 0 のとき *)
    by [].

  (* n = n'+1 のとき *)
  case=> n.
    by [].
  case=> Hf Hg.
  split; move=> f; rewrite fib_cps_SSn.
    by rewrite Hg.
  by rewrite <-Hg, <-Hf.
Qed.

Lemma eq_f_fib_fib_cps_f : forall n f, f (fib n) = fib_cps n f.
Proof.
  move=> n f.
  apply (eq_fib_fib_cps_aux n).
Qed.

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

2. お気楽 Haskell プログラミング入門
   http://www.geocities.jp/m_hiroi/func/haskell38.html

3. CPS変換されたフィボナッチ関数の証明をしてみた」
   http://d.hatena.ne.jp/yoshihiro503/20100830#p2

*)

(* END *)
