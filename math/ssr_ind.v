(**
完全帰納法 complete induction について

強化帰納法 strengthening induction, strong induction、
あるいは、累積帰納法ともいう。
*)

From mathcomp Require Import all_ssreflect.
Require Import ssromega.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(**
# 完全帰納法 complete induction

Coq/SSReflectでたった1行のコマンドで完全帰納法を適用する方法

https://qiita.com/nekonibox/items/514da8edfc6107b57254

MathComp のイデオム 「elim: m {-2}m (leqnn m)」 の説明です。
 *)

(* -2 を繰り返すことで、2で割る関数。 *)
Fixpoint div2 (n : nat) : nat :=
match n with
| 0 => 0
| 1 => 0
| n'.+2 => (div2 n').+1
end.

Compute div2 10.                            (* = 5 *)

(**
## うまくいかない例
 *)
Goal forall m, div2 m <= m.
Proof.
  elim.
    by [].
  move=> n.
  (* div2 n <= n -> div2 n.+1 <= n.+1 *)
  simpl.
Abort.

(**
## Standard Coq の帰納法の原理を使う
 *)
Check Wf_nat.lt_wf_ind
  : forall (n : nat) (P : nat -> Prop),
    (forall n0 : nat, (forall m : nat, (m < n0)%coq_nat -> P m) -> P n0) -> P n.
      
Goal forall m, div2 m <= m.
Proof.
  move=> m.
  pattern m.
  apply Wf_nat.lt_wf_ind => {m}.
  (* forall n : nat,
     (forall m : nat, (m < n)%coq_nat -> div2 m <= m)
     -> div2 n <= n *)
  case; first by [].
  case; first by [].
  move=> n IH /=.
  apply: ltnW.
  apply: IH.
    (* (n < n.+2)%coq_nat *)
  by apply/ltP.
Qed.

(**
## MathComp のイデオムを使う
 *)
Lemma ltS n m : (n.+1 < m.+1) = (n < m).
Proof. apply/idP/idP => H; by ssromega. Qed.

Goal forall m, div2 m <= m.
Proof.
  move=> m.
  elim: m {-2}m (leqnn m).                  (* ！！ここ！！ *)
  - (* forall m : nat, m <= 0 -> div2 m <= m *)
    move=> m.
      by rewrite leqn0 => /eqP ->.
  - (* forall n : nat,
       (forall m : nat, m <= n -> div2 m <= m)
       -> forall m : nat, m <= n.+1
       -> div2 m <= m *)
    move=> n IHm m'.
    move: m' n IHm.               (* ラムダ変数の順番を入れ替える。 *)
    case; first by [].
    case; first by [].
    move=> n m IHm Hm'.
    apply: ltnW.
    apply: (IHm n).
    rewrite ltS in Hm'.
      by apply: ltnW.
Qed.

(**
## 完全帰納法の原理を証明してから
*)

Lemma complete_ind (P:nat -> Prop) :
  (forall n, (forall m, m < n -> P m) -> P n) ->
  forall n, P n.
Proof.
  move => H n.
    by elim : n {-2}n (leqnn n) =>[[_|//]|n IHn m Hm];
       apply : H => l Hl //; exact : IHn (leq_trans Hl Hm).
Qed.

Goal forall m, div2 m <= m.
Proof.
  move=> m.
  elim/complete_ind : m.
  (* forall n : nat,
     (forall m : nat, m < n -> div2 m <= m)
     -> div2 n <= n *)
  case; first by [].
  case; first by [].
  move=> n IH /=.
  apply: ltnW.
  apply: IH.
    by apply: ltnW.
Qed.

(**
# Custum Induction

完全帰納法 を使うわけではない。
*)

(**
## Funcutonal Scheme

http://www.a-k-r.org/d/2019-04.html#a2019_04_25_1
 *)

Require Import FunInd.
Functional Scheme div2_ind := Induction for div2 Sort Prop.
(*
div2_equation is defined
div2_ind is defined
 *)
Check div2_ind
  : forall P : nat -> nat -> Prop,
    (forall n : nat, n = 0 -> P 0 0) ->
    (forall n n0 : nat, n = n0.+1 -> n0 = 0 -> P 1 0) ->
    (forall n n0 : nat,
        n = n0.+1 ->
        forall n' : nat, n0 = n'.+1 -> P n' (div2 n') -> P n'.+2 (div2 n').+1) ->
    forall n : nat, P n (div2 n).

Goal forall m, div2 m <= m.
Proof.
  move=> m.
  functional induction (div2 m).
    by [].
      by [].
        by apply ltnW.
Qed.

(**
## Funcutonal Scheme の発展形が Function である。

http://www.a-k-r.org/d/2019-05.html#a2019_05_03_1

https://people.irisa.fr/David.Pichardie/papers/flops06.pdf
*)

Function div2'' (n : nat) : nat :=
match n with
| 0 => 0
| 1 => 0
| n'.+2 => (div2'' n').+1
end.
Check div2''_ind
  : forall P : nat -> nat -> Prop,
    (forall n : nat, n = 0 -> P 0 0) ->
    (forall n : nat, n = 1 -> P 1 0) ->
       (forall n n' : nat, n = n'.+2 -> P n' (div2'' n') -> P n'.+2 (div2'' n').+1) ->
       forall n : nat, P n (div2'' n).
                         
Lemma leq_div2'' m : div2'' m <= m.
Proof.
  functional induction (div2'' m).
    by [].
      by [].
        by apply ltnW.
Qed.

(**
# Mathcomp イデオムの例
*)

(**
## Mathcomp 身近なライブラリの例
 *)
Print edivn.                             (* Euclideanで定義した剰余 *)
Print modn.                              (* 引算で定義した剰余 *)

Lemma modn_def m d : (modn m d) = (edivn m d).2.
Proof.
  case: d => //= d; rewrite /modn /edivn /=.
  elim: m {-2}m 0 (leqnn m) => [|n IHn] [|m] q //=.
  rewrite ltnS !subn_if_gt; case: (d <= m) => // le_mn.
    by apply: IHn; apply: leq_trans le_mn; exact: leq_subr.
Qed.

(**
## MCBの例

3.2.4 Application: strengthening induction
*)

Lemma stamps n : 12 <= n -> exists s4 s5, s4 * 4 + s5 * 5 = n.
Proof.
  elim: n {-2}n (leqnn n) =>[|n IHn]; first by case.
  do 12! [ case; first by [] ].            (* < 12c *)
  case; first by exists 3, 0.              (* 12c = 3 * 4c *)
  case; first by exists 2, 1.              (* 13c = 2 * 4c + 1 * 5c *)
  case; first by exists 1, 2.              (* 14c = 1 * 4c + 2 * 5c *)
  case; first by exists 0, 3.              (* 15c = 3 * 5c *)
  move=> m'; set m := _.+1; move=> mn m11.
  case: (IHn (m-4) _ isT) => [|s4 [s5 def_m4]].
    by rewrite leq_subLR (leq_trans mn) // addSnnS leq_addl.
      by exists s4.+1, s5; rewrite mulSn -addnA def_m4 subnKC.
Qed.

(* END *)
