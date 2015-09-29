(**
SSReflect の方法
*)

(**
# Import
*)
Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq.
Require Import choice fintype.

(**
# Set
*)
(**
Coq RM Sec. 2.7 の「暗黙の引数」の使い方に従うために、以下の設定をする。
 *)
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(**
# Set Printing
*)
(**
以下は省略時解釈値である。必要に応じてSet/Unsetする。
``Set Printing All.`` を使用してもよい。
 *)
(* 左記の意味、D:省略時、A:All 設定時 *)
Unset Printing Implicit.           (* implicitな引数を表示しない。 Dしない。 A:する。*)
Unset Printing Coercions.          (* コアーションを表示しない     D:しない。 A:する。*)
Set Printing Notations.            (* Notation を使って表示する。  D:する。  A:しない。*) 
Unset Printing Universe.           (* 高階のTypeを表示する。       D:しない。 A:-*)

(**
# auto-simplifying predicates
*)
(**
simpl と unfold に対する動作が異なる。
 *)

(**
## 簡単な例
 *)

(**
通常の関数
 *)
Definition funA : nat -> nat        := (fun n : nat => n.+1).

Goal funA 1 = 2.
Proof.
  (* Goal : funA 1 = 2 *)
  move=> /=.                                (* simpl *)
  (* Goal : funA 1 = 2、変化しない。 *)
  rewrite /funA.                            (* unfold funA *)
  (* Goal : 2 = 2 *)
  Undo 1.

  (* Goal : funA 1 = 2 *)
  rewrite /funA.                            (* unfold funA *)
  (* Goal : 2 = 2 *)
  reflexivity.
Qed.

(**
simpl_fun
 *)
Definition funB : simpl_fun nat nat := [fun n : nat => n.+1].

Goal funB 1 = 2.
Proof.
  (* Goal : funB 1 = 2 *)
  move=> /=.                                (* simpl *)
  (* Goal : 2 = 2 *)
  Undo 1.
  
  (* Goal : funB 1 = 2 *)
  rewrite /funA.                            (* unfold funA *)
  (* Goal : [fun n => n.+1] 1 = 2 *)
  move=> /=.                                (* simpl *)
  (* Goal : 2 = 2 *)
  reflexivity.
Qed.

(**
## もう少し複雑な例
 *)

(**
通常の関数
 *)
Definition f := fun (n : nat) =>
                  (fix f' (n : nat) := if n is n'.+1 then (f' n').+2 else 0) n.

Lemma foo : forall n, f (2 * n) = f n + f n.
Proof.
  elim => [|n ihn].
  - by rewrite muln0 //.
  - rewrite !addnS !addSn -/f.
    rewrite mulnS.
    rewrite -ihn.
    rewrite /=.
    (* Goal: (f (2 * n)).+4 = (f (2 * n)).+4 *)
      by [].
Qed.

(**
simpl_fun
 *)
Definition g := [fun n : nat =>
                   (fix g' (n : nat) := if n is n'.+1 then (g' n').+2 else 0) n].

Lemma goo : forall n, g (2 * n) = g n + g n.
Proof.
  elim => [|n ihn].
  - by rewrite muln0 //.
  - rewrite !addnS !addSn -/g.
    rewrite mulnS.
    rewrite -ihn.
    rewrite /=.
    (* Goal:
 ((fix g' (n0 : nat) : nat := ...) (2 * n)).+4 =
 ((fix g' (n0 : nat) : nat := ...) (2 * n)).+4    *)
      by [].
Qed.

(**
# simpl_fun, simpl_pred, simpl_red
*)
(**
## simpl_fun

型コンストラクタ simpl_fun
値コンストラクタ SimpFun
デストラクタ   fun_of_simpl
*)

(**
## simpl_pred
*)

(**
## simpl_red
*)

(*
# mem_pred
*)
(**
## simpl_fun

型コンストラクタ mem_pred
値コンストラクタ Mem
デストラクタ   pred_of_mem
*)

(**
# xpred1 と pred1 とその仲間たち。
*)

(**
## pred は別

よく使う。
*)
Compute pred.                               (* fun T : Type => T -> bool *)
Compute pred nat.                           (* nat -> bool *)
Fail Check pred nat : nat -> bool.          (* 型コンストラクタではない！ *)

(*
## xpred1 は通常のpred型
*)
Check xpred1 : _ -> _ -> bool.              (* Notation なので *)
Check xpred1 1 : pred nat.                  (* ここに注目 *)
Compute xpred1 1 1.                         (* true *)

(*
## pred1 はsimpl_pred型、引数はeqTypeのインスタンスの型
*)
Check @pred1 : forall T : eqType, T -> simpl_pred T.
Check @pred1 nat_eqType : nat_eqType -> simpl_pred nat_eqType.
Check @pred1 nat_eqType 1 : simpl_pred nat_eqType. (* ここに注目 *)
Compute @pred1 nat_eqType 1 1.              (* true *)
Compute pred1 1 1.                          (* true *)



(*
## xpred0 は通常のpred型
*)
Check xpred0 : forall (T : Type), bool.
Check xpred0 1 : bool.
Compute xpred0 1.                           (* false *)


(*
## pred0 はsimpl_pred型
*)
Check @pred0 : forall (T : Type), simpl_pred T.
Check @pred0 nat_eqType 1 : bool.
Compute @pred0 nat_eqType 1.                (* false *)
Compute pred0 1.                            (* false *)

(**
# 関数適用
*)

Check minus : nat -> nat -> nat.
Check minus ^~ 1 : nat -> nat.
Compute minus^~1 10.                        (* 9 *)

Check S : nat -> nat.
Check @^~ 1 : (nat -> nat) -> nat.
Compute @^~1 S.                             (* 2 *)

(** あまり使わない *)
Check S \o Peano.pred.
Compute (S \o Peano.pred) 0.                (* 1 *)
Compute S (Peano.pred 0).                   (* 1 *)

Check S \; Peano.pred.
Compute (S \; Peano.pred) 0.                (* 0 *)
Compute Peano.pred (S 0).                   (* 0 *)


(**
# ``[eta f]`` について。
*)
Locate "[ eta _ ]".                         (* fun x => f x *)

(**
# predArgType と {: T}
*)

(**
# lock と nosimpl

"A Small Scale Reflection Extension for the Coq system" p.53
*)

Definition addn' n m := locked (plus n m).

Goal forall n m, addn' n m = plus n m.
Proof.
  rewrite /=.                               (* 左辺はsimplされない。 *)
  (* addn' n m = n + m *)
  unlock addn'.                             (* unfold と同じ効果がおきる。 *)
  (* n + m = n + m *)
  done.
Qed.


(**
nosimpl な関数の例：

ssrbool.v:Definition in_mem T x mp := nosimpl pred_of_mem T mp x.
ssrnat.v:Definition addn := nosimpl addn_rec.
ssrnat.v:Definition subn := nosimpl subn_rec.
ssrnat.v:Definition muln := nosimpl muln_rec.
ssrnat.v:Definition expn := nosimpl expn_rec.
ssrnat.v:Definition factorial := nosimpl fact_rec.
ssrnat.v:Definition double := nosimpl double_rec.
seq.v:Definition rev T (s : seq T) := nosimpl (catrev s [::]).
div.v:Definition gcdn := nosimpl gcdn_rec.
*)

Definition addn'' n m := nosimpl (plus n m).
Definition addn''' := nosimpl plus.         (* 同じ。 *)

Goal forall n m : nat, addn'' n.+1 m = plus n.+1 m.
Proof.
  rewrite /=.                               (* 左辺はsimplされない。 *)
  (* addn'' n.+1 m = (n + m).+1 *)
  rewrite /addn'' /=.                       (* 明示的にunfoldすると。 *)
  (* (n + m).+1 = (n + m).+1 *)
  done.
Qed.

(* END *)
