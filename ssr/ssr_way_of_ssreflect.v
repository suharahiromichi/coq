(**
SSReflect の方法
*)

(**
# Import
*)
Require Import ssreflect ssrbool.
Require Import ssrfun eqtype ssrnat seq.
Require Import ssralg ssrnum ssrint finset fintype.

(**
# Set
*)
(**
Coq RM Sec. 2.7 の「暗黙の引数」の使い方に従うために、以下の設定をする。
 *)
Set Implicit Arguments .
Unset Strict Implicit .
Unset Printing Implicit Defensive .

(**
# Set Printing
*)
(**
以下は省略時解釈値である。必要に応じてSet/Unsetする。
 *)
Unset Printing Implicit.                    (* implicitな引数を表示しない。 *)
Unset Printing Coercions.                   (* コアーションのための関数を表示しない。 *)
Set Printing Notations.                     (* Notation を展開しない。 *)
(**
``Set Printing All.`` は、上記の省略解釈値を逆にする。
*)

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

(* END *)



















Definition funA' :=  (fun n : nat => (fun m : nat => n = m)).
Definition funB' := [fun n : nat => [fun m : nat => n = m]].

