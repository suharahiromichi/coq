(**
An introduction to small scale reflection in Coq

6.1.4 Example: a depth rst search algorithm

http://hal.inria.fr/docs/00/55/53/79/PDF/main-rr.pdf
*)

Require Import ssreflect ssrfun ssrbool eqtype ssrnat div seq.
Require Import path choice fintype tuple finfun finset.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Variables (T : finType) (e : T -> seq T).

Definition grel := [rel x y | y \in e x].
Check grel : rel T.                         (* simpl_rel T := rel T *)
Check [rel x y : T | y \in e x] : rel T.
Check [rel x y : nat | y \in [:: x]] : rel nat.
Check (fun x y : nat => y \in [:: x]) : rel nat.

(* 参考 *)
Check [pred n : nat | n == 0] : pred nat.
Check (fun n : nat => n == 0) : pred nat.

Fixpoint dfs (n : nat) (a : seq T) (x : T) {struct n} :=
  if n is n'.+1 then
    if x \in a then a else foldl (dfs n') (x :: a) (e x)
  else a.

Inductive dfs_path x y (a : seq T) : Prop :=
  DfsPath p of (path grel x p) & (y = last x p) & [disjoint (x :: p) & a].

(* 古い書き方 *)
Inductive dfs_path' x y (a : seq T) : Prop :=
  DfsPath' p : (path grel x p) -> (y = last x p) -> [disjoint (x :: p) & a] -> dfs_path' x y (a : seq T).

(**
dfs_path の意味：
- ふたつの連続した要素からなるseq 「x :: p」 は、grel関係である。それらはグラフ上で隣接adjacentしている。
- y は p の最後の要素である。
- seq 「x :: p」は、seq a の要素ではない。disjoint
*)

Lemma dfsP : forall n x y (a : seq T),
               #|T| <= #|a| + n ->
                            y \notin a ->
                            reflect (dfs_path x y a) (y \in dfs n a x).
Proof.
  elim=> [|n IHn] x y a Hn Hy /=.           (* elim by n *)
  admit.
  admit.
Qed.

Lemma max_card : forall (T : finType) (A : pred T), #|A| <= #|T|.
Proof.
  admit.
Qed.

(* last は、pの最後の要素、[::]ならx。 *)
Lemma dfs_pathP : forall x y,
                    reflect
                      (exists2 p, (path grel x p) & (y = last x p))
                      (y \in dfs #|T| [::] x).
Proof.
  admit.
Qed.

(* END *)
