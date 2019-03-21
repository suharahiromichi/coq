(* ラムダ式をコンビネータに変換するα消去のプログラム *)
(* 
   TODO:
   α消去で与える変数を自動化する。
 *)

From mathcomp Require Import all_ssreflect.
Require Import Ascii.
Require Import String.
Require Import ssr_string.
Open Scope string_scope.

Section BirdTerm.

Compute "aaa" == "aaa".                     (* true *)
Compute "aaa" == "aba".                     (* false *)

Reserved Notation "x '@' y" (at level 50, left associativity).
Inductive birdterm : Set :=
| var     of string
| bird    of string
| birdapp of birdterm & birdterm.            (* x @ y *)
Notation "x @ y" := (birdapp x y).

Fixpoint eqBirdterm (u v : birdterm) :=
  match (u, v) with
  | (var u', var v') => u' == v'
  | (bird u', bird v') => u' == v'
  | (u1 @ u2, v1 @ v2) =>
    eqBirdterm u1 v1 && eqBirdterm u2 v2
  | (_ , _) => false
  end.

Definition x := var "x".
Definition y := var "y".
Definition z := var "z".

Definition S := bird "S".
Definition K := bird "K".
Definition I := bird "I".

Lemma apply_eq u1 u2 v1 v2 :
  eqBirdterm (u1 @ u2) (v1 @ v2) = eqBirdterm u1 v1 && eqBirdterm u2 v2.
Proof.
  done.
Qed.

Lemma birdterm_eqP : forall (u v : birdterm),
    reflect (u = v) (eqBirdterm u v).
Proof.
  move=> u v.
  apply: (iffP idP).
  (* eqBirdterm u v -> u = v *)
  - elim: u v.
    + by move=> s1; elim=> s2 // /eqP => ->. (* var *)
    + by move=> s1; elim=> s2 // /eqP => ->. (* bird *)
    + move=> u1 H1 u2 H2.
      elim=> // v1 _ v2 _ H.     (* v の帰納法。 v = v1@v2 が残る。 *)
      move: (H1 v1) => <-.
      move: (H2 v2) => <-.
      * done.                               (* u1 @ u2 = u1 @ u2 *)
      * move: H.
        rewrite apply_eq => /andP.          (* u2 = v2 *)
          by case.
      * move: H.                            (* u1 = v1 *)
        rewrite apply_eq => /andP.
          by case.
  (* u = v -> eqBirdterm u v *)
  -  move=> ->.
     elim: v => //= => u1 H1 v1 H2.
     by apply/andP.
Qed.

Definition birdterm_Mixin := @EqMixin birdterm eqBirdterm birdterm_eqP.
Canonical birdterm_EqType := @EqType birdterm birdterm_Mixin.

Compute x @ I == x @ I.                     (* true *)
Compute x @ I == I @ x.                     (* false *)

Fixpoint in_bird (M : birdterm) (v : string) : bool := (* v \in M *)
  match M with
  | var u => v == u
  | bird _ => false
  | M1 @ M2 => in_bird M1 v || in_bird M2 v
  end.
Canonical birdterm_predType := @mkPredType string birdterm in_bird.

(*
Fixpoint in_bird' (M N : birdterm) : bool := (* N \in M *)
  (M == N) ||
         match M with
         | M1 @ M2 => in_bird' M1 N || in_bird' M2 N
         | _ => false
         end.
Canonical birdterm_predType' := @mkPredType birdterm birdterm in_bird'.
*)

Fixpoint lc_bird (v : string) (M : birdterm) : birdterm :=
  match M with
  | var u =>   if u == v then I else K @ var u
  | bird _ => M
  | M1 @ M2 =>
    let M1' := if v \in M1 then lc_bird v M1 else K @ M1 in
    let M2' := if v \in M2 then lc_bird v M2 else K @ M2 in
            S @ M1' @ M2'
  end.

(* 実行例 *)

(* 合成鳥 *)
Definition B := x @ (y @ z).

(* ものまね鳥 *)
Definition M := x @ x.

Compute lc_bird "z" B.
(* = bird S @ (bird K @ bird x) @ (bird S @ (bird K @ bird y) @ bird I) *)

Compute lc_bird "x" (lc_bird "y" (lc_bird "z" B)).
(* = bird S @
       (bird S @ (bird K @ bird S) @
        (bird S @ (bird K @ bird K) @
         (bird S @ (bird K @ bird S) @ (bird S @ (bird K @ bird K) @ bird I)))) @
       (bird K @
        (bird S @ (bird S @ (bird K @ bird S) @ (bird S @ (bird K @ bird K) @ bird I)) @
         (bird K @ bird I)))
*)

Compute lc_bird "x" M.
(* = bird S @ bird I @ bird I *)

End BirdTerm.

(* END *)
