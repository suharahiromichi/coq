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
  - move=> ->.
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
  | M1 @ M2 =>
    [predU in_bird M1 & in_bird M2] v (* in_bird M1 v || in_bird M2 v *)
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

(* α除去のプログラム *)
Fixpoint lc_bird (v : string) (T : birdterm) : birdterm :=
  match T with
  | var u => if u == v then I else K @ var u
  | bird _ => T
  | T1 @ T2 =>
    let T1' := if v \in T1 then lc_bird v T1 else K @ T1 in
    let T2' := if v \in T2 then lc_bird v T2 else K @ T2 in
            S @ T1' @ T2'
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

Lemma apply_notinE (T1 T2 : birdterm) (v : string) :
  (v \notin T1 @ T2) = (v \notin T1) && (v \notin T2).
Proof.
  rewrite /mem /in_mem /in_bird /=.
  Search (~~ _ = ~~ _ && ~~ _).
  by apply: negb_or.
Qed.

Lemma apply_inE (T1 T2 : birdterm) (v : string) :
  (v \in T1 @ T2) = (v \in T1) || (v \in T2).
Proof.
  (* rewrite /inE. *)
  by rewrite /mem /in_mem /in_bird /=.
Qed.

Lemma neq_sym (T : eqType) (x y :T) : (x != y) = (y != x).
Proof.
  by apply/idP/idP; apply: contra_neq.
Qed.

Lemma neq__notin (s v : string) : s <> v -> v \notin var s.
Proof.
(*
  move=> H.
  Search _ (_ \notin _).
  apply/memPn => u.
  rewrite /mem /in_mem /in_bird /=.
  move/eqP => ->.
  by apply/eqP.
*)  
  Restart.
  move=> H.
  rewrite /mem /in_mem /in_bird /=.
  move/eqP in H.
  by rewrite neq_sym.
Qed.

(* 泥縄の補題 *)
Lemma notin_l (v : string) (T S1 S2 : birdterm) :
  v \notin S1 -> v \notin S2 -> v \notin (if v \in T then S1 else S2 @ T).
Proof.
  case H : (v \in T) => HS1 HS2.
  (* v \in T *)
  - done.
  (* v \notin T *)
  (* 次の2行で、H : (v \in T) = false を
     H : v \notin T に書き換える。 *)
  - move/eqP in H.
    rewrite eqbF_neg in H.
    rewrite apply_notinE.
    by apply/andP; split.
Qed.

(* α除去の証明 *)
Theorem notin__lc_bird : forall (T : birdterm) (v : string), v \notin lc_bird v T.
Proof.
  elim.
  - rewrite /lc_bird // => s v.             (* v \in var u *)
    case H : (s == v).
    (* s = v *)
    + by [].
    (* s <> v *)
    + move/eqP in H.
      rewrite apply_notinE.
      apply/andP.
      split.
      * done.
      * by apply: neq__notin.
  - by [].                                  (* v \in bird s *)
  - move=> T1 H1 T2 H2 v /=.                (* v \in bird T1 @ T2 *)
    rewrite 2!apply_notinE /=.
    by apply/andP; split; apply: notin_l.
    
(*
    + case H : (v \in T1).
      * by apply H1.
      * rewrite apply_notinE.
        apply/andP.
        split.
        ** done.
        ** move/eqP in H.
           by rewrite eqbF_neg in H.
    + case H : (v \in T2).
      * by apply H2.
      * rewrite apply_notinE.
        apply/andP.
        split.
        ** done.
        ** move/negP in H.
           by apply/negP.
 *)
Qed.

End BirdTerm.

(* END *)

(* おまけ。否定の表現は6種類ある。 *)

Goal forall (b : bool), ~~ b -> ~ b.        (* negb と not *)
Proof.
  move=> b.
  move/negP.
  done.
Qed.

Goal forall (b : bool), b == false -> b = false.
Proof.
  move=> b.
  move/eqP.
  done.
Qed.

Goal forall (b : bool), ~~ b -> b == false.
  move=> b.
  rewrite eqbF_neg.
  done.
Qed.

Goal forall (b : bool), b != true -> ~~ b.  (* negb eqb true *)
Proof.
  move=> b.
  move/eqP/negP.
  done.
Qed.

Goal forall (b : bool), b <> true -> ~~ b.  (* not eq true *)
Proof.
  move=> b.
  move/negP.
  done.
Qed.

(* おまけ。終わり。 *)

(* おまけのおまけ。不等号は5種類ある。 *)
(* ただし、= false を <> true にしたののは、上を参照のこと。 *)

Goal forall (x y : nat), (x == y) == false -> (x == y) = false.
  move=> x y.
  (* 外側の 「== false」 に適用されている。上とおなじ。 *)
  move/eqP.
  Undo 1.
  move/(elimT eqP).
  done.
Qed.

Goal forall (x y : nat), (x == y) = false -> x <> y.
  move=> x y.
  move/eqP.
  Undo 1.
  move/(elimF eqP).
  done.
Qed.

Goal forall (x y : nat), (x != y) -> x <> y. (* negb eqb *)
  move=> x y.
  move/eqP.
  Undo 1.
  move/(elimN eqP).
  done.
Qed.

Goal forall (x y : nat), ~ (x == y) -> x != y. (* not eqb *)
  move=> x y.
  move/negP.
  Undo 1.
  move/(introT negP).
  done.
Qed.

(* 等号も4種類あるが、ひとつだけ。 *)
Goal forall (x y : nat), (x != y) = false -> x = y.
  move=> x y.
  move/eqP.
  Undo 1.
  move/(elimNf eqP).
  done.
Qed.


Check elimT (@eqP _ x y) : x == y -> x = y.
Check elimF (@eqP _ x y) : (x == y) = false -> x <> y.
Check elimN (@eqP _ x y) : x != y -> x <> y.
Check elimNf (@eqP _ x y) : (x != y) = false -> x = y.

Check introT (@eqP _ x y) : x = y -> x == y.
Check introF (@eqP _ x y) : x <> y -> (x == y) = false.
Check introN (@eqP _ x y) : x <> y -> x != y.
Check introNf (@eqP _ x y) : x = y -> (x != y) = false.
  
Check elimTn.               (* reflect 述語中に否定が含まれる場合。 *)
Check elimFn.

(* おまけのおまけ。終わり。 *)

