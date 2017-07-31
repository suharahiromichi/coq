(**
「The Little Prover」のCoqでの実現
======
2017/07/28

@suharahiromichi


# はじめに

Coqユーザ（と胸を張れるほどではありませんが）が、
「The Little Prover」（以下 TLP）を読んで、
Coqの上でそれを実現しようとした話です。

TLPで証明しているプログラムをGallinaに移植して証明することは簡単です[1]。

しかし、これからやろうとするのは、
TLPの対象言語であるLispの「意味」をCoqで実現しようと思います。
それによって、

1. Coqはinductiveに定義したデータ型はinductionができることを原理としています。
   これに対して、TLPはinductionはハードコードされています。
   結果として、帰納法の公理からすべての定理を導くことができず、多くの「公理」を導入しています。
   帰納法の公理を使って、TLPの「公理」を証明することで、TLPの正しさが検証できるでしょう。

2. TLPはLispのプログラム（当然S式を返す）がnilでないことを証明する。
   これをもって、そのプログラムの意味する論理式が真であるとします。
   Coqは論理式（Prop型）でなければ証明できないので、
   これをLispのプログラムをCoqの論理式に埋め込むことで実現します。

3. TPLの証明は、(EQUAL A B) による書き換えで進みますが、
   Coqの書き換えはモノイドに対しておこないます。
   これを実現したい。

今回は、上記の1と2について実現した結果をまとめます。
 *)


From mathcomp Require Import all_ssreflect.
From mathcomp Require Import all_algebra.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Set Print All.

(**
# S式の定義
*)

(**
Symbol
 *)

Inductive symbol : Type :=
| SYM_T
| SYM_NIL
| SYM_QUESTION_MARK.

Definition eqSym (s t : symbol) : bool :=
  match (s, t) with
  | (SYM_T, SYM_T) => true
  | (SYM_NIL, SYM_NIL) => true
  | (SYM_QUESTION_MARK, SYM_QUESTION_MARK) => true
  | _ => false
  end.

Lemma symbol_eqP : forall (x y : symbol), reflect (x = y) (eqSym x y).
Proof.
  move=> x y.
    by apply (iffP idP); case x; case y.
Qed.
Definition symbol_eqMixin := @EqMixin symbol eqSym symbol_eqP.
Canonical symbol_eqType := @EqType symbol symbol_eqMixin.

(**
Literal
 *)

Inductive literal : Type :=
| LIT_NAT (n : nat)
| LIT_SYM (s : symbol).

Definition eqLit (a b : literal) : bool :=
  match (a, b) with
  | (LIT_NAT n, LIT_NAT m) => n == m
  | (LIT_SYM s, LIT_SYM t) => s == t        (* eqSym *)
  | _ => false
  end.

Lemma literal_eqP : forall (x y : literal), reflect (x = y) (eqLit x y).
Proof.
  move=> x y.
  apply: (iffP idP).
  - case: x; case: y; rewrite /eqLit => x y; move/eqP => H;
    by [rewrite H| | |rewrite H].
  - move=> H; rewrite H.
    case: y H => n H1;
    by rewrite /eqLit.
Qed.
Definition literal_eqMixin := @EqMixin literal eqLit literal_eqP.
Canonical literal_eqType := @EqType literal literal_eqMixin.

(**
Star (S-EXP)
*)

Inductive star : Type :=
| S_ATOM (a : literal)
| S_CONS (x y : star).

Fixpoint eqStar (x y : star) : bool :=
  match (x, y) with
  | (S_ATOM a, S_ATOM b) => a == b          (* eqLit *)
  | (S_CONS x1 y1, S_CONS x2 y2) =>
    eqStar x1 x2 && eqStar y1 y2
  | _ => false
  end.

Lemma eqCons x y x' y' : (x = x' /\ y = y') -> S_CONS x y = S_CONS x' y'.
Proof.
  case=> Hx Hy.
  by rewrite Hx Hy.
Qed.

Lemma star_eqP_1 : forall (x y : star), eqStar x y -> x = y.
Proof.
  elim.
  - move=> a.
    elim=> b.
    + move/eqP=> H.                         (* ATOM どうし *)
        by rewrite H.  
    + done.                                 (* ATOM と CONS *)
  - move=> x Hx y Hy.
    elim.
    + done.                                 (* CONS と ATOM *)
    + move=> x' IHx y' IHy.                 (* CONS と CONS *)
      move/andP.
      case=> Hxx' Hyy'.
      apply: eqCons.
      split.
      * by apply: (Hx x').
      * by apply: (Hy y').
Qed.

Lemma star_eqP_2 : forall (x y : star), x = y -> eqStar x y.
Proof.
  move=> x y H; rewrite -H {H}.
  elim: x.
  - by move=> a /=.
  - move=> x Hx y' Hy /=.
    by apply/andP; split.
Qed.

Lemma star_eqP : forall (x y : star), reflect (x = y) (eqStar x y).
Proof.
  move=> x y.
  apply: (iffP idP).
  - by apply: star_eqP_1.
  - by apply: star_eqP_2.
Qed.
Definition star_eqMixin := @EqMixin star eqStar star_eqP.
Canonical star_eqType := @EqType star star_eqMixin.

Notation "'T" := (S_ATOM (LIT_SYM SYM_T)).
Notation "'NIL" := (S_ATOM (LIT_SYM SYM_NIL)).
Notation "'?" := (S_ATOM (LIT_SYM SYM_QUESTION_MARK)).

Lemma refl_eqStar (x : star) : (x == x).
Proof.
  by apply/eqP.
Qed.

Lemma symm_eqStar (x y : star) : (x == y) = (y == x).
Proof.
  by apply/idP/idP; move/eqP=> H; rewrite H.
Qed.

(**
# 組込関数の定義
*)

Definition CONS (x y : star) := S_CONS x y.

Definition CAR  (x : star) : star :=
  match x with
  | S_ATOM _ => 'NIL
  | S_CONS x _ => x
  end.

Definition CDR (x : star) : star :=
  match x with
  | S_ATOM _ => 'NIL
  | S_CONS _ y => y
  end.

Definition ATOM (x : star) : star :=
  match x with
  | S_ATOM _ => 'T
  | S_CONS _ _ => 'NIL
  end.

Definition _IF (q a e : star) : star :=
  if q == 'NIL then e else a.

Definition EQUAL (x y : star) : star :=
  if x == y then 'T else 'NIL.

(**
# 埋め込み

S-EXPを論理式(Prop)に埋め込むためのコアーションを定義する。
否定が扱えるように、一旦boolを経由する。
*)
             
Coercion is_not_nil (x : star) : bool := ~~ eqStar x 'NIL.

Check (ATOM 'T) : star.
Check (ATOM 'T) : Prop.
Check ~ (ATOM 'T) : Prop.

Check (ATOM (CONS 'T 'T)) : star.
Check (ATOM (CONS 'T 'T)) : Prop.
Check ~ (ATOM (CONS 'T 'T)) : Prop.

(**
# タクティク

_IFやEQUALを分解するためのタクティクを定義する。
このなかではコアーションが機能しないことに注意すること。
*)

(* Set Printing Coercions. *)

Ltac case_if :=
  match goal with
  | [ |- is_true (is_not_nil (if ?X then _ else _)) ] => case Hq : X; try done
  end.

(**
# J-Bobの「公理」を証明する。
*)

Theorem atom_cons (x y : star) :
  (ATOM (CONS x y)) = 'NIL.
Proof.
  done.
Qed.

Theorem car_cons (x y : star) :
  CAR (CONS x y) = x.
Proof.
  done.
Qed.

Theorem cdr_cons (x y : star) :
  (CDR (CONS x y)) = y.
Proof.
  done.
Qed.

Theorem equal_same (x : star) :
  (EQUAL x x).
Proof.
(*
  elim: x => [a | x Hxx y Hyy]; rewrite /EQUAL; case_if. (* move: Hq => Hq. *)
  - by move/eqP in Hq.
  - by move/eqP in Hq.
  Restart.
*)
  rewrite /EQUAL.
    by rewrite refl_eqStar.
Qed.

Lemma l_equal_swap (x y : star) :
  (EQUAL x y) = (EQUAL y x).
Proof.
  rewrite /EQUAL.
    by rewrite {1}symm_eqStar.
Qed.
                          
Theorem equal_swap (x y : star) :
  (EQUAL (EQUAL x y) (EQUAL y x)).
Proof.
  rewrite [(EQUAL y x)]l_equal_swap.
    by rewrite equal_same.
Qed.

Theorem equal_if (x y : star) :
  (_IF (EQUAL x y) (EQUAL x y) 'T).
Proof.
  rewrite /_IF; case_if; move: Hq => Hc.
  move/eqP in Hc.
  rewrite /EQUAL; case_if; move: Hq => Hd.
  rewrite /EQUAL in Hc.
    by rewrite Hd in Hc.
Qed.

Theorem if_true (x y : star) :
  (EQUAL (_IF 'T x y) x).
Proof.
  rewrite /EQUAL; case_if.
  rewrite /_IF /= in Hq.
    by move/eqP in Hq.
Qed.

Theorem if_false (x y : star) :
  (EQUAL (_IF 'NIL x y) y).
Proof.
  rewrite /EQUAL; case_if.
    by rewrite /_IF /=; move/eqP in Hq.
Qed.

Lemma l_if_same (x y : star) :
  (_IF x y y) = y.
Proof.
  case: x.
  - case.
    + done.                                 (* NAT *)
    + case; done.                           (* SYM *)
  - done.                                   (* CONS *)
Qed.

Theorem if_same (x y : star) :
  (EQUAL (_IF x y y) y).
Proof.
  rewrite l_if_same.
    by rewrite equal_same.
Qed.

Lemma l_if_nest_A (x y z : star) :
  x != 'NIL -> (_IF x y z) = y.
Proof.
  rewrite /_IF.
  by case Hc : (x == 'NIL) => Hd.
Qed.

Theorem if_nest_A (x y z : star) :
  (_IF x (EQUAL (_IF x y z) y) 'T).
Proof.
  rewrite /_IF; case_if.
  by rewrite equal_same.
Qed.

Lemma l_if_nest_E (x y z : star) :
  x = 'NIL -> (_IF x y z) = z.
Proof.
(*
  rewrite /_IF.
  case Hc : (x == 'NIL) => Hd.
  done.
    by rewrite Hd in Hc.
  Restart.
*)
  move=> H.
  by rewrite H.
Qed.

Theorem if_nest_E (x y z : star) :
  (_IF x 'T (EQUAL (_IF x y z) z)).
Proof.
(*  
  rewrite {1}/_IF; case_if.
  rewrite l_if_nest_E.
  - by rewrite equal_same.
  - by apply/eqP; rewrite Hq.
  Restart.
 *)
  rewrite /_IF; case_if.
    by rewrite equal_same.
Qed.

Lemma l_cons_car_cdr (x : star) :
  (ATOM x) = 'NIL -> (CONS (CAR x) (CDR x)) = x.
Proof.
  intros Hn.
  case Hc: x; rewrite /CONS => /=.
  - by rewrite Hc in Hn.                    (* 前提の矛盾 *)
  - by [].
Qed.

Theorem cons_car_cdr (x : star) :
  (_IF (ATOM x) 'T (EQUAL (CONS (CAR x) (CDR x)) x)).
Proof.
  rewrite /_IF; case_if.
  rewrite l_cons_car_cdr.
  - by rewrite equal_same.
  - apply/eqP.
      by rewrite Hq.
Qed.

(* END *)
