(**
「The Little Prover」のCoqでの実現
======
2017/08/02

@suharahiromichi


# はじめに

「The Little Prover」（以下 TLP）[1] を読んで、
Coqの上でそれを実現しようとした話です。

TLPで証明しているプログラムをGallinaに移植して証明することは簡単です[2]。

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
   Coqの書き換えはモノイドに対しておこないます。T.B.D.


今回は、上記の1と2について実現した結果をまとめます。
CoqのMathcomp/SSReflect拡張を使用しているので、
それについては[3]を参照してください。
 *)

From mathcomp Require Import all_ssreflect.
From mathcomp Require Import all_algebra.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Set Print All.

(**
# S式の定義

S式をInductiveなデータ型として定義します。ここでは、
S式にことをTLPにあわせて Star型と呼ぶことにします。
*)

(**
##Symbol

Lispではもちろん任意の文字列を(quoteすることで)シンボルとして使用できますが、
ここでは、T, NIL, FOO, BAR, BAZ と ? に限定することにします。
もちろん、本節の定義に追加するこで、シンボルを増やすことができます。

シンボルどうしのbooleanの等式を定義したうえで、それが、
論理式(ライプニッツの等式、Propの等式)と同値であることを証明することで、
boolとPropの間での行き来ができるようになります。
つまり、「==」と「=」の両方を使うことができるようになります。
これをリフレクションといいます[4]。
 *)

Inductive symbol : Type :=
| SYM_T
| SYM_NIL
| SYM_FOO
| SYM_BAR
| SYM_BAZ
| SYM_QUESTION_MARK.

Definition eqSym (s t : symbol) : bool :=
  match (s, t) with
  | (SYM_T, SYM_T) => true
  | (SYM_NIL, SYM_NIL) => true
  | (SYM_FOO, SYM_FOO) => true
  | (SYM_BAR, SYM_BAR) => true
  | (SYM_BAZ, SYM_BAZ) => true
  | (SYM_QUESTION_MARK, SYM_QUESTION_MARK) => true
  | _ => false
  end.

Lemma symbol_eqP : forall (x y : symbol), reflect (x = y) (eqSym x y).
Proof.
  move=> x y.
    by apply: (iffP idP); case x; case y.
Qed.
Definition symbol_eqMixin := @EqMixin symbol eqSym symbol_eqP.
Canonical symbol_eqType := @EqType symbol symbol_eqMixin.

(**
##Atomic

アトムとしては、シンボルの他に自然数もとれるようにします。
アトムについてもリフレクションできるようにします。
 *)

Inductive atomic : Type :=
| ATOM_NAT (n : nat)
| ATOM_SYM (s : symbol).

Definition eqAtom (a b : atomic) : bool :=
  match (a, b) with
  | (ATOM_NAT n, ATOM_NAT m) => n == m
  | (ATOM_SYM s, ATOM_SYM t) => s == t      (* eqSym *)
  | _ => false
  end.

Lemma atomic_eqP : forall (x y : atomic), reflect (x = y) (eqAtom x y).
Proof.
  move=> x y.
  apply: (iffP idP).
  - case: x; case: y; rewrite /eqAtom => x y; move/eqP => H;
    by [rewrite H| | |rewrite H].
  - move=> H; rewrite H.
    case: y H => n H1;
    by rewrite /eqAtom.
Qed.
Definition atomic_eqMixin := @EqMixin atomic eqAtom atomic_eqP.
Canonical atomic_eqType := @EqType atomic atomic_eqMixin.

(**
##Star (S-EXP)

「Star型は、アトム、または、Star型のふたつ要素を連結(Cons)したもの」
と再帰的に定義できます。これがinductiveなデータ型です。
*)

Inductive star : Type :=
| S_ATOM (a : atomic)
| S_CONS (x y : star).

(**
Coqはinductiveなデータ型に対して、inductionできるようになります。
そのために、star_ind という公理が自動的に定義されます。
これは、TLPの第7賞で説明されている "star induction" と同じものです。

Coqによる証明でも、この公理を直接使用することはなく、
star型のデータに対して、
inductionタクティクまたはelimタクティクを使用すると、
この公理が適用されます。
 *)

Check star_ind  : forall P : star -> Prop,
    (forall a : atomic, P (S_ATOM a)) ->
    (forall x : star, P x -> forall y : star, P y -> P (S_CONS x y)) ->
    forall s : star, P s.

(**
Star型についても、booleanの等号を定義して、論理式の等号にリフレク
ションできるようにします。
*)

Fixpoint eqStar (x y : star) : bool :=
  match (x, y) with
  | (S_ATOM a, S_ATOM b) => a == b          (* eqAtom *)
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

(**
Star型のboolの等式について、反射律と対称律が成立することを証明ておきます。
リフレクションを使用してPropの等式に変換することで、簡単に証明できます。

この補題はあとで使用します。
 *)

Lemma refl_eqStar (x : star) : (x == x).
Proof.
  by apply/eqP.
Qed.

Lemma symm_eqStar (x y : star) : (x == y) = (y == x).
Proof.
  by apply/idP/idP; move/eqP=> H; rewrite H.
Qed.


(**
シンボルをS式の中に書くときに簡単になるような略記法を導入します。
「'」は記法の一部ですが、quoted literal のように見えます。
 *)

Notation "'T" := (S_ATOM (ATOM_SYM SYM_T)).
Notation "'NIL" := (S_ATOM (ATOM_SYM SYM_NIL)).
Notation "'FOO" := (S_ATOM (ATOM_SYM SYM_FOO)).
Notation "'BAR" := (S_ATOM (ATOM_SYM SYM_BAR)).
Notation "'BAZ" := (S_ATOM (ATOM_SYM SYM_BAZ)).
Notation "'?" := (S_ATOM (ATOM_SYM SYM_QUESTION_MARK)).

(**
自然数については、（S式の）アトムとの相互変換をする関数を用意します。
 *)

Definition s2n (x : star) : nat :=
  match x with
  | S_ATOM (ATOM_NAT n) => n
  | _ => 0
  end.

Definition n2s (n : nat) : star :=
  S_ATOM (ATOM_NAT n).

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

(**
IFとEQUALは、booleanの等式で判定します。

「IF」というラベルが使えないようなので、「_IF」とします。
 *)
Definition _IF (q a e : star) : star :=
  if q == 'NIL then e else a.

Definition EQUAL (x y : star) : star :=
  if x == y then 'T else 'NIL.

Fixpoint s_size (x : star) : nat :=
  match x with
  | S_CONS a b => s_size a + s_size b + 1
  | _ => 0
  end.

Definition SIZE (x : star) : star :=
  S_ATOM (ATOM_NAT (s_size x)).
Eval compute in SIZE (S_CONS 'T (S_CONS 'T 'T)). (* S_ATOM (ATOM_NAT 2) *)

Definition LT (x y : star) : star :=
  if s2n x < s2n y then 'T else 'NIL.
Eval compute in LT (n2s 2) (n2s 3).         (* 'T *)

Definition PLUS (x y : star) : star :=
  n2s (s2n x + s2n y).
Eval compute in PLUS (n2s 2) (n2s 3).       (* S_ATOM (ATOM_NAT 5) *)


(**
# 埋め込み

S式を論理式(Prop)に埋め込めるようにします。このとき、Lispの真偽の定義から、

「真」 iff 「'NILでないS式」

としなければいけません。
実際には、S式からbooleanの等式 (x != 'NIL) へのコアーションを定義します。
これは、一旦boolを経由することで、論理式(Prop)の否定も扱えるようにするためです。
*)
             
Coercion is_not_nil (x : star) : bool := x != 'NIL. (* ~~ eqStar x 'NIL *)

Check (ATOM 'T) : star.
Check (ATOM 'T) : Prop.
Check ~ (ATOM 'T) : Prop.

Check (ATOM (CONS 'T 'T)) : star.
Check (ATOM (CONS 'T 'T)) : Prop.
Check ~ (ATOM (CONS 'T 'T)) : Prop.

(**
# タクティク

_IFやEQUALを分解するためのタクティクを定義します。
このなかではコアーションが機能しないことに注意してください。
*)

(* Set Printing Coercions. *)

Ltac case_if :=
  match goal with
  | [ |- is_true (is_not_nil (if ?X then _ else _)) ] => case Hq : X; try done
  end.

(**
# J-Bobの「公理」の証明
*)

Theorem equal_same (x : star) :
  (EQUAL x x).
Proof.
(*
  elim: x => [a | x Hxx y Hyy]; rewrite /EQUAL; case_if.
  - by move/eqP in Hq.
  - by move/eqP in Hq.
  Restart.
*)
  rewrite /EQUAL.
    by rewrite refl_eqStar.
Qed.

Lemma l_atom_cons (x y : star) :
  (ATOM (CONS x y)) = 'NIL.
Proof.
  done.
Qed.

Theorem atom_cons (x y : star) :
  (EQUAL (ATOM (CONS x y)) 'NIL).
Proof.
  by rewrite l_atom_cons.
Qed.

Lemma l_car_cons (x y : star) :
  CAR (CONS x y) = x.
Proof.
  done.
Qed.

Theorem car_cons (x y : star) :
  (EQUAL (CAR (CONS x y)) x).
Proof.
  by rewrite l_car_cons equal_same.
Qed.

Lemma l_cdr_cons (x y : star) :
  (CDR (CONS x y)) = y.
Proof.
  done.
Qed.

Theorem cdr_cons (x y : star) :
  (EQUAL (CDR (CONS x y)) y).
Proof.
  by rewrite l_cdr_cons equal_same.
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

Lemma l_size_plus_1 (x y : star) (n m : nat) :
  s_size x = n -> s_size y = m -> s_size (CONS x y) = n + m + 1.
Proof.
  move=> Hx Hy /=.
  by rewrite Hx Hy.
Qed.

Lemma l_size_plus_2 (x : star) (n m l : nat) :
  ATOM x = 'NIL -> s_size (CAR x) = n ->
  s_size (CDR x) = m -> s_size x = n + m + 1.
Proof.
  move=> Ha Hx Hy /=.
  Check @l_size_plus_1 (CAR x) (CDR x) n m.
  rewrite -(@l_size_plus_1 (CAR x) (CDR x) n m).
  - by rewrite l_cons_car_cdr.
  - by [].
  - by [].
Qed.

Lemma l_size_car (x : star) :
  ATOM x = 'NIL -> s_size (CAR x) < s_size x.
Proof.
  elim: x.
  - by move=> a Hc /=.
  - move=> x Hx y Hy Hc /=.
      (* s_size x < s_size x + s_size y + 1 *)
      by rewrite addn1 ltnS leq_addr.
Qed.

Lemma l_size_cdr (x : star) :
  ATOM x = 'NIL -> s_size (CDR x) < s_size x.
Proof.
  elim: x.
  - by move=> a Hc /=.
  - move=> x Hx y Hy Hc /=.
    (* s_size y < s_size x + s_size y + 1 *)
    rewrite [s_size x + s_size y]addnC.
      by rewrite addn1 ltnS leq_addr.
Qed.

Theorem size_car (x : star) :
  (_IF (ATOM x) 'T (EQUAL (LT (SIZE (CAR x)) (SIZE x)) 'T)).
Proof.
  rewrite /_IF; case_if.
  rewrite /LT /= l_size_car.
  - by [].
  - by apply/eqP.
Qed.

Theorem size_cdr (x : star) :
  (_IF (ATOM x) 'T (EQUAL (LT (SIZE (CDR x)) (SIZE x)) 'T)).
Proof.
  rewrite /_IF; case_if.
  rewrite /LT /= l_size_cdr.
  - by [].
  - by apply/eqP.
Qed.


(**
# 「公理」を書換規則として使う
 *)

(**
## IFとEQUALの補題
 *)

Lemma ifAP (q x y : star) : (_IF q (EQUAL x y) 'T) -> (q -> x = y).
Proof.
  rewrite /_IF /EQUAL => H Hq.
  case Hxy : (x == y); case Hqq : (q == 'NIL).
  - by apply/eqP; rewrite Hxy.
  - by apply/eqP; rewrite Hxy.
  - by move/eqP in Hqq; rewrite Hqq in Hq.
  - by rewrite Hqq Hxy in H.
Qed.

Lemma ifEP (q x y : star) : (_IF q 'T (EQUAL x y)) -> (~q -> x = y).
Proof.
  rewrite /_IF /EQUAL => H Hq.
  case Hxy : (x == y); case Hqq : (q == 'NIL).
  - by apply/eqP; rewrite Hxy.
  - by apply/eqP; rewrite Hxy.
  - by rewrite Hqq Hxy in H.
  - rewrite /is_not_nil in Hq.
    move/negP in Hq.
    move/negP/negP in Hqq.
    by rewrite Hqq in Hq.
Qed.

(**
## 書き換えの例
 *)

Check ifAP (if_nest_A _ _ _).
Check ifEP (size_cdr _).


(**
# 参考文献

[1] Daniel P. Friedman, Carl Eastlund, "The Little Prover", MIT Press, 2015.

https://mitpress.mit.edu/books/little-prover

[2] 「The Little Prover の memb?/remb をCoqで解いてみる（サブリスト改訂版）」

https://github.com/suharahiromichi/coq/blob/master/prog/coq_membp_remb_3.v

[3] Mathematical Components resources

http://ssr.msr-inria.inria.fr/

[4] 「リフレクションのしくみをつくる」

http://qiita.com/suharahiromichi/items/9cd109386278b4a22a63
 *)

(* END *)
