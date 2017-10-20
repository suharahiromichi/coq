(**
「The Little Prover」のCoqでの実現
======
2017/08/02


2017/08/07 シンボルをstringを使うようにした。
2017/08/09 case: eqP を使うようにした。
2017/08/11 prove_nil タクティクを完成した。

@suharahiromichi

この文書のソースコードは以下にあります。


https://github.com/suharahiromichi/coq/blob/master/lisp/tlp_lisp_2.v


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


CoqのMathcomp/SSReflect拡張を使用しているので、
それについては[3]を参照してください。
 *)

From mathcomp Require Import all_ssreflect.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Set Print All.

Require Import Ascii.
Require Import String.
Require Import ssr_string.

Check "aaa"%string = "aaa"%string : Prop.
Check "aaa"%string == "aaa"%string : bool.
Check "aaa"%string == "aaa"%string : Prop.

Section TLP.
  
(**
# S式の定義

S式をInductiveなデータ型として定義します。ここでは、
S式にことをTLPにあわせて Star型と呼ぶことにします。
*)

(**
##Atomic

アトムどうしのbooleanの等式を定義したうえで、それが、
論理式(ライプニッツの等式、Propの等式)と同値であることを証明することで、
boolとPropの間での行き来ができるようになります。
つまり、「==」と「=」の両方を使うことができるようになります。
これをリフレクションといいます[4]。

アトムとしては、シンボルの他に自然数もとれるようにします。
 *)

Inductive atomic : Type :=
| ATOM_NAT (n : nat)
| ATOM_SYM (s : string).

Definition eqAtom (a b : atomic) : bool :=
  match (a, b) with
  | (ATOM_NAT n, ATOM_NAT m) => n == m
  | (ATOM_SYM s, ATOM_SYM t) => s == t      (* eqString *)
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
##Star型 (S-EXP)

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

Definition s_quote (s : string) : star :=
  (S_ATOM (ATOM_SYM s)).
Notation "\' s" := (S_ATOM (ATOM_SYM s)) (at level 60).

Notation "'T" := (S_ATOM (ATOM_SYM "T")).
Notation "'NIL" := (S_ATOM (ATOM_SYM "NIL")).
Notation "'FOO" := (S_ATOM (ATOM_SYM "FOO")).
Notation "'BAR" := (S_ATOM (ATOM_SYM "BAR")).
Notation "'BAZ" := (S_ATOM (ATOM_SYM "BAZ")).
Notation "'?" := (S_ATOM (ATOM_SYM "?")).

Check 'NIL : star.
Check \'"aaa" : star.

Check \'"FOO" : star.
Check 'FOO : star.
Compute \'"FOO" == 'FOO.                    (* true *)


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
Set Printing Coercions.
を使うと、コアーションがどのように使われているか分かります。
*)

Check is_true (is_not_nil (ATOM 'T)) : Prop.
Check ~ is_true (is_not_nil (ATOM 'T)) : Prop.

(**
のちの証明で便利なように、'NILに関する補題を証明しておきます。


``_ != _`` は ``~~(_ = _)`` の略記なので、次はis_not_nil と同じことです。
が、忘れがちなので定義しておきます。
 *)

Lemma not_nil_E q : ~~ (q == 'NIL) = q.
Proof.
  done.
Qed.

(**
二重否定を解消するための補題です。
*)

Lemma not_not_nil__nil_E q : ~~ (q != 'NIL) = (q == 'NIL).
Proof.
  by case: (q == 'NIL).
Qed.

Lemma not_q__q_nil_E (q : star) : ~q <-> q = 'NIL.
Proof.
  split.
  - rewrite /is_not_nil => /negP.
    by rewrite not_not_nil__nil_E => /eqP.
  - by move=> Hq; rewrite Hq.
Qed.

Lemma q__q_not_nil_E (q : star) : q <-> q <> 'NIL.
Proof.
  rewrite /is_not_nil.
  split.
  - move=> H. by apply/eqP.
  - by move/eqP.
Qed.

(**
# タクティク

## case_if (不使用)

_IFやEQUALを分解するためのタクティクを定義します。
このなかではコアーションが機能しないことに注意してください。

ほとんどの場合、case: eqP または case: ifP で置き換えることができるので、使用していない。
*)

Ltac case_if :=
  match goal with
  | [ |- is_true (is_not_nil (if ?X then _ else _)) ] => case Hq : X => //
  end.

(**
## prove_nil

ゴールおよび前提の NIL に関する命題を q=NIL または q<>NIL に変換するものです。
前提とゴールが同じでなくても、
前提に q=NILとq<>NILの両方があるなら、矛盾からdoneで証明が終わることができます。

なお、~~(q==NIL) は q!=NIL と同じなので、条件としてあらわれません。
 *)

Ltac prove_nil :=
  repeat match goal with
         | [ H : is_true (?q != 'NIL)      |- _ ] => move/eqP            in H
         | [ H : is_true (is_not_nil ?q)   |- _ ] => move/q__q_not_nil_E in H

         | [ H : is_true (?q == 'NIL)      |- _ ] => move/eqP            in H
         | [ H : ~ is_true (is_not_nil ?q) |- _ ] => move/not_q__q_nil_E in H

         | [ |- is_true (?q != 'NIL)            ] => apply/eqP
         | [ |- is_true (is_not_nil ?q)         ] => apply/q__q_not_nil_E

         | [ |- is_true (?q == 'NIL)            ] => apply/eqP
         | [ |- ~ is_true (is_not_nil ?q)       ] => apply/not_q__q_nil_E

         end.

(**
# IFとEQUALの補題

TLPの定理は、(IF Q 'T (EQUAL X Y)) または (IF Q (EQUAL X Y) 'T) のかたちをしているので、
それをCoqの条件付きのequalと同値であることを証明しておきます。
TLPの定理の証明や、その定理を使うときに使用します。
 *)

Lemma ifAP {q x y : star} : (_IF q (EQUAL x y) 'T) <-> (q -> x = y).
Proof.
  split.
  - rewrite /_IF /EQUAL.
    case: ifP => Hq_nil.
    + move=> _ Hq.
      by prove_nil.
    + case: ifP; move/eqP; by prove_nil.
      
  - move=> H.
    rewrite /_IF; case: ifP => // Hnot_nil_q.   (* q <> NIL *)
    rewrite /EQUAL; case: ifP => // => Hx_ne_y. (* x <> y) *)
    exfalso.
    
    apply negbT in Hx_ne_y.
    move/negP in Hx_ne_y.
    apply: Hx_ne_y.
    apply/eqP.
    apply: H.
    move/eqP in Hnot_nil_q.
    by prove_nil.
Qed.

Lemma ifEP {q x y : star} : (_IF q 'T (EQUAL x y)) <-> (~q -> x = y).
Proof.
  split.
  - rewrite /_IF /EQUAL.
    case: eqP => Hq_nil.
    + by case: eqP.
    + move=> _ Hnq.
      by prove_nil.
    
  - move=> H.
    rewrite /_IF; case: eqP => // Hq_nil.       (* q = NIL  *)
    rewrite /EQUAL; case: eqP => // => Hx_ne_y. (* x <> y) *)
    exfalso.
    apply: Hx_ne_y.
    apply: H.
    by prove_nil.
Qed.

(*
    Set Printing Coercions.
 *)

(**
# J-Bobの「公理」の証明
*)

Theorem equal_same (x : star) :
  (EQUAL x x).
Proof.
  rewrite /EQUAL.
    by rewrite refl_eqStar.
Qed.

Theorem atom_cons (x y : star) :
  (EQUAL (ATOM (CONS x y)) 'NIL).
Proof.
  done.
Qed.

Theorem car_cons (x y : star) :
  (EQUAL (CAR (CONS x y)) x).
Proof.
  rewrite /EQUAL.
  by case: eqP.
Qed.

Theorem cdr_cons (x y : star) :
  (EQUAL (CDR (CONS x y)) y).
Proof.
  rewrite /EQUAL.
  by case: eqP.
Qed.

Theorem equal_swap (x y : star) :
  (EQUAL (EQUAL x y) (EQUAL y x)).
Proof.
  rewrite {2}/EQUAL {2}/EQUAL.
  rewrite {1}symm_eqStar.
    by rewrite equal_same.
Qed.

Theorem equal_if (x y : star) :
  (_IF (EQUAL x y) (EQUAL x y) 'T).
Proof.
    by rewrite /_IF; case: eqP; move/eqP.
Qed.

Theorem if_true (x y : star) :
  (EQUAL (_IF 'T x y) x).
Proof.
    by rewrite /EQUAL; case: eqP.
Qed.

Theorem if_false (x y : star) :
  (EQUAL (_IF 'NIL x y) y).
Proof.
    by rewrite /EQUAL; case: eqP.
Qed.

Lemma l_if_same (x y : star) :
  (_IF x y y) = y.
Proof.
  case: x.
  - case.
    + done.                                 (* NAT *)
    + rewrite /_IF => s.
      by case: eqP.                         (* SYM *)
  - done.                                   (* CONS *)
Qed.

Theorem if_same (x y : star) :
  (EQUAL (_IF x y y) y).
Proof.
  rewrite l_if_same.
    by rewrite equal_same.
Qed.

Theorem if_nest_A (x y z : star) :
  (_IF x (EQUAL (_IF x y z) y) 'T).
Proof.
  rewrite /_IF; case: eqP => //.
  by rewrite equal_same.
Qed.

Theorem if_nest_E (x y z : star) :
  (_IF x 'T (EQUAL (_IF x y z) z)).
Proof.
  rewrite /_IF; case: eqP => //.
  by rewrite equal_same.
Qed.

Lemma l_cons_car_cdr (x : star) :
  (ATOM x) = 'NIL -> (CONS (CAR x) (CDR x)) = x.
Proof.
  move=> Hn.
  case Hc: x; rewrite /CONS => //.
  by rewrite Hc in Hn.                      (* 前提の矛盾 *)
Qed.

Theorem cons_car_cdr (x : star) :
  (_IF (ATOM x) 'T (EQUAL (CONS (CAR x) (CDR x)) x)).
Proof.
  rewrite /_IF; case: eqP => Hq //.
  rewrite l_cons_car_cdr //.
  by rewrite equal_same.
Qed.

Lemma l_size_car (x : star) :
  ATOM x = 'NIL -> s_size (CAR x) < s_size x.
Proof.
  elim: x.
  - by move=> a Hc //.
  - move=> x Hx y Hy Hc /=.
    (* s_size x < s_size x + s_size y + 1 *)
    by rewrite addn1 ltnS leq_addr.
Qed.

Lemma l_size_cdr (x : star) :
  ATOM x = 'NIL -> s_size (CDR x) < s_size x.
Proof.
  elim: x.
  - by move=> a Hc //.
  - move=> x Hx y Hy Hc /=.
    (* s_size y < s_size x + s_size y + 1 *)
    rewrite [s_size x + s_size y]addnC.
    by rewrite addn1 ltnS leq_addr.
Qed.

Theorem size_car (x : star) :
  (_IF (ATOM x) 'T (EQUAL (LT (SIZE (CAR x)) (SIZE x)) 'T)).
Proof.
  apply/ifEP => Hq.
  rewrite /LT /= l_size_car.
  - by [].
  - by apply/not_q__q_nil_E.
Qed.

Theorem size_cdr (x : star) :
  (_IF (ATOM x) 'T (EQUAL (LT (SIZE (CDR x)) (SIZE x)) 'T)).
Proof.
  apply/ifEP => Hq.
  rewrite /LT /= l_size_cdr.
  - by [].
  - by apply/not_q__q_nil_E.
Qed.

(**
# 「公理」を書換規則として使う
 *)

(**
## 書き換えの例
 *)

Section TLP_REWRITE_TEST.
  Variables x y z : star.

  Check iffLR ifAP (if_nest_A x y z) : x -> (_IF x y z) = y.
  Check iffLR ifEP (size_cdr x)      : ~ ATOM x -> (LT (SIZE (CDR x)) (SIZE x)) = 'T.

End TLP_REWRITE_TEST.

End TLP.

(**
# 参考文献

[1] Daniel P. Friedman, Carl Eastlund, "The Little Prover", MIT Press, 2015.

https://mitpress.mit.edu/books/little-prover

中野圭介監訳、「定理証明手習い」、ラムダノート、2017。

https://www.lambdanote.com/collections/littleprover


[2] 「The Little Prover の memb?/remb をCoqで解いてみる（サブリスト改訂版）」

https://github.com/suharahiromichi/coq/blob/master/prog/coq_membp_remb_3.v

[3] Mathematical Components resources

http://ssr.msr-inria.inria.fr/

[4] 「リフレクションのしくみをつくる」

http://qiita.com/suharahiromichi/items/9cd109386278b4a22a63
 *)

(* END *)
