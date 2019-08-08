(**
「The Little Prover」のCoqでの実現
======
2017/08/02


2017/08/07 シンボルをstringを使うようにした。
2017/08/09 case: eqP を使うようにした。
2017/08/11 prove_nil タクティクを完成した。
2017/10/21 「定理証明手習い」発刊記念。
2019/07/24 Stringの定義をマージした。
2019/08/08 Proof Summit の発表に対応させる。

@suharahiromichi

この文書のソースコードは以下にあります。


https://github.com/suharahiromichi/coq/blob/master/lisp/tlp_lisp_6.v


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
また、見ただけでは解らないようなタクティカル（"by case=> -> ->" など) の使用は避けています。
 *)

From mathcomp Require Import all_ssreflect.
Require Import String.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
(* Set Print All. *)

(**
# 文字列の定義

バニラCoqの定義を使用し、eqTypeのインスタンスにすることで、「==」が使えるようになります。
 *)
Definition string_eqMixin := @EqMixin string String.eqb String.eqb_spec.
Canonical string_eqType := @EqType string string_eqMixin.
Open Scope string_scope.

Check "aaa" = "aaa" : Prop.
Check "aaa" == "aaa" : bool.
Check "aaa" == "aaa" : Prop.

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
    by [rewrite H | | | rewrite H].
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

Inductive star T : Type :=
| S_ATOM of T
| S_CONS of star T & star T.

(**
Coqはinductiveなデータ型に対して、inductionできるようになります。
そのために、star_ind という公理が自動的に定義されます。
これは、TLPの第7章で説明されている "star induction" と同じものです。

Coqによる証明でも、この公理を直接使用することはなく、
star型のデータに対して、
inductionタクティクまたはelimタクティクを使用すると、
この公理が適用されます。
 *)

Check star_ind : forall (T : Type) (P : star T -> Prop),
    (forall t : T, P (S_ATOM t)) ->
    (forall s : star T, P s -> forall s0 : star T, P s0 -> P (S_CONS s s0)) ->
    forall s : star T, P s.

(**
Star型についても、booleanの等号を定義して、論理式の等号にリフレク
ションできるようにします。
*)

Fixpoint eqStar {T : eqType} (x y : star T) : bool :=
  match (x, y) with
  | (S_ATOM a, S_ATOM b) => a == b          (* eqType *)
  | (S_CONS x1 y1, S_CONS x2 y2) => eqStar x1 x2 && eqStar y1 y2
  | _ => false
  end.

Lemma eqCons {T : eqType} (x y x' y' : star T) :
  (x = x' /\ y = y') -> S_CONS x y = S_CONS x' y'.
Proof.
  case=> Hx Hy.
    by rewrite Hx Hy.
Qed.

Lemma star_eqP : forall (T : eqType) (x y : star T), reflect (x = y) (eqStar x y).
Proof.
  move=> T x y.
  apply: (iffP idP).
  - elim: x y.
    + move=> x'.
      elim=> y.
      * by move/eqP => <-.                  (* ATOM と ATOM *)
      * done.                               (* ATOM と CONS *)
    + move=> x Hx y Hy.
      elim.
      * done.                               (* CONS と ATOM *)
      * move=> x' IHx y' IHy.               (* CONS と CONS *)
        move/andP.
        case=> Hxx' Hyy'.
        apply: eqCons.
        split.
        ** by apply: (Hx x').
        ** by apply: (Hy y').
  -  move=> <-.
     elim: x.
     * by move=> a /=.
     * move=> x Hx y' Hy /=.
         by apply/andP; split.
Qed.

Definition star_eqMixin (T : eqType) := EqMixin (@star_eqP T).
Canonical star_eqType (T : eqType) := EqType (star T) (star_eqMixin T).

(**
Star型のboolの等式について、反射律と対称律が成立することを証明ておきます。
リフレクションを使用してPropの等式に変換することで、簡単に証明できます。

この補題はあとで使用します。
 *)

Lemma refl_eqStar (T : eqType) (x : star T) : (x == x).
Proof.
  by apply/eqP.
Qed.

Lemma symm_eqStar (T : eqType) (x y : star T) : (x == y) = (y == x).
Proof.
  by apply/idP/idP; move/eqP=> H; rewrite H.
Qed.


(**
# 埋め込み

以降では、string型を要素（アトム）にもつS式だけを考えるので、その型を定義します。
*)

Definition star_exp := star atomic.

(**
S式を論理式(Prop)に埋め込めるようにします。このとき、Lispの真偽の定義から、

「真」 iff 「'NILでないS式」

としなければいけません。
実際には、S式からbooleanの等式 (x != 'NIL) へのコアーションを定義します。
これは、一旦boolを経由することで、論理式(Prop)の否定も扱えるようにするためです。
*)
             
Coercion is_not_nil (x : star_exp) : bool := x != (S_ATOM (ATOM_SYM "NIL")).

(**
さらに、S式の文脈で自然数とシンボルを直接書けるようにします。
次のコアーションで、S式のなかで、S_ATOM "ABC" の S_ATOM を省けるようになります。

これは、Lispの評価規則として正しくないかもしれませんが、
eval-quote式のLispの評価規則を実装することはTLPの範囲外と考え、
ここでは、書きやすさを優先することにします。

Set Printing Coercions.
を使うと、コアーションがどのように使われているか分かります。
*)

Coercion n_quote (n : nat) : star_exp := S_ATOM (ATOM_NAT n).
Coercion s_quote (s : string) : star_exp := S_ATOM (ATOM_SYM s).


Check "T" : star_exp.
Check "T" : bool.
Check "T" : Prop.

Check 1 : star_exp.
Check 1 : bool.
Check 1 : Prop.

(**
アトムとの相互変換をする関数を用意します。
 *)

Definition s2n (x : star_exp) : nat :=
  match x with
  | S_ATOM (ATOM_NAT n) => n
  | _ => 0
  end.

Definition s2s (x : star_exp) : string :=
  match x with
  | S_ATOM (ATOM_SYM s) => s
  | _ => ""
  end.


(**
# 組込関数の定義
*)

Definition CONS (x y : star_exp) : star_exp := S_CONS x y.

Definition CAR (x : star_exp) : star_exp :=
  match x with
  | S_ATOM _ => "NIL"
  | S_CONS x _ => x
  end.

Definition CDR (x : star_exp) : star_exp :=
  match x with
  | S_ATOM _ => "NIL"
  | S_CONS _ y => y
  end.

Definition ATOM (x : star_exp) : star_exp :=
  match x with
  | S_ATOM _ => "T"
  | S_CONS _ _ => "NIL"
  end.

(**
IFとEQUALは、booleanの等式で判定します。
 *)

Definition If (q a e : star_exp) : star_exp :=
  if q == s_quote "NIL" then e else a.

Definition EQUAL (x y : star_exp) : star_exp :=
  if x == y then "T" else "NIL".

Fixpoint s_size (x : star_exp) : nat :=
  match x with
  | S_CONS a b => s_size a + s_size b + 1
  | _ => 0
  end.

Definition SIZE (x : star_exp) : star_exp := s_size x.
Eval compute in SIZE (CONS "T" (CONS "T" "T")). (* = S_ATOM (ATOM_NAT 2) *)

Definition LT (x y : star_exp) : star_exp :=
  if s2n x < s2n y then "T" else "NIL".
Eval compute in LT 2 3.                     (* = S_ATOM (ATOM_SYM "T") *)

Definition PLUS (x y : star_exp) : star_exp := s2n x + s2n y.
Eval compute in PLUS 2 3.                   (* = S_ATOM (ATOM_NAT 5) *)

(**
# 補題

のちの証明で便利なように、'NILに関する補題を証明しておきます。


``_ != _`` は ``~~(_ == _)`` の略記なので、次はis_not_nil と同じことです。
が、忘れがちなので定義しておきます。
 *)

Lemma not_nil_E q : ~~ (q == "NIL") = q.
Proof.
  done.
Qed.

(**
二重否定を解消するための補題です。
*)

Lemma not_not_nil__nil_E (q : star_exp) :
  ~~ (q != s_quote "NIL") = (q == s_quote "NIL"). (* ここはコアーションが機能しない。 *)
Proof.
  by case: eqP.
Qed.

Lemma not_q__q_nil_E (q : star_exp) : ~q <-> q = "NIL".
Proof.
  split.
  - rewrite /is_not_nil => /negP H.
    apply/eqP.
    by rewrite -not_not_nil__nil_E.
  - by move=> Hq; rewrite Hq.
Qed.

Lemma q__q_not_nil_E (q : star_exp) : q <-> q <> "NIL".
Proof.
  rewrite /is_not_nil.
  split.
  - move=> H. by apply/eqP.
  - by move/eqP.
Qed.

(**
# タクティク
 *)

(**
## prove_nil

ゴールおよび前提の NIL に関する命題を q=NIL または q<>NIL に変換するものです。
前提とゴールが同じでなくても、
前提に q=NILとq<>NILの両方があるなら、矛盾からdoneで証明が終わることができます。

なお、~~(q==NIL) は q!=NIL と同じなので、条件としてあらわれません。
 *)

Ltac prove_nil :=
  repeat match goal with
         | [ H : is_true (?q != "NIL")     |- _ ] => move/eqP            in H
         | [ H : is_true (is_not_nil ?q)   |- _ ] => move/q__q_not_nil_E in H

         | [ H : is_true (?q == "NIL")     |- _ ] => move/eqP            in H
         | [ H : ~ is_true (is_not_nil ?q) |- _ ] => move/not_q__q_nil_E in H

         | [ |- is_true (?q != "NIL")           ] => apply/eqP
         | [ |- is_true (is_not_nil ?q)         ] => apply/q__q_not_nil_E

         | [ |- is_true (?q == "NIL")           ] => apply/eqP
         | [ |- ~ is_true (is_not_nil ?q)       ] => apply/not_q__q_nil_E

         end.

(**
# IFとEQUALの補題

TLPの定理は、(EQUAL X Y) または (IF Q 'T (EQUAL X Y)) または (IF Q (EQUAL X Y) 'T)
のかたちをしているので、
それをCoqの等式と同値であることを証明しておきます。
これらは、TLPの定理の証明や、その定理を使うときに使用します。
 *)

Lemma equal_eq {x y : star_exp} : (EQUAL x y) -> x = y.
Proof.
  rewrite /EQUAL.
    by case: eqP.
Qed.

Lemma ifAP {q x y : star_exp} : (If q (EQUAL x y) "T") <-> (q -> x = y).
Proof.
  split.
  - rewrite /If /EQUAL.
    case: eqP => Hq_nil.
    + move=> _ Hq.
      by prove_nil.
    + by case: eqP.
      
  - move=> H.
    rewrite /If; case: eqP => // Hnot_nil_q.   (* q <> NIL *)
    rewrite /EQUAL; case: ifP => // => Hx_ne_y. (* x <> y) *)
    exfalso.
    
    apply negbT in Hx_ne_y.
    move/negP in Hx_ne_y.
    apply: Hx_ne_y.
    apply/eqP.
    apply: H.
      by prove_nil.
Qed.

Lemma ifEP {q x y : star_exp} : (If q "T" (EQUAL x y)) <-> (~q -> x = y).
Proof.
  split.
  - rewrite /If /EQUAL.
    case: eqP => Hq_nil.
    + by case: eqP.
    + move=> _ Hnq.
      by prove_nil.
    
  - move=> H.
    rewrite /If; case: eqP => // Hq_nil.        (* q = NIL  *)
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

ここまでに用意した道具を使って、証明をおこないます。
*)

Theorem equal_same (x : star_exp) :
  (EQUAL x x).
Proof.
  rewrite /EQUAL.
    by rewrite refl_eqStar.
Qed.

Theorem atom_cons (x y : star_exp) :
  (EQUAL (ATOM (CONS x y)) "NIL").
Proof.
  done.
Qed.

Theorem car_cons (x y : star_exp) :
  (EQUAL (CAR (CONS x y)) x).
Proof.
  rewrite /EQUAL.
  by case: eqP.
Qed.

Theorem cdr_cons (x y : star_exp) :
  (EQUAL (CDR (CONS x y)) y).
Proof.
  rewrite /EQUAL.
  by case: eqP.
Qed.

Theorem equal_swap (x y : star_exp) :
  (EQUAL (EQUAL x y) (EQUAL y x)).
Proof.
  rewrite {2}/EQUAL {2}/EQUAL.
  rewrite {1}symm_eqStar.
    by rewrite equal_same.
Qed.

Theorem equal_if (x y : star_exp) :
  (If (EQUAL x y) (EQUAL x y) "T").
Proof.
    by rewrite /If; case: eqP; move/eqP.
Qed.

Theorem if_true (x y : star_exp) :
  (EQUAL (If "T" x y) x).
Proof.
    by rewrite /EQUAL; case: eqP.
Qed.

Theorem if_false (x y : star_exp) :
  (EQUAL (If "NIL" x y) y).
Proof.
    by rewrite /EQUAL; case: eqP.
Qed.

Lemma l_if_same (x y : star_exp) :
  (If x y y) = y.
Proof.
  case: x.
  - case.
    + done.                                 (* NAT *)
    + rewrite /If => s.
      by case: eqP.                         (* SYM *)
  - done.                                   (* CONS *)
Qed.

Theorem if_same (x y : star_exp) :
  (EQUAL (If x y y) y).
Proof.
  rewrite l_if_same.
    by rewrite equal_same.
Qed.

Theorem if_nest_A (x y z : star_exp) :
  (If x (EQUAL (If x y z) y) "T").
Proof.
  rewrite /If; case: eqP => //.
  by rewrite equal_same.
Qed.

Theorem if_nest_E (x y z : star_exp) :
  (If x "T" (EQUAL (If x y z) z)).
Proof.
  rewrite /If; case: eqP => //.
  by rewrite equal_same.
Qed.

Lemma l_cons_car_cdr (x : star_exp) :
  (ATOM x) = "NIL" -> (CONS (CAR x) (CDR x)) = x.
Proof.
  move=> Hn.
  case Hc: x; rewrite /CONS => //.
  by rewrite Hc in Hn.                      (* 前提の矛盾 *)
Qed.

Theorem cons_car_cdr (x : star_exp) :
  (If (ATOM x) "T" (EQUAL (CONS (CAR x) (CDR x)) x)).
Proof.
  rewrite /If; case: eqP => Hq //.
  rewrite l_cons_car_cdr //.
  by rewrite equal_same.
Qed.

Lemma l_size_car (x : star_exp) :
  ATOM x = "NIL" -> s_size (CAR x) < s_size x.
Proof.
  elim: x.
  - by move=> a Hc //.
  - move=> x Hx y Hy Hc /=.
    (* s_size x < s_size x + s_size y + 1 *)
    by rewrite addn1 ltnS leq_addr.
Qed.

Lemma l_size_cdr (x : star_exp) :
  ATOM x = "NIL" -> s_size (CDR x) < s_size x.
Proof.
  elim: x.
  - by move=> a Hc //.
  - move=> x Hx y Hy Hc /=.
    (* s_size y < s_size x + s_size y + 1 *)
    rewrite [s_size x + s_size y]addnC.
    by rewrite addn1 ltnS leq_addr.
Qed.

Theorem size_car (x : star_exp) :
  (If (ATOM x) "T" (EQUAL (LT (SIZE (CAR x)) (SIZE x)) "T")).
Proof.
  apply/ifEP => Hq.
  rewrite /LT /= l_size_car.
  - by [].
  - by apply/not_q__q_nil_E.
Qed.

Theorem size_cdr (x : star_exp) :
  (If (ATOM x) "T" (EQUAL (LT (SIZE (CDR x)) (SIZE x)) "T")).
Proof.
  apply/ifEP => Hq.
  rewrite /LT /= l_size_cdr.
  - by [].
  - by apply/not_q__q_nil_E.
Qed.

(**
# 「公理」を書換規則として使う

TLPでは、以上の「公理」を問題プログラムの 書換 に使用します。
Coqの場合、書換 は、X = Y または Q -> (X = Y) のかたちでなければなりません。
後者の場合、書換えにともなって、新しいゴールとしてQが追加されます。

## 「公理」の書換への変換

EQUALのかたちをした「公理」を等式に変換するには、equal_eq を使います。
 *)
Section TLP_REWRITE_CHECK.
  
  Variables q x y : star_exp.

  Section TLP_REWRITE_CHECK_0.
    
    Variable e : (EQUAL x y).
    Check equal_eq e : x = y.
  End TLP_REWRITE_CHECK_0.

(**
If式かたちをした「公理」を等式に変換するには、
(iffLR ifAP) または (iffLR ifEP) を使います。
 *)
  Section TLP_REWRITE_CHECK_1.
    (** (If Q (EQUAL X Y) "T") の場合。 *)
    
    Variable ifa : (If q (EQUAL x y) "T").
    Check iffLR ifAP ifa : q -> x = y.
    
  End TLP_REWRITE_CHECK_1.
  
  Section TLP_REWRITE_CHECK_2.
    (** (If Q "T" (EQUAL X Y)) の場合。 *)
    
    Variable ife : (If q "T" (EQUAL x y)).
    Check iffLR ifEP ife : ~ q -> x = y.
    
  End TLP_REWRITE_CHECK_2.
End TLP_REWRITE_CHECK.
  
(**
## 書換の例
 *)
Section TLP_REWRITE_SAMPLE.
  
  Variables x y z : star_exp.
  
  Check equal_eq (equal_same x)      : x = x.
  Check iffLR ifAP (if_nest_A x y z) : x -> (If x y z) = y.
  Check iffLR ifEP (size_cdr x)      : ~ ATOM x -> (LT (SIZE (CDR x)) (SIZE x)) = "T".
  
End TLP_REWRITE_SAMPLE.

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
