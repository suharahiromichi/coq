(**
「The Little Prover」の CTX?/SUB の証明
======
2017/08/09


@suharahiromichi

- この文書のソースコードは以下にあります。


https://github.com/suharahiromichi/coq/blob/master/lisp/tlp_ctx_sub.v


- バージョン


OCaml 4.07.1, Coq 8.9.0, MathComp 1.9.0
 *)

(**
# はじめに

「The Little Prover」（以下 TLP）[1] を読んで、
Coqの上でそれを実現しようとした話です。

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


Check "T" : string.
Check "T" : star_exp.
Check "T" : bool.
Check "T" : Prop.

Check 1 : nat.
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
# TLP Chapter 7

## CTX? と SUB の定義
*)

Fixpoint ctxp (x : star_exp) : star_exp :=
  match x with
  | S_CONS x1 x2 => if (ctxp x1) then (s_quote "T") else (ctxp x2)
  | _ => if x == (s_quote "?") then "T" else "F"
  end.

Fixpoint sub (x y : star_exp) : star_exp :=
  match y with
  | S_CONS y1 y2 => S_CONS (sub x y1) (sub x y2)
  | _ => if y == (s_quote "?") then x else y
  end.

(**
## CTX?/SUB 定理の証明
*)

Lemma l_ctxp_cons (s1 s2 : star_exp) :
  (ctxp s1) || (ctxp s2) = (ctxp (S_CONS s1 s2)).
Proof.
  rewrite /=.
    by case: ifP.
Qed.

(* 不使用 *)
Lemma l_sub_cons (x s1 s2 : star_exp) :
  (sub x (S_CONS s1 s2)) = (S_CONS (sub x s1) (sub x s2)).
Proof.
  done.
Qed.

Lemma ctxp_sub (x y : star_exp) :
  (ctxp x) -> (ctxp y) -> (ctxp (sub x y)).
Proof.
  elim: y.
  - move=> t Hx Ht /=.
      by case: ifP.
  - move=> s1 IHs1 s2 IHs2 H /=.
    rewrite -l_ctxp_cons.
    move/orP.
    case.
    + move=> Hs1.
      case: ifP.
      * done.
      * move: (IHs1 H Hs1) => {IHs1} {Hs1} Hs1.
        move/negbT/negP.                    (* Hs1と矛盾する。 *)
        done.
    + move=> Hs2.
      move: (IHs2 H Hs2) => {IHs2} {Hs2} Hs2.
      case: ifP.
      * done.
      * move/negbT/negP.                    (* Hs2と矛盾する。 *)
        done.
Qed.

(**
# TLP Chapter 8
 *)

(** 線形リストとして、xを要素に含まないか。 *)
Fixpoint memberp (x ys : star_exp) : star_exp :=
  match ys with
  | S_CONS ys1 ys2 => if (x == ys1) then (s_quote "T") else (memberp x ys2)
  | _ => "NIL"
  end.

(** 線形リストとして、要素に重複がないか。集合であるか。 *)
Fixpoint setp (xs : star_exp) : star_exp :=
  match xs with
  | S_CONS xs1 xs2 => if (memberp xs1 xs2) then (s_quote "NIL") else (setp xs2)
  | _ => "T"
  end.

(** 線形リストとして、要素に重複がないなら、追加する。 *)
Definition add_atom (x ys : star_exp) : star_exp :=
  if (memberp x ys) then ys else (S_CONS x ys).

(** xの要素それぞれに対して、追加する *)
Fixpoint add_atoms (x ys : star_exp) : star_exp :=
  match x with
  | S_CONS x1 x2 => add_atoms x1 (add_atoms x2 ys)
  | _ => add_atom x ys
  end.

Definition atoms (x : star_exp) : star_exp :=
  add_atoms x "NIL".

Lemma step__step_add_atoms s1 s2 : setp s2 = setp (add_atoms s1 s2).
Proof.
  elim: s1 s2 => [s1 s2 | s1' IHs1 s2' IHs2] /=.
  - rewrite /add_atom.
    case: ifP => [| H] //=.
    case: ifP => //= Hc.
      by move/negbT/negP in H.              (* H と Hc の矛盾 *)
  - move=> s2.
    rewrite -(IHs1 (add_atoms s2' s2)).
      by rewrite IHs2.
Qed.

Theorem setp_add_atoms (a bs : star_exp) :
  (setp bs) -> (setp (add_atoms a bs)).
Proof.
  move=> H.
    by rewrite -step__step_add_atoms.
Qed.

(** atoms の結果は集合である。 *)
Theorem setp_atoms (a : star_exp) : (setp (atoms a)).
Proof.
  rewrite /atoms.
    by apply: setp_add_atoms.
Qed.

(**
# TLP Chapter 10

（これは解けないだろう）
 *)

Definition rotate (x : star_exp) : star_exp :=
  match x with
  | S_CONS (S_CONS x11 x12) x2 => (S_CONS x11 (S_CONS x12 x2))
  | _ => "NIL"
  end.

Theorem rotare_cons (x y z : star_exp) :
  (rotate (S_CONS (S_CONS x y) z)) = (S_CONS x (S_CONS y z)).
Proof.
  done.
Qed.

Require Import Program.
Require Import Recdef.

Definition Atom (x : star_exp) : star_exp :=
  match x with
  | S_ATOM _ => "T"
  | S_CONS _ _ => "NIL"
  end.

Fixpoint s_size (x : star_exp) : nat :=
  match x with
  | S_CONS a b => s_size a + s_size b + 1
  | _ => 0
  end.

Function align (x : star_exp) {measure s_size x} : star_exp :=
  match x with
  | S_CONS x1 x2 => if (Atom x1) then (S_CONS x1 (align x2)) else (align (rotate x))
  | _ => x
  end.
Proof.
  (* aling の引数の size が減っていかない。 *)
Admitted.

Fixpoint wt (x : star_exp) : star_exp :=
  match x with
  | S_CONS x1 x2 => (wt x1).*2 + (wt x2)
  | _ => 1
  end.

Theorem align_align (x : star_exp) : (align (align x)) = (align x).
Proof.
Admitted.


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
