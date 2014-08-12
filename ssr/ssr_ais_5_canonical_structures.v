(**
An introduction to small scale reflection in Coq

5. Type inference using canonical structures

http://hal.inria.fr/docs/00/55/53/79/PDF/main-rr.pdf
*)

Require Import ssreflect ssrfun ssrbool eqtype ssrnat div seq.
Require Import path choice fintype tuple finfun finset.

Set Implicit Arguments.
(* この宣言は必須である。これによって省かれた項はコメントしてある。 *)
Unset Strict Implicit.
Import Prenex Implicits.

(**
5.1 Canonical Structures
*)

Record zmodule_mixin_of (T : Type) : Type :=
  ZmoduleMixin {
      zero : T;
      opp : T -> T;
      add : T -> T -> T;
      addA : associative add;
      addC : commutative add;
      addm0 : left_id zero add;
      add0m : left_inverse zero opp add
    }.

Record zmodule : Type :=
  Zmodule {
      carrier :> Type;
      spec : zmodule_mixin_of carrier
    }.
(** bool_zodule は少し後ろにずらした。 *)

Definition zmadd (Z : zmodule) := add (spec Z).
(* add の forall T の T （つまり、 zmodule_mixin_of (T : Type) の T)
 が省かれている。zmaddACの証明も同様。 *)

Notation "x \+ y" := (zmadd x y) (at level 50, left associativity).
(* zmadd の Zが省かれている。 *)

(** Excercise 5.1.1 *)
Lemma zmaddAC : forall (m : zmodule)(x y z : m),
                  x \+ y \+ z = x \+ z \+ y.
Proof.
  move=> m x y z.
  rewrite /zmadd.
  rewrite -[add (spec m) (add (spec m) x y) z]addA.
  rewrite [add (spec m) y z]addC.
  rewrite [add (spec m) x (add (spec m) z y)]addA.
  by [].
Qed.

(** bool_zodule *)

Definition bool_zmoduleMixin :=
  ZmoduleMixin
    (* 最初の4引数が省かれている。 *)
    (* Type:=bool zero:=false opp:=(@id bool) add:=addb *)
    addbA addbC addFb addbb.

Definition bool_zmodule := Zmodule (* bool *) bool_zmoduleMixin.
(* Zmodule の bool が省かれている。  *)
Variable b : bool_zmodule.

Canonical Structure bool_zmodule.           (* 以下が有効になる。 *)
Check false \+ true.                        (* bool_zmodule *)
Eval compute in false \+ true.              (* true *)

Goal forall x y z : bool, x (+) y (+) z = x (+) z (+) y.
Proof.
  Locate "(+)".                             (* addb *)
  apply zmaddAC.
Qed.

(**
5.2 Canonical constructions
*)

(* eqtype.v の定義が使用される。 *)
Lemma unit_eqP : Equality.axiom (fun _ _ : unit => true).
Proof.
    by do 2!case; left.
Qed.

Definition unit_eqMixin := EqMixin unit_eqP.
Canonical Structure unit_eqType := EqType unit unit_eqMixin.

(** Exercise 5.2.1 *)

(** bool *)
Definition eqb x y :=
  if x then y else ~~ y.

Lemma bool_eqP : Equality.axiom eqb.
Proof.
  move=> x y.
  apply/(@iffP (eqb x y)).
  - by apply/idP.
  - case: x=> /= Hy.
    + by [].
    + by move/negPf in Hy.
  - case: x=> /= Hy.
    + by [].
    + by apply/negPf.
Qed.

Definition bool_eqMixin := EqMixin bool_eqP.
Canonical Structure bool_eqType := EqType bool bool_eqMixin.

(** nat *)
Lemma nat_eqP : Equality.axiom (fun m n : nat => eqn m n).
Proof.
  move=> m n.
  apply/(@iffP (eqn m n)).
  - by apply/idP.
  - by apply/eqP.
  - by move/eqP.
Qed.

Definition nat_eqMixin := EqMixin nat_eqP.
Canonical Structure nat_eqType := EqType nat nat_eqMixin.

(** Exercise 5.2.2 *)

Definition pair_eq (T1 T2 : eqType) :=
  [rel u v : T1 * T2 | (u.1 == v.1) && (u.2 == v.2)].

Lemma tuto_pair_eqP : forall T1 T2, Equality.axiom (pair_eq T1 T2).
Proof.
  (* u v の場合わけして、u1 u2 v1 v2としてpopするのが味噌 *)
  move=> T1 T2 [u1 u2] [v1 v2].
  apply/(@iffP (pair_eq T1 T2 (u1, u2) (v1, v2))).
  - by apply/idP.
  - rewrite /pair_eq /=.
    case/andP.
    move/eqP => H1.
    move/eqP => H2.
    by subst.
  - rewrite /pair_eq /=.
    (* 前提 (u1,u2)=(v1,v2)を u1=v1とu2=v2にわけてpopするのが味噌 *)
    move=> [H1 H2].
    apply/andP.
    by subst.
Qed.

Definition prod_eqMixin (T1 T2 : eqType) :=
  EqMixin (@tuto_pair_eqP T1 T2).

Canonical Structure prod_eqType (T1 T2 : eqType) :=
  EqType (T1 * T2) (prod_eqMixin T1 T2).    (* 最後のT1 T2 は略せない。 *)

Check (true, 3) == (true && true, 1 + 2).   (* bool *)
Print Canonical Projections.

(**
5.3 Predtypes: canonical structures for notations
 *)
Section SeqMem.
  Variable T : eqType.
  Implicit Type s : seq T.
  Implicit Types x y : T.

  Lemma tuto_in_cons : forall y s x,
                         (x \in y :: s) = (x == y) || (x \in s).
  Proof.
      by [].
  Qed.

  (** Exercise 5.3.1 *)
  Lemma tuto_in_nil : forall x, (x \in [::]) = false.
  Proof.
    by [].
  Qed.
  
  Lemma tuto_mem_seq1 : forall x y, (x \in [:: y]) = (x == y).
  Proof.
    move=> x y.
    Locate "\in".
    rewrite /in_mem /=.
      by case: (x == y).
  Qed.
  
  Lemma tuto_mem_head : forall x s, x \in x :: s.
  Proof.
    move=> x s.
    rewrite /in_mem /=.
    apply/orP.
    by left.
  Qed.

  (** Exercise 5.3.2 *)
  Lemma tuto_mem_cat : forall x s1 s2,
                         (x \in s1 ++ s2) = (x \in s1) || (x \in s2).
  Proof.
    have orC p q r : p || q || r = p || (q || r)
      by case: p; case: q; case: r.
    move=> x s1 s2.
    rewrite /in_mem /=.
    elim: s1.
    + by [].
    + move=> a l IH /=.
      by rewrite IH. (* rewrite orC. も使われる。 *)
  Qed.

  Lemma tuto_mem_behead: forall s, {subset (behead s) <= s}.
  Proof.
    rewrite /sub_mem /in_mem /mem /=.
    elim.                                   (* by s *)
    + by [].
    + move=> a l IH /= x H.
      apply/orP.
      by right.
  Qed.    

  Lemma tuto_hasP : forall (a : pred T) s,
                      reflect (exists2 x, x \in s & a x) (has a s).
  Proof.
    

(* END *)
