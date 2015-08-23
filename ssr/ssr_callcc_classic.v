(**
call/ccと古典論理
======
2015/08/22

@suharahiromichi

# はじめに

継続は古典論理との意味をもって語られることが多いけれど、
実は ``call/cc`` の型（p型を返すとする）、
``((p→void)→p)→p`` が、Curry-Howard同型から、
``forall P, ((P -> False) -> P) -> P)`` という論理式にみなせる、
ということだ（からだとおもう）。

それがどうして古典論理と関係するかというと、
この論理式と排中律や二重否定除去定理が同値だからである。

ここでは、実際にその証明をしてみたい。

証明はSSReflectを使うが、あまり省略しないようにした。
*)

Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq.
Set Implicit Arguments.
Unset Strict Implicit.

(**
``call/cc``と排中律が同値であるこを証明する。
 *)
Goal (forall (P : Prop), ((P -> False) -> P) -> P) <->
(forall (P : Prop), P \/ ~P).
Proof.
  split.
  - move=> Callcc P.
    apply: (Callcc (P \/ ~P)).
    move=> H.
    right=> H1.
    apply: H.
    left.
    by apply: H1.
  - move=> Em P.
    case: (Em P)=> HP H1.
    + by apply: HP.
    + apply: H1.
      by apply: HP.
Qed.  

(**
``call/cc``と二重否定除去が同値であることを証明する。
 *)
Goal (forall (P : Prop), ((P -> False) -> P) -> P) <->
(forall (P : Prop), ~ ~ P -> P).
Proof.
  split.
  - move=> Callcc P.
    apply: Callcc => H1 H2.
    exfalso.
    apply: H2 => HP.
    apply: H1 => H3.
    by apply: HP.
  - move=> Dn P H1.
    apply: (Dn P) => HnP.
    apply HnP.
    apply H1 => HP.
    apply HnP.
    by apply HP.
Qed.

(**
``call/cc``とパースの論理式が同値であるこを証明する。
 *)
Goal (forall (P : Prop), ((P -> False) -> P) -> P) <->
(forall (P Q : Prop), ((P -> Q) -> P) -> P).
Proof.
  split.
  - move=> Callcc P Q H1.
    apply: Callcc => H2.
    apply: H1 => HP.
    exfalso.
    apply: H2.
    by apply: HP.
  - move=> Pe P.
    by apply (Pe P False).
Qed.

(* END *)
