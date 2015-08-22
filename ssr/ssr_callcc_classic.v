(**
call/ccと古典論理
======
2015/08/22

@suharahiromichi

# はじめに

継続と二重否定や排中律の関係は、
「カリー・ハワード同型は古典論理でも成立する」とか、
「継続があれば、直観論理を古典論理に拡張できる」とか、
「継続と二重否定が等価だった」とか、
いろいろロマンチックに語られることが多いけれど、
実は ``call/cc`` の型（p型を返すとする）、
``((p→void)→p)→p`` が、Curry-Howard同型から、
``forall P, ((P -> False) -> P) -> P)`` という論理式にみなせる、
ということに過ぎない（からだとおもう）。

それがどうして古典論理と関係するかというと、
この論理式から排中律や二重否定除去定理を証明できるからである。

ここでは、実際にその証明をしてみたい。

証明はSSReflectを使うが、あまり省略しないようにした。
*)

Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq.
Set Implicit Arguments.
Unset Strict Implicit.

(**
``call/cc``から排中律を証明する。
 *)
Goal (forall (P : Prop), ((P -> False) -> P) -> P) ->
forall (P : Prop), P \/ ~P.
Proof.
  move=> Callcc P.
  apply: (Callcc (P \/ ~P)).
  move=> H.
  right=> H1.
  apply: H.
  left.
  apply: H1.
Qed.  

(**
``call/cc``から二重否定除去を証明する。
 *)
Goal (forall (P : Prop), ((P -> False) -> P) -> P) ->
forall (P : Prop), ~ ~ P -> P.
Proof.
  move=> Callcc P.
  apply: Callcc => H1 H2.
  exfalso.
  apply: H2 => HP.
  apply: H1 => H3.
  apply: HP.
Qed.

(**
二重否定除去からcall/cc
 *)
Goal (forall (P : Prop), ~ ~ P -> P) ->
(forall (P : Prop), ((P -> False) -> P) -> P).
Proof.
  move=> Pe P H1.
  apply: (Pe P) => HnP.
  apply HnP.
  apply H1 => HP.
  apply HnP.
  apply HP.
Qed.

(**
``call/cc``からパースの論理式を証明する。
 *)
Goal (forall (P : Prop), ((P -> False) -> P) -> P) ->
forall (P Q : Prop), ((P -> Q) -> P) -> P.
Proof.
  move=> Callcc P Q H1.
  apply: Callcc => H2.
  apply: H1 => HP.
  exfalso.
  apply: H2.
  apply: HP.
Qed.

(* パースの論理式からcall/cc *)
Goal (forall (P Q : Prop), ((P -> Q) -> P) -> P) ->
forall (P : Prop) , ((P -> False) -> P) -> P.
Proof.
  move=> Pe P.
  apply (Pe P False).
Qed.

(* END *)
