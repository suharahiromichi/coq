(**
MathComp になぜ公理がないか。
======
2019/08/14


この文書のソースコードは以下にあります。


https://github.com/suharahiromichi/coq/blob/master/pearl/ssr_axiom_free.v

 *)

(**
OCaml 4.07.1, Coq 8.9.0, MathComp 1.9.0
 *)

From mathcomp Require Import all_ssreflect.

(**
----------------
# MathComp は排中律を仮定しているのか

Stackoverflow (英語版）に、このような質問がありました([1.])。

``forall A: Prop, A \/ ~A``

の証明を教えてほしいとう趣旨でクローズしているようなのですが、
その回答にあるように、MathComp のライブラリには排中律の公理が定義されていないので、
任意の ``A : Prop`` については証明できません。

もちろん、排中律を自分で定義するか、Standard CoqのClassical.vを導入すれば解けます。

MathComp のライブラリには公理、すなわち、証明なしで導入される
命題はひとつも含まれていません。このことは [2.] の3.3節に説明があって、

The Mathematical Components library is axiom free. This makes the
library compatible with any combination of axioms that is known to be
consistent with the Calculus of Inductive Constructions.

要するに（Standard Coqと違って）、
CICとの互換性が保たれない（かもしれない）命題は一切入れないのだ、
ということのようです。

では、排中律ががなくて困ることはないのでしょうか？
代わりの仕組みがあるのでしょうか？
そもそも、Standard Coqはどんな「公理」を導入していて、
MathComp はそれぞれをどうしているのでしょうか？

結論からいうと、命題をbool値の式に変換（リフレクト）して、
決定性のあるbool値の上では、古典論理に基づいた証明ができるからなのですが、
そのような、「MathComp」の考え方を調べてみましょう。
 *)

(** ----------------
# 古典論理

Standard Coq では Classical.v で次のように定義されています。
排中律(classic)が公理として定義され、それから二重否定除去(NNPP)が証明されています。

（補足）今回は、排中律から二重否定除去を導くことについては説明しません。
興味のあるかたは [3.] を参照してください（補足終わり）。
 *)
Require Import Classical.
Check classic : forall P : Prop, P \/ ~ P.  (* Axiom *)
Check NNPP : forall p : Prop, ~ ~ p -> p.   (* Lemma *)

(**
これに対して、MathComp では ssrbool.v で次の補題が証明されています。
*)
Check classicP : forall P : Prop, classically P <-> ~ ~ P. (* Lemma *)
Check classic_EM : forall P : Prop, classically (decidable P). (* Lemma *)

(** ----------------
## 二重否定除去
*)

(**
classicP は、``classically P`` の成り立つ P について二重否定除去が成り立つということです。

``classically := fun P : Type => forall b : bool, (P -> b) -> b``

ここで仮に P を Prop型の等式 ``P : m = n`` に限って考えるとしましょう。

そして m と n が eqType型の型であるとして、
``b : m == n`` とおくと、次の補題が成り立ちます。
*)

Lemma classic_eq {eT : eqType} (m n : eT) : classically (m = n) -> m = n.
Proof.
  move=> Hc.
    by case: (Hc (m == n)); move/eqP.
Qed.

(**
classicP と この補題を使うと、``m = n`` について二重否定除去が証明できます。
当然、m と n はeqType型の型（たとえば nat_eqType で nat）である必要があります。
  *)

Lemma ssr_nnpp : forall (m n : nat), ~ m <> n -> m = n.
Proof.
  move=> m n Hnn.
  apply: classic_eq.
  by apply/classicP.
Qed.  

(**
Standard Coq のライブラリを使う場合は、NNPPを使って証明できます。
*)
Lemma coq_nnpp : forall (m n : nat), ~ m <> n -> m = n.
Proof.
  move=> m n Hnn.
  by apply: NNPP.
Qed.


(** ----------------
## 排中律
*)

(**
classic_EM は、``decidable := fun P : Prop => {P} + {~ P}`` は、
classically が成り立つということです。

ここで P を Prop型の等式 ``P : m = n`` に限って考え、
そして m と n が eqType型の型であるとすると、decidable は成立します。
そのため、eqType型の型の等式については、classic_EM を使用せずに、排中律を証明できます。
*)

Check classic_EM : forall P : Prop, classically ({P} + {~ P}). (* Lemma *)
Check classic_EM : forall P : Prop, classically (decidable P). (* Lemma *)

Check sumboolP : forall (Q : Prop) (decQ : decidable Q), reflect Q decQ.
Check decP : forall (P : Prop) (b : bool), reflect P b -> decidable P.

Lemma dec_eq (m n : nat) : decidable (m = n).
Proof.
  apply: (@decP (m = n) (m == n)).
  apply: (iffP idP); by move/eqP.
Qed.

Lemma ssr_EM (m n : nat) : m = n \/ m <> n.
Proof.
    by case: (dec_eq m n); by [left | right].
Qed.


(**
Standard Coq のライブラリを使う場合は、classicを使って証明できます。
*)
Lemma coq_EM (m n : nat) : m = n \/ m <> n.
Proof.
  by apply: classic.
Qed.


(**
-------
# 関数拡張 (functional_extensionality)

Standard Coq では FunctionalExtensionality.v で定義されています。
 *)

Require Import FunctionalExtensionality.
Check @functional_extensionality_dep        (* Axiom *)
  : forall (A : Type) (B : A -> Type) (f g : forall x : A, B x),
    (forall x : A, f x = g x) -> f = g.
Check @functional_extensionality            (* Lemma *)
  : forall (A B : Type) (f g : A -> B), (forall x : A, f x = g x) -> f = g.

(**
これに対して、MathComp では finfun.v で次の補題が証明されています。
*)

Check ffunP : forall (aT : finType) (rT : aT -> Type) (* lemma *)
                     (f1 f2 : {ffun forall x : aT, rT x}),
    (forall x : aT, f1 x = f2 x) <-> f1 = f2.


(**
--------
# (proof irrelevance)

Standard Coq では ProofIrrelevance.v でで定義されています。

*)
Require Import ProofIrrelevance.
Check proof_irrelevance                     (* Axiom *)
  : forall (P : Prop) (p1 p2 : P), p1 = p2.

(**
これに対して、MathComp では eqtype.v と ssrnat.v で次の補題が証明されています。
*)

Check bool_irrelevance : forall (b : bool) (p1 p2 : b), p1 = p2.
Check eq_irrelevance : forall (T : eqType) (x y : T) (e1 e2 : x = y), e1 = e2.
Check le_irrelevance : forall (m n : nat) (le_mn1 le_mn2 : (m <= n)%coq_nat),
    le_mn1 = le_mn2.
Check lt_irrelevance : forall (m n : nat) (lt_mn1 lt_mn2 : (m < n)%coq_nat),
    lt_mn1 = lt_mn2.


(**
---------------
# 文献

[1.] Does ssreflect assume excluded middle?

https://stackoverflow.com/questions/34520944/does-ssreflect-assume-excluded-middle


[2.] Mathematical Components Book

https://math-comp.github.io/mcb/


[3.] Classical_Logic

https://github.com/suharahiromichi/coq/blob/master/ssr/ssr_classical_logic.v


 *)

(* END *)

