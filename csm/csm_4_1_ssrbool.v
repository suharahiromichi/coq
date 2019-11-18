(**
Coq/SSReflect/MathComp による定理証明

第4章 MathComp ライブラリの基本ファイル

4.1 ssrbool.v --- bool型のためのライブラリ

======

2018_11_17 @suharahiromichi
 *)

From mathcomp Require Import all_ssreflect.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(**
# はじめに

本節はテキストを参照しながら、MathComp のソースコードに沿って説明していきます。
ソースコードが手元にあるならば、それも参照してください。
opamでインストールしている場合は、ssrbool.v のソースは、たとえば以下にあります。

~/.opam/4.07.1/lib/coq/user-contrib/mathcomp/ssreflect/ssrbool.v   

つぎのコマンドで探すこともできます。

find ~/.opam/ -name ssrbool.v

ライブラリを使う目的から説明していきます。実装について興味のあるひとは、
以下を参照してください：
Assia Mahboubi and Enrico Tassi, Mathematical Components
https://math-comp.github.io/mcb/
*)

(**
# is_true

Coercion is_true (b : bool) : Prop := b = true

と定義されている関数です。Coercion は Definition と同じですが、
b を Prop の文脈に書いたときに（ただし、b : bool）、
is_true を補って（コアーション）、b = true と解釈されます。

このときの b をブール命題と呼ぶことがあります。
 *)
                                                  
(**
## if-then-else (ssreflect.v で定義) 

本来 if-then-else はmatchの省略形で、

if c is v then v1 else v2 は

match c with | v => v1 | _ => v2 end

の意味です。ifの条件節が c is v であることに注意してください。
しかし b : bool の場合に限り、is v を省略できます。以降このかたちを使います。

if b then v1 else v2

if b is true then v1 else v2

match b with | true => v1 | _ => v2 end

*)


(**
# bool型の論理演算 

&&      andb
||      orb
~~      negb
==>     implb
(+)     addb    (排他的論理和 exor)

&&と^^はバニラCoqで定義されています。
*)

(**
等式については eqtype.v で詳しく扱いますが、

= が Prop型の等式で、その否定は <> です。
== が bool型の等式で、その否定は != です。
*)


(**
## 自明な補題 -- is_true_true など

自明ですが「名前が欲しい」こともあるので、記憶にとどめて置おきましょう。
*)

Check is_true_true : true.
Check isT : true.                           (* 短縮名 *)

Check not_false_is_true : ~ false.
Check notF : ~ false.                       (* 短縮名 *)

(**
## 否定補題 -- negbT など。

b = false と ~~ b は同値のはずですが、自明でないので補題が用意されています。
~~ b = false と b は同値のはずですが、自明でないので補題が用意されています。
*)
Check negbT  : forall b : bool, b = false -> ~~ b.
Check negbTE : forall b : bool, ~~ b -> b = false.
Check negbF  : forall b : bool, b -> ~~ b = false.
Check negbFE : forall b : bool, ~~ b = false -> b.

(**
~~ は involutive (2回適用すると元に戻る) が成立します。二重否定除去ですね。
~~ は injective (単射) です。
 *)
Check negbK : forall b : bool, ~~ ~~ b = b. (* involutive negb *)
Check negb_inj : forall b c, ~~ b = ~~ c -> b = c. (* injective negb *)

(**
二重否定が成り立つので、4種類の対偶もすべて成立します。
 *)
Check contraNN : forall c b : bool, (c -> b) -> ~~ b -> ~~ c.
Check contraTN : forall c b : bool, (c -> ~~ b) -> b -> ~~ c.
Check contraNT : forall c b : bool, (~~ c -> b) -> ~~ b -> c.
Check contraTT : forall c b : bool, (~~ c -> ~~ b) -> b -> c.

(**
次も参照してください： MathComp の「等号問題」を解決する
https://qiita.com/suharahiromichi/items/85773d5af998ae3fe148
https://github.com/suharahiromichi/coq/blob/master/pearl/ssr_ltac_1.v
*)

(**
# reflect 

P : Prop、b : bool のとき、 reflect P b が成り立つ（注）とき、
P と b を入れ替えることができる。これをリフレクションといいます。

注：reflect P (b = true) とおなじ。
*)

(**
## 基本 

if b then P else ~ P および if b then ~ Q else Q に関する補題（略）
*)

(**
### リフレクション補題

reflect P b が成り立っていることを前提に、P と b を入れ替える補題が用意されています。
*)

Check introT  : forall (P : Prop) (b : bool), reflect P b -> P -> b.
Check introF  : forall (P : Prop) (b : bool), reflect P b -> ~ P -> b = false.
Check introN  : forall (P : Prop) (b : bool), reflect P b -> ~ P -> ~~ b.
Check introNf : forall (P : Prop) (b : bool), reflect P b -> P -> ~~ b = false.
Check introTn : forall (P : Prop) (b' : bool), reflect P (~~ b') -> ~ P -> b'.
Check introFn : forall (P : Prop) (b' : bool), reflect P (~~ b') -> P -> b' = false.

Check elimT  : forall (P : Prop) (b : bool), reflect P b -> b -> P.
Check elimF  : forall (P : Prop) (b : bool), reflect P b -> b = false -> ~ P.
Check elimN  : forall (P : Prop) (b : bool), reflect P b -> ~~ b -> ~ P.
Check elimNf : forall (P : Prop) (b : bool), reflect P b -> ~~ b = false -> P.
Check elimTn : forall (P : Prop) (b' : bool), reflect P (~~ b') -> b' -> ~ P.
Check elimFn : forall (P : Prop) (b' : bool), reflect P (~~ b') -> b' = false -> P.

(**
### view hint 

前節の補題は、View Hint に使える。
*)

(**
### リフレクション補題 -- iffP, appP, sameP など

reflect P b を証明するための補題などが証明されています。

使用例：
reflect P b の補題を証明するときは、apply: (iffP idP) を実行して、
b -> P と P -> b のふたつのゴールに変換します。
*)

Goal reflect (1 = 1) (1 == 1).
Proof.
  Check @idP : forall b1 : bool, reflect b1 b1.
  apply: (iffP idP).
  - done.                                   (* 1 == 1 -> 1 = 1 *)
  - done.                                   (* 1 = 1 -> 1 == 1 *)
Qed.

(**
apply: introP も使えます。場合によってはこちらの方がよいかもしれません。
*)
Goal reflect (1 = 1) (1 == 1).
Proof.
  apply: introP.
  - done.                                   (* 1 == 1 -> 1 = 1 *)
  - done.                                   (* 1 != 1 -> 1 <> 1 *)
Qed.


Check introP : forall (Q : Prop) (b : bool), (b -> Q) -> (~~ b -> ~ Q) -> reflect Q b.
Check iffP   : forall (P Q : Prop) (b : bool),
       reflect P b -> (P -> Q) -> (Q -> P) -> reflect Q b.
Check appP   : forall (P Q : Prop) (b : bool), reflect P b -> reflect Q b -> P -> Q.
Check sameP  : forall (P : Prop) (b c : bool), reflect P b -> reflect P c -> b = c.

(**
## decidable  と リフレクション補題 -- sumboolP

命題 P : Prop が決定可能なとき、すなわち P か ~ P のどちらかが成立するとき、
バニラCoqでは、{P} + {~ P} 成り立つといい、これをsumboolと呼びます。

reflect P b の b は bool でなければいけませんが、
sumbool から bool型へのコアーション is_left が定義されているため、
sumbool reflect P b の b のところに書くことができます。
*)

Print decidable.                   (* = fun P : Prop => {P} + {~ P} *)
Check sumboolP : forall (Q : Prop) (decQ : decidable Q), reflect Q decQ.
Check sumboolP : forall (Q : Prop) (decQ : decidable Q), reflect Q (is_left decQ).

Require Import Ascii String.
Definition string_dec : forall x y : string, decidable (x = y).
Proof.
  rewrite /decidable => x y.                (* {x = y} + {x <> y} *)
  decide equality;                          (* string に対して。 *)
    decide equality;                        (* ascii に対して。 *)
    decide equality.                        (* bool に対して。 *)
Defined.

Check          string_dec "foo"%string "bar"%string  : bool.
Check is_left (string_dec "foo"%string "bar"%string) : bool.

Definition string_eqb (x y : string) : bool := string_dec x y.
Definition string_eqP (x y : string) := sumboolP (string_dec x y).

Check string_eqb : forall x y : string, bool.
Check string_eqP : forall x y : string, reflect (x = y) (string_dec x y).

(**
以下も参照してください；
https://github.com/suharahiromichi/coq/blob/master/lisp/ssr_string.v
https://github.com/suharahiromichi/coq/blob/master/ssr/ssr_mockbird_2.v
*)

(**
## classically と リフレクション補題 -- classicP

MathComp では古典論理の公理を含んで居ません。その代わりに次の補題が証明されています。
命題 P が classically という条件を満たすことと、二重否定が成り立つことは同値だということです。
*)

Print classically. (* fun P : Type => forall b : bool, (P -> b) -> b *)
Check classicP : forall P : Prop, classically P <-> ~ ~ P.

(* eqTypeの成り立つ型どうしの等式については、上記の条件を満たすので、
二重否定除去が成立することを証明することができます。
等式自体はProp型であるこに注意してください。
*)
Lemma classic_eq {eT : eqType} (m n : eT) : classically (m = n) -> m = n.
Proof.  move=> Hc. by case: (Hc (m == n)); move/eqP. Qed.

Lemma ssr_nnpp : forall (m n : nat), ~ m <> n -> m = n.
Proof.  move=> m n Hnn. apply: classic_eq. by apply/classicP. Qed.  

(**
以下も参照してください：
pearl/ssr_axiom_free.v
ssr/ssr_classical_logic_2.v
*)


(**
## リストスタイル記法 list-style notations 

右結合であること。
*)

(**
### リフレクション補題 -- negP, andP, orP など。

apply/P または move/P のかたちで使用し、ゴールまたは前提を P と b の間で相互変換する。

使用例：
*)
Goal true || false.
Proof. apply/orP. by left. Qed.

Goal true \/ false.
Proof. apply/orP. done. Qed.

Goal true && false -> False.
Proof. move/andP. by case. Qed.

Goal true /\ false -> False.
Proof. move/andP. done. Qed.

(** 補題 *)

Check @idP   : forall b1 : bool, reflect b1 b1.
Check @boolP : forall b1 : bool, alt_spec b1 b1 b1.
Check @idPn  : forall b1 : bool, reflect (~~ b1) (~~ b1).
Check @negP  : forall b1 : bool, reflect (~ b1) (~~ b1).
Check @negPn : forall b1 : bool, reflect b1 (~~ ~~ b1).
Check @negPf : forall b1 : bool, reflect (b1 = false) (~~ b1).
Check @andP  : forall b1 b2 : bool, reflect (b1 /\ b2) (b1 && b2).
Check @and3P : forall b1 b2 b3 : bool, reflect [/\ b1, b2 & b3] [&& b1, b2 & b3].
Check @and4P
  : forall b1 b2 b3 b4 : bool, reflect [/\ b1, b2, b3 & b4] [&& b1, b2, b3 & b4].
Check @and5P
  : forall b1 b2 b3 b4 b5 : bool,
    reflect [/\ b1, b2, b3, b4 & b5] [&& b1, b2, b3, b4 & b5].
Check @orP   : forall b1 b2 : bool, reflect (b1 \/ b2) (b1 || b2).
Check @or3P  : forall b1 b2 b3 : bool, reflect [\/ b1, b2 | b3] [|| b1, b2 | b3].
Check @or4P
  : forall b1 b2 b3 b4 : bool, reflect [\/ b1, b2, b3 | b4] [|| b1, b2, b3 | b4].
Check @nandP
  : forall b1 b2 : bool, reflect (~~ b1 \/ ~~ b2) (~~ (b1 && b2)).
Check @norP  : forall b1 b2 : bool, reflect (~~ b1 /\ ~~ b2) (~~ (b1 || b2)).
Check @implyP : forall b1 b2 : bool, reflect (b1 -> b2) (b1 ==> b2).

(**
# ブール演算に関する補題 
*)

(* This file extends the lemma name suffix conventions of ssrfun as follows:  *)
(*   A -- associativity, as in andbA : associative andb.                      *)
(*  AC -- right commutativity.                                                *)
(* ACA -- self-interchange (inner commutativity), e.g.,                       *)
(*        orbACA : (a || b) || (c || d) = (a || c) || (b || d).               *)
(*   b -- a boolean argument, as in andbb : idempotent andb.                  *)
(*   C -- commutativity, as in andbC : commutative andb,                      *)
(*        or predicate complement, as in predC.                               *)
(*  CA -- left commutativity.                                                 *)
(*   D -- predicate difference, as in predD.                                  *)
(*   E -- elimination, as in negbEf : ~~ b = false -> b.                      *)
(*   F or f -- boolean false, as in andbF : b && false = false.               *)
(*   I -- left/right injectivity, as in addbI : right_injective addb,         *)
(*        or predicate intersection, as in predI.                             *)
(*   l -- a left-hand operation, as andb_orl : left_distributive andb orb.    *)
(*   N or n -- boolean negation, as in andbN : a && (~~ a) = false.           *)
(*   P -- a characteristic property, often a reflection lemma, as in          *)
(*        andP : reflect (a /\ b) (a && b).                                   *)
(*   r -- a right-hand operation, as orb_andr : rightt_distributive orb andb. *)
(*   T or t -- boolean truth, as in andbT: right_id true andb.                *)
(*   U -- predicate union, as in predU.                                       *)
(*   W -- weakening, as in in1W : {in D, forall x, P} -> forall x, P.         *)

(**
# ブール述語 

ブール述語とは pred T (= T -> bool) の型の述語のことで、[pred x : T | E] で表される。
*)

Print pred.                                 (* T -> bool *)
Check [pred n : nat | n == 2] : pred nat.
Check [pred n       | n == 2] : pred nat.

Goal [pred n | n == 2] 2.
Proof. done. Qed.

(**
## ブール述語 \in 

2項演算子のブール述語に \in がある。forall T, pred S の型を持つ。

\in の右側 (型 Sのところ) に書ける述語を collective述語といいます。
（これに対して、普通に P x の Pに書ける述語を applicatable述語といいます。）
x \in A は自動で簡約されない。明示的に apply inE または rewrite inE で簡約する。

collective述語は、predType型クラスのインスタンス型である必要があります
（mkPredType で定義する場所が判る）。

predType型のインスタンスとしては以下がある。自分で定義することもできる。
*)

Check predPredType _ : predType _.          (* ssrbool で定義 *)
Check seq_predType _ : predType _.          (* seq で定義 *)
Check tuple_predType _ _ : predType _.      (* tuple で定義 *)

(**
例として、T と S は次の組み合わせが可能である。
*)

(* T と predPredType T の組み合わせ： *)
Check forall (T : Type) (x : T) (t : predPredType T), x \in t.
Check 1 \in {: nat}.

(* T と seq T の組み合わせ： *)
Check forall (T : eqType) (x : T) (l : seq T), x \in l.
Check 1 \in [:: 1].

(* T と tuple T の組み合わせ： *)
Check forall (T : eqType) (x : T) (l : 3.-tuple T), x \in l.
Check 1 \in [tuple of [:: 1]].

(* T と T * T の組み合わせ（ができるように定義する）： *)
Coercion pred_of_eq_pair (T : eqType) (s : T * T) :
  pred_class := xpredU (eq_op s.1) (eq_op s.2).
Canonical pair_predType (T : eqType) := @mkPredType T (T * T) (@pred_of_eq_pair T).

Check forall (T : eqType) (x : T) (l : pair_predType T) , x \in l.
Check 1 \in (1, 2).

(* T と eqType の組み合わせ： *)
Check 1 \in nat_eqType.
Check forall (T : eqType) (x : T), x \in T.

(**
以下も参照してください：
ssr/ssr_collective_predicate.v
*)

(**
## ブール述語 同値と部分集合 

Collective述語の同値は「=i」で比較します（Applicatable述語の同値は「=1」です）。
1階の述語なので、なにもないところからintro xするように見えます。
*)

Goal forall (T : eqType) (a b : T), (a, b) =i (b, a).
Proof.
  move=> T a b.
  (* rewrite /eq_mem. *)
  (* forall x, (x \in (a, b)) = (x \in (b, a)) *)
  move=> x.                   (* 1階の述語の比較なので intro する。 *)
  rewrite -!topredE /=.
  Set Printing All.
  rewrite /pred_of_eq_pair /=.
  Unset Printing All.
    by rewrite Bool.orb_comm.
Qed.

(**
部分重合 subset の関係も使えます。
これも1階の述語なので、なにもないところからintro xするように見えます。
 *)

Goal forall (T : eqType) (a b : T), {subset (a, a) <= (a, b)}.
Proof.
  move=> T a b.
  (* rewrite /sub_mem. *)
  (* forall x, x \in (a, a) -> x \in (a, b) *)
  move=> x.                   (* 1階の述語の比較なので intro する。 *)
  rewrite -!topredE /=.
  Set Printing All.
  rewrite /pred_of_eq_pair /=.
  Unset Printing All.
    by case/orP => ->.
Qed.

(**
# 二項関係 

二項関係とは rel T (= T -> T -> bool) の型の述語のことで、[rel x : T | E] で表される。
*)

Check [rel m n : nat | m.+1 == n] : rel nat.
Check [rel m n       | m.+1 == n] : rel nat.

(**
## 対称律、同値関係 
*)

Definition R := [rel m n : nat | m == n].
Check symmetric.
Check equivalence_rel.

(**
# 補足：boolからnatへのコアーション
 *)

Compute (true : nat) + 2.                   (* 3 *)

Compute sumn [seq (m < 10) : nat | m <- [:: 0; 3; 20]]. (* 2 *)

(* END *)
