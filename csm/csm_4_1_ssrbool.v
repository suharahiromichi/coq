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

Lemma is_true_true : true = true. Proof. done. Qed.
Check is_true_true : true.
Check isT : true.                           (* 短縮名 *)

Lemma not_false_is_true : ~ (false = true). Proof. done. Qed.
Check not_false_is_true : ~ false.
Lemma not_false_is_true' : false <> true. Proof. done. Qed.
Check not_false_is_true' : ~ false.
Check notF : ~ false.                       (* 短縮名 *)

(**
## 否定補題 -- negbT など。

b = false と ~~ b は同値のはずですが、自明でないので補題が用意されています。
~~ b = false と b は同値のはずですが、自明でないので補題が用意されています。
*)
Check negbT  : forall b : bool, b = false -> (~~ b) = true.
Check negbTE : forall b : bool, (~~ b) = true -> b = false.
Check negbF  : forall b : bool, b = true -> ~~ b = false.
Check negbFE : forall b : bool, ~~ b = false -> b = true.

(**
~~ は involutive (対合、2回適用すると元に戻る) が成立します。二重否定除去ですね。
~~ は injective (単射) です。
 *)
Check negbK : forall b : bool, ~~ ~~ b = b. (* involutive negb *)
Check negb_inj : forall b c, ~~ b = ~~ c -> b = c. (* injective negb *)

(**
二重否定除去が成り立つので、4種類の対偶もすべて成立します。
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

以下も参照してください；
SSReflectのViewとView Hintについてのメモ
https://qiita.com/suharahiromichi/items/02c7f42809f2d20ba11a
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

Print is_left. (* fun (A B : Prop) (u : {A} + {B}) => if u then true else false *)

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
命題 P が classically という条件を満たすことと、
二重否定除去が成り立つことは同値だということです。
*)

Print classically. (* fun P : Type => forall b : bool, (P -> b) -> b *)
Check classicP : forall P : Prop, classically P <-> ~ ~ P.

(* eqTypeの成り立つ型どうしの等式については、上記の条件を満たすので、
二重否定除去が成立することを証明することができます。
等式自体はProp型であるこに注意してください。
*)

Lemma classic_eq {eT : eqType} (m n : eT) : classically (m = n) -> m = n.
Proof. move=> Hc. apply/eqP/Hc. by move/eqP. Qed.

Lemma ssr_nnpp : forall (m n : nat), ~ ~ m = n -> m = n. (* 二重否定除去 *)
Proof. move=> m n Hnn. apply: classic_eq. by apply/classicP. Qed.  

(* classically の成り立つ条件を一般化する。 *)
(* 命題 P をリフレクトできる ブール式 b があれば、classically P は成り立つ。 *)
Lemma classic_p (P : Prop) (b : bool) : reflect P b -> classically P -> P.
Proof.
  move=> Hr Hc.
  apply/Hr.
  apply: Hc.
  move/Hr.
  done.
Qed.

(* 命題 P をリフレクトできる ブール式 b があれば、二重否定除去は成り立つ。 *)
Lemma nnpp_p (P : Prop) (b : bool) : reflect P b -> ~ ~ P -> P.
Proof.
  move=> Hr Hnn.
  apply: classic_p.
  - by apply: Hr.
  - by apply/classicP.
Qed.

(* 命題 P をリフレクトできる ブール式 b があれば、排中律は成り立つ。 *)
Lemma exmid_p (P : Prop) (b : bool) : reflect P b -> P \/ ~ P.
Proof.
  move=> Href.
  move: (Href).
  case/(iffP idP) => H.
  - by apply/Href.
  - by left.
  - by right.
Qed.

(**
以下も参照してください：
https://github.com/suharahiromichi/coq/blob/master/pearl/ssr_axiom_free.v

これは、古典論理の命題相互の証明であり、MathComp とは直接関係ありません：
https://github.com/suharahiromichi/coq/blob/master/ssr/ssr_classical_logic.v
*)


(**
## リストスタイル記法 list-style notations 

右結合であること。
*)

Goal forall x y z, [&& x, y & z] = x && (y && z).
Proof. done. Qed.

(* 最後のひとつの & は、カンマと同じ意味です。 *)
Goal forall x y z t, [&& x, y, z & t] = x && (y && (z && t)).
Proof. done. Qed.

(* 途中に && を挿入できることに注意してください。 *)
Goal forall x y z t, [&& x, y && z & t] = x && ((y && z) && t).
Proof. done. Qed.

(* 最後のひとつの | は、カンマと同じ意味です。 *)
Goal forall x y z t, [|| x, y, z | t] = x || (y || (z || t)).
Proof. done. Qed.


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

(* and の例 *)
(**
# これだけは憶えておきたい補題

以下も参照してください；
https://staff.aist.go.jp/reynald.affeldt/ssrcoq/ssrbool_doc.pdf
*)

Section Lemmas.
Variables a b c d : bool.

Check andTb b : true && b = b.          (* left_id true andb *)
Check andbT b : b && true = b.          (* right_id true andb *)
Check andFb b : false && b = false.     (* left_zero false andb *)
Check andbF b : b && false = false.     (* right_zero false andb *)
Check andbb b : b && b = b.             (* idempotent andb *)

Check andbC a b : a && b = b && a.      (* commutative andb *)
Check andbA a b c : a && (b && c) = a && b && c. (* associative andb *)
Check andbCA a b c : a && (b && c) = b && (a && c). (* left_commutative andb *)
Check andbAC a b c : a && b && c = a && c && b. (* right_commutative andb *)
Check andbACA a b c d : [&& a && b, c & d] = [&& a && c, b & d]. (* interchange andb andb *)
Check andbACA a b c d : a && b && (c && d) = a && c && (b && d). (* interchange andb andb *)  
Check andbN b :  b && ~~ b = false.
Check andNb b :  ~~ b && b = false.
Check andbK a b : a && b || a = a.
Check andKb a b : a || b && a = a.

(* or の例 *)
Check orTb b : true || b.                   (* = true *)
Check orbT b : b || true.                   (* = true *)
Check orFb b : false || b = b.              (* left_id false orb *)
Check orbF b : b || false = b.              (* right_id false orb *)
Check orbb b : b || b = b.                  (* idempotent orb *)
Check orbC a b : a || b = b || a.           (* commutative orb *)
Check orbA a b c : a || (b || c) = a || b || c. (* associative orb *)
Check orbCA a b c : a || (b || c) = b || (a || c). (* left_commutative orb *)
Check orbAC a b c : a || b || c = a || c || b. (* right_commutative orb *)
Check orbACA a b c d : [|| a || b, c | d] = [|| a || c, b | d]. (* interchange orb orb *)
Check orbACA a b c d : a || b || ( c || d) = (a || c) || (b || d). (* interchange orb orb *)
Check orbN b :  b || ~~ b.                  (* = true *)
Check orNb b :  ~~ b || b.                  (* = true *)
Check orbK a b : (a || b) && a = a.
Check orKb a b : a && (b || a) = a.

(* 分配則 *)
(* && と || *)
Check andb_orl a b c : (a || b) && c = a && c || b && c. (* left_distributive andb orb *)
Check andb_orr a b c : a && (b || c) = a && b || a && c. (* right_distributive andb orb *)
Check orb_andl a b c : a && b || c = (a || c) && (b || c). (* left_distributive orb andb *)
Check orb_andr a b c : a || b && c = (a || b) && (a || c). (* right_distributive orb andb *)
(* && と (+) exor *)
Check andb_addl a b c : (a (+) b) && c = a && c (+) b && c. (* left_distributive andb addb *)
Check andb_addr a b c : a && (b (+) c) = a && b (+) a && c. (* right_distributive andb addb *)

(* neg の例 *)
Check @negbT b : b = false -> ~~ b.
Check @negbTE b : ~~ b -> b = false.
Check @negbF b : (b : bool) -> ~~ b = false.
Check @negbFE b : ~~ b = false -> b.
Check negbK b : ~~ ~~ b = b.       (* involutive negb. 憶えること！ *)
Check @negbNE b : ~~ ~~ b -> b.

Check @negb_inj b c : ~~ b = ~~ c -> b = c. (* injective negb *)
Check @negbLR b c : b = ~~ c -> ~~ b = c.
Check @negbRL b c : ~~ b = c -> b = ~~ c.

(* ドモルガンの定理 *)
Check negb_and a b : ~~ (a && b) = ~~ a || ~~ b.
Check negb_or  a b : ~~ (a || b) = ~~ a && ~~ b.
End Lemmas.  

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
x \in A は自動で簡約されない。明示的に rewrite inE または apply inE で簡約する。

collective述語は、predType型クラスのインスタンス型である必要があります
（mkPredType でソースコードを検索すると、定義されている場所が判る）。
*)

(**
### predType
*)

Check seq_predType.
Check forall (T : eqType) (x : T) (l : seq T), x \in l.
Goal 1 \in [:: 1].
Proof. done. Qed.

Check tuple_predType.
Check forall (T : eqType) (x : T) (l : 3.-tuple T), x \in l.
Goal 1 \in [tuple of [:: 1]].
Proof. done. Qed.

(* pair (prod型) が使えるようにする。コアーション....。 *)
Coercion pred_of_eq_pair (T : eqType) (s : T * T) : pred T := (* pred_class *)
  fun x => (s.1 == x) || (s.2 == x). (* xpredU (eq_op s.1) (eq_op s.2). *)

Compute pred_of_eq_pair (1, 2) 1.           (* true *)

Canonical pair_predType (T : eqType) := mkPredType (@pred_of_eq_pair T).
(* Canonical pair_predType (T : eqType) := @mkPredType T (T * T) (@pred_of_eq_pair T). *)

Check forall (T : eqType) (x : T) (l : pair_predType T) , x \in l.

Goal 1 \in (1, 2).
Proof. done. Qed.

(**
### predArgType
*)

(* 型が書けるようにする。 *)
Inductive ball' : Type := red' | white'.   (* : Type は省略できる。 *)
Goal red' \in {: ball'}.                (* 任意の型を {:_} で囲む。 *)
Proof. rewrite inE. done. Qed.

(* predArgType を指定したほうがよい。finType で濃度が定義されるため（後述）。 *)
Inductive ball : predArgType := red | white. (* predArgType 型 *)
Goal red \in ball.
Proof. rewrite inE. done. Qed.

(* おまけ *)
Check nat_eqType : predPredType nat.
Goal 1 \in nat_eqType.
Proof. rewrite inE. done. Qed.
Goal 1 \in {: nat}.
Proof. rewrite inE. done. Qed.

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
  rewrite /eq_mem.
  (* forall x, (x \in (a, b)) = (x \in (b, a)) *)
  move=> x.                   (* 1階の述語の比較なので intro する。 *)
  rewrite -!topredE /=.
  Set Printing All.
  rewrite /pred_of_eq_pair /=.
  Unset Printing All.
    by rewrite orbC.
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
