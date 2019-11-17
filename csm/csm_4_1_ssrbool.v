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

reflect P b を証明するための補題が証明されています。
*)

Check introP : forall (Q : Prop) (b : bool), (b -> Q) -> (~~ b -> ~ Q) -> reflect Q b.
Check iffP   : forall (P Q : Prop) (b : bool),
       reflect P b -> (P -> Q) -> (Q -> P) -> reflect Q b.
Check appP   : forall (P Q : Prop) (b : bool), reflect P b -> reflect Q b -> P -> Q.
Check sameP  : forall (P : Prop) (b c : bool), reflect P b -> reflect P c -> b = c.

(**
## decidable  と リフレクション補題 -- sumboolP

以下も参照してください；
https://github.com/suharahiromichi/coq/blob/master/ssr/ssr_mockbird_2.v
*)

Print decidable.                   (* = fun P : Prop => {P} + {~ P} *)
Check sumboolP : forall (Q : Prop) (decQ : decidable Q), reflect Q decQ.

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
*)


(**
## ブール述語 \in 
*)

(**
## ブール述語 部分集合 
*)



(**
# 二項関係 
*)

(**
## 対称律、同値関係 
*)

(**
# 補足：boolからnatへのコアーション
 *)

Compute (true : nat) + 2.                   (* 3 *)

Compute sumn [seq (m < 10) : nat | m <- [:: 0; 3; 20]]. (* 2 *)

(* END *)
