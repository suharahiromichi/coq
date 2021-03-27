(**
Coq/SSReflect/MathComp による定理証明

6.2.1 有限群の型と補題
======

2021_03_07 @suharahiromichi
 *)

From mathcomp Require Import all_ssreflect.
From mathcomp Require Import fingroup.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(**
## 最初に

``group`` スコープにしておきます。
*)
Open Scope group_scope.

(**
## ``finGroupType`` とはなにか

テキストでは、「``fingroup`` は有限群の基本的な仮定や補題を提供します」
と記載されています。有限群は finite group のことですから、間違いではないのですが、
MathComp の型クラスとして定義されているのは、``finGroupType`` 
すなわち「有限群型」であることに注意してください。

``fingroup.v``のコメントでは、``finGroupType`` は、
"the structure for finite types with a group law" と記載されています。

有限群型とは、その要素が群の規則を満たす有限型という意味で、
``finType``型クラスを継承して、公理として乗法の結合則や単位元の存在を仮定します。
すなわち、``finType``型クラスのインスタンス型``T``を台として、以下が成り立ちます。

- 二項演算 mulg : T -> T -> T が存在する。
- 元 one : T が存在する。
- 関数 invg : T -> T が存在する。
- mulg は結合律を満たす。
- one は左単位元である。
- invg は対合である（involutive、2回適用するともとにもどる）。
```invg (invg x) = x```
- invg と mulg は逆自己同型（？）である（anti-mophism を満たす）。
```invg (mulg x y) = mulg (invg y) (invg x)```

（``anti-`` は x と y が逆になるということ）
 *)

(**
## 型インスタンスとしての「有限群型」の定義

前節の繰り返しになりますが、
型クラス``finGroupType``のインスタンス型の値は、
有限群の公理を満たすということです。
*)
Section Sect_1.

  Check finGroupType : Type.                (* 型クラス *)
  
(**
### 群の公理と定理

群 gT の要素 x, y, z の間で群の公理や定理が成り立ちます。
*)
  Variable gT : finGroupType.               (* 有限群 = 型インスタンス *)
  Variable x y z : gT.                      (* 有限群の要素 *)

  Check mulg x y : gT.                      (* 乗算 *)
  Check x * y : gT.                         (* 乗算（演算子） *)
  
  Check invg x : gT.                        (* 逆元 *)
  Check x^-1 : gT.                          (* 逆元（演算子） *)
  
  (* 群の公理 *)
  Goal 1 * x = x. Proof. by rewrite mul1g. Qed.
  Goal x * y * z = x * (y * z). Proof. by rewrite mulgA. Qed.
  Goal x^-1^-1 = x. Proof. by rewrite invgK. Qed.
  Goal (x * y)^-1 = y^-1 * x^-1. Proof. by rewrite invMg. Qed.
  
  (* 群の定理 *)
  Goal x * 1 = x. Proof. by rewrite mulg1. Qed.
  Goal x * x^-1 = 1. Proof. by rewrite mulgV. Qed.
  Goal x^-1 * x = 1. Proof. by rewrite mulVg. Qed.

(**
参考： mulg において、``FinGroup.base gT`` が gT のカノニカル解です。
（x や y が gT 型であることから、``FinGroup.base gT`` を見つけ出せるます）
*)
  Check @mulg : forall T : baseFinGroupType, T -> T -> T.
  Check @mulg (FinGroup.base gT) x y : FinGroup.base gT.
  Compute FinGroup.sort (FinGroup.base gT). (* gT *)

(**
別に定義した有限群 ``gT'`` と ``gT`` の要素の間の乗算はできません。
*)
  Section Sect_1_2.
    Variable gT' : finGroupType.            (* 別な有限群 *)
    Variable x' y' : gT'.
    
    Check x' * y' : gT'.
    Fail Check x' * y.
  End Sect_1_2.

(**
## ``group_set_of_baseGroupType gT``
*)

(**
### 集合としての群
  
テキストの6.2節でもそうですが、
群そのもの（有限集合としての有限群）を扱いたい場合があります。

``gT`` は型インスタンスであり、コアーションで型になることに間違いありません。
*)  
  Check FinGroup.sort gT : Type.
  Check gT : Type.                          (* コアーション *)
  Check x : gT.
  Check x \in gT.                           (* このような表記も可能です。 *)

(**
しかし、型と集合はCoqの対象としては別なものです。
*)
(**
## 集合としての群の型（その１）

集合としての群を扱うには次のようにします：

まず、``finGroupType``型クラスのインスタンス型（例：gT）の値を要素とする
有限集合の型は、``{set gT}``で表します。
  
``{set gT}``のインスタンス（この場合は集合） A, B, C は、次のように定義します：
 *)
  Check {set gT} : predArgType.
  Variable A B C : {set gT}.

(**
``{set gT}`` のインスタンスは、``[set _ : _ | _]`` のかたちでも定義できます。
あとで出てきます。任意のbool述語を併用して集合を定義できます。
*)
    Check [set a : gT | _] : {set gT}.

(**
また、``{set gT}`` は、predArgType で ``\in`` による判定ができます。
 *)
  Check x : gT.                             (* x は gT 型 *)
  Check x \in A : bool.                     (* true または false *)

(**
``mem A`` は、gT 型の変数が集合Aに含まれるか否かを決定する``gT -> bool``型の関数になります。
(``finset`` の ``set_type``の定義を参照のこと)。
*)
  Check mem A : gT -> bool.
  Check mem A x : bool. (* x \in A とだいたい同じ。。。ちょっと苦しい。 *)
  
(**
しかし、x は A型 でないことに注意してください。そもそも A は型ではありません。
 *)
  Fail Check x : A.
  Fail Check A : Type.
  
(**
集合としての群の型として、group_set_of_baseGroupType が定義されています。
 *)
  Check group_set_of_baseGroupType : baseFinGroupType -> Type.
  Check gT : baseFinGroupType.
  Check group_set_of_baseGroupType gT : Type.
  
(**
``group_set_of_baseGroupType gT`` は {set gT} のカノニカル解なので、
（A や B が ``{set gT}``型であることから、``group_set_of_baseGroupType gT``
を見つけ出すことができ）mulg (``*``) を使って集合としての群どうしの積が計算できます。
*)  
  Check @mulg : forall T : baseFinGroupType, T -> T -> T.
  Check @mulg (group_set_of_baseGroupType gT) A B : group_set_of_baseGroupType gT.
  
(**
## 集合としての群の型（その２）

ついで、有限群は``{group A}``で表します。

``{group A}``の実体は、``{set A}``を台として、
以下の条件を追加したものです(``fingroup`` の ``group_type``の定義を参照のこと)。
*)
  
(**
``{group gT}``のインスタンスは、次のように使って定義します：
*)
  Check {group gT} : predArgType.
  Variable G H : {group gT}.
  (**
有限群の公理や定理のうち、集合としての有限群がでてくるものが使えます。
*)

  Goal 1 \in G. Proof. by rewrite group1. Qed.
  Goal x \in G -> x^-1 \in G. Proof. by move/groupVr. Qed.
  Goal x \in G -> y \in G -> x * y \in G. Proof. apply: groupM. Qed.
  
(**
``{set T}`` と ``{group T}``の定義にはファントムタイプを使っていますが、
これは、``T``の部分に、
finType にカノニカルプロジェクションできる型だけを書けるように制限するためです。
*)
  Check {set bool}.                         (* bool型はよいが、 *)
  Fail Check {set nat}.                     (* nat型はダメ。 *)
  
(**
Math-Comp Book の 5.10.1 や次の文書も参照してください。

[https://github.com/suharahiromichi/coq/blob/master/math-comp-book/suhara.ch7-phantom_types.v]

*)

(**
## 剰余類 (coset) の定義

MathComp には、関数``rcoset`` と 演算子``A :* x`` のふたつの定義があります。
このふたつは別のものです。
 *)
(**
### ひとつめの定義

関数``rcoset``の定義は、有限群Aのすべての要素に、右からxを掛けたものです。
(A の ``mulg x = λy.(x * y)`` による像の集合といえます。)
*)
  Check rcoset : {set gT} -> gT -> {set gT}.
  
  Check rcoset A x.
  Check (fun a => mulg a x) @: A.           (* rcoset を展開する。 *)
  Check mulg^~x @: A.                       (* ``^~`` は MathComp 風の表記 *)
  Check [set a * x | a in A].               (* ``@:`` を展開する。 *)
  (* ``@:`` は、finset で定義 *)
  
(**
### ふたつめの定義

演算子``A :* x``の定義は、有限集合としての有限群Aと``{x}``を掛けたものです。
*)
  Check A :* x.
  Check A * [set x].                    (* ``:*`` を展開する。 *)
  Check mulg A [set x].                 (* ``*`` を展開する。 *)
  
(**
### ふたつの定義がおなじであることの証明
*)
  Check rcosetE
    : forall (gT : finGroupType) (A : {set gT}) (x : gT), rcoset A x = A :* x.
  Check rcosetP
    : reflect (exists2 a, a \in G & y = a * x) (y \in G :* x).
  
(**
## 剰余群 (cosets) の定義

MathComp には、関数``rcosets`` があります。
``rcosets A B`` は、有限集合としての有限群Bのすべての要素に、
有限集合としての有限群Aのすべての要素を右から掛けたものです。

関数``rcosets``の定義は、
有限集合としての有限群Bのすべての要素に、
有限集合としての剰余類Aを右から掛けたものです。
 *)
  Check rcosets : {set gT} -> {set gT} -> {set {set gT}}.
  
  Check rcosets A B.
  Check (rcoset A) @: B.                    (* rcosets を展開する。 *)
  
(**
### ひとつめの定義

rcoset の定義を rcoset のひとつめの定義（``[set a * x | a in A] ``）で展開すると、
つぎのようになります。
*)
  Check [set (rcoset A x) | x in B].        (* ``@:`` を展開する。 *)
  Check [set [set a * x | a in A] | x in B]. (* rcoset を展開する。 *)
(**
これは、次に示すものではありません。
*)    
  Check A * B  : {set gT}.

(**
### ふたつめの定義

rcoset の定義を rcoset のふたつめ定義（``A :* x``）で展開すると、
つぎのようになります。
*)
  Check [set (A :* x) | x in B].
    
(**
### ふたつの定義がおなじであることの証明

ここで、 exists2 の2は、2つの命題を&で結ぶという意味。
*)
  Check rcosetsP
    : reflect (exists2 x, (x \in B) & (C = A :* x)) (C \in rcosets A B).

End Sect_1.

(**
# おまけ

rcosetsP の「ふたつめの定義」に近い定義を示す。
*)
Section Appendix.
  
  Variable gT : finGroupType.
  
(**
左が rcosetsP の書き方、右が「ふたつめの定義」の書き方です。
*)
  Lemma test (B C : {set gT}) f :
    reflect (exists2 x, (x \in B) & (C = f x)) (C \in [set f x | x in B]).
  Proof.
      by apply: imsetP.
  Qed.
  
  Lemma rcosetsP' (A B C : {set gT}) :
    reflect (C \in [set (A :* x) | x in B]) (C \in rcosets A B).
  Proof.
    apply: (iffP idP).
    - move=> H.
        by apply/imsetP/rcosetsP.
    - by move/imsetP/rcosetsP.
  Qed.
  
End Appendix.

(* END *)
