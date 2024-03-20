Porting Coq Scripts to the Mathematical Components Library Version 2


# 1. Target Audience of this Document このドキュメントの対象読者

1. Canonical コマンドを使用していない MathComp ユーザーは、MathCompの過去のバージョン アップグレードと比較して、大きな違いは感じられないはずです。 現在では役に立たないいくつかの識別子は削除されましたが、これは変更ログに文書化されています。 たとえば、 ``bool_eqType`` を ``bool : eqType`` または単に ``bool`` に置き換える必要がある場合があります。 また、一部の書き換えの動作が変更され、明示的なパターンが必要になる場合があります。 通常、結合法則についての補題を使用した書き換えでは、ユーザーが等価関係の左側と右側のどちらで起こるかを指定する必要があるため、``addrA`` の書き換えを ``rewrite [in LHS]addrA`` に書き換える必要がある場合があります。具体的な例については 4.4 を参照してください。 そのようなユーザーの場合、このチュートリアルを最後まで読む必要はないかもしれません。

2. 対象読者は主に、Canonical コマンドを使用して構造体をインスタンス化している MathComp ユーザーです。

3. 独自の構造階層を開発している少数のユーザーにとって、このチュートリアルはあまり役に立たない可能性があり、むしろ以下を参照する必要があります。

  - the original paper for an extensive introduction to HB commands [4],
  - the HB development for documentation and examples [7] (start with the README),
  -  various papers for more applications [1] [2, Sect. 3] [3, Sect. 4],
  -  already ported developments such as odd-order, multinomials, etc.

具体的にするために、セクション4 で CompDecModal [5] のポートを説明します。その前に、セクション2 で HB の基本を確認します。セクション3で移植に使用できるドキュメントとツールを確認します。 


# 2. Quick Reminder about the HB Vocabulary 
このセクションの目的は、HB によって導入された 3 つの主要なコマンド、HB.mixin、HB.struction、および HB.instance を簡単に説明することです。 知識のある読者はこのセクションを読み飛ばしても問題ありません。
最も基本的なシナリオを一般的な観点から考えてみましょう。 以下は階層の最下位に位置する構造体 Struct を宣言するパターンです。 構造体のインターフェイスは``Mixin``に入ります。

```
HB.mixin Record isStruct params carrier := {
  ... properties about the carrier ...
}
```
構造体自体は sigma-type のように宣言されます。

```
#[short(type=structType)]
HB.structure Definition Struct params := {carrier of isStruct params carrier}
```
HB は Coq 属性を使用して、構造に対応する型を宣言していることに注意してください。 以下は、既存の構造体 Struct を拡張する新しい構造体 NewStruct を宣言するパターンです。注 ``of`` 構文に注意してください。

```
HB.mixin Record NewStruct_from_Struct params carrier
  of Struct params carrier := {
  ... more properties about the carrier ...
}
```
拡張構造の場合、シグマタイプは親構造への依存関係を示します。注 ``&``構文に注意してください。

```
#[short(type=newStructType)]
HB.structure Definition NewStruct params :=
             {carrier of NewStruct_from_Struct parames carrier
                       & Struct params carrier}.
```
このプロセスの結果、型 structType と newStructType が作成され、後者の要素は前者の要素としても理解されるようになります。最後に、ミックスイン Struct の宣言には、コンストラクター Struct.Build が作成され、次のコマンドを使用して構造体をインスタンス化するために使用されます。

```
HB.instance Definition _ := Struct.Build params.
```
コマンド HB.instance は、次のような数行の情報出力の出力を引き起こすでしょう。

```
module_type__canonical__struct_Struct is defined
```
この出力がない場合は、多くの場合、HB.instance コマンドの失敗を示します。

# 3. Tools to Port MathComp Applications

## 3.1 Documentation
以下のドキュメントは、MathComp アプリケーションを MathComp 2 に移植する手順に役立ちます。

- The changelog is the primary source of information. See CHANGELOG.md [9].

- Additionally, structures are documented in the headers of Coq scripts according to the following format:

```
(*****************************************************************************)
(* Centered Title                                                            *)
(*                                                                           *)
(* Some introductory text: what is this file about, instructions to use this *)
(* file, etc.                                                                *)
(*                                                                           *)
(* Reference: bib entry if any                                               *)
(*                                                                           *)
(* * Section Name                                                            *)
(* definition == prose explanation of the definition and its parameters      *)
(*   notation == prose explanation, scope information should appear nearby   *)
(* structType == name of structures should make clear the corresponding      *)
(*               HB structure with the following sentence:                   *)
(*               "The HB class is Xyz."                                      *)
(*  shortcut := a shortcut can be explained with (pseudo-)code instead of    *)
(*              prose                                                        *)
(*                                                                           *)
(* Acknowledgments: people                                                   *)
(*****************************************************************************)
```
たとえば、ファイル ssreflect/eqtype.v で定義されている eqType 構造を参照してください。スクリプトのドキュメントの詳細については、この Wiki エントリを参照してください。

- オプションで、ユーザーは CONTRIBUTING.md [9] で説明されている命名規則に従って識別子と補題の命名を再確認できます。

## 3.2 HB Commands Useful to Explore an Existing Hierarch
changelog と Coq スクリプトのヘッダーに加えて、ユーザーは HB コマンドを使用して数学的構造の階層を探索できます。

### 3.2.1 Information about Structures with HB.about構造に関する基本情報は、次のようにコマンド HB.about を使用して取得できます。

```
> HB.about eqType.
HB: eqType is a structure (from "./ssreflect/eqtype.v", line 137)
HB: eqType characterizing operations and axioms are:
    - eqP
    - eq_op
HB: eqtype.Equality is a factory for the following mixins:
    - hasDecEq (* new, not from inheritance *)
HB: eqtype.Equality inherits from:
HB: eqtype.Equality is inherited by:
    - SubEquality
    - choice.Choice
...
```
(出力メッセージはファクトリーを参照します。これはミックスインの一般化です。)
HB 階層のグラフ コマンド HB.graph を使用して HB 階層を調べることもできます。Coq ファイル内:

```
HB.graph "hierarchy.dot".
```
端末の中から、

```
tred hierarchy.dot | dot -Tpng > hierarchy.png
```
For example, Fig. 1 displays the immediate vicinity of eqType.
（略）
Figure 1: The vicinity of the structure eqType in MathComp


### 3.2.2 Information about Constructors with HB.howto and HB.about
構造体を構築するコンストラクターを検出するには、コマンド HB.howto を使用できます。 例えば:

```
> HB.howto eqType.
HB: solutions (use 'HB.about F.Build' to see the arguments of each factory F):
    - hasDecEq
```
eqType インスタンスは hasDecEq.Build で構築できることがわかります。 (デフォルトでは、HB.howto は利用可能なすべてのファクトリーを返さない可能性があることに注意してください。HB.howto xyzType 5 のように自然数を使用して深さの検索を増やす必要がある場合があります。)xyz.Build コンストラクターがどのパラメーターを予期しているかを知るには、HB.about コマンドを使用できます。

```
> HB.about hasDecEq.Build.
HB: hasDecEq.Build is a factory constructor
    (from "./ssreflect/eqtype.v", line 135)
HB: hasDecEq.Build requires its subject to be already equipped with:
HB: hasDecEq.Build provides the following mixins:
    - hasDecEq
HB: arguments: hasDecEq.Build T [eq_op] eqP
    - T : Type
    - eq_op : rel T
    - eqP : Equality.axiom eq_op
```
このメッセージは、 hasDecEq.Build が型 T、述語 ``eq_op : rel T`` (角括弧で示される暗黙の引数)、および ``Equality.axiom eq_op`` の証明を予期していることを示します。したがって、ある型 T で eqType をインスタンス化するには

```
HB.instance Definition _ := hasDecEq.Build T proof_of_Equality_axiom.
```
または

```
HB.instance Definition _ := @hasDecEq.Build T eq_op proof_of_Equality_axiom.
```
そのうちの数行が出力されるはずです (この出力がない場合は、インスタンス化に問題があることを示していることが多いことを思い出してください)
この記事の執筆時点では、VSCoq では HB.instance コマンドの出力がデフォルトで表示されない可能性があることも確認しています。

```
module_T__canonical__eqtype_Equality is defined
```

#### Discover Aliases and Feather Factories エイリアスとフェザー ファクトリの検出 
HB.about でリストされている構造体とコンストラクターに加えて、ライブラリではいくつかのエイリアス (別名フェザー ファクトリ) が定義されています。 これらのエイリアスはヘッダーのコメントに記載されています。 たとえば、ある型 T の eqType インスタンスは、関数 ``f : T -> T'`` と証明 ``injf : injective f`` が与えられると、すでに eqType 構造を備えたある T' から派生できます。

```
HB.instance Definition _ := Equality.copy T (inj_type injf).
```
inj_type は eqType.v を参照。


### 3.2.3 Information about Instances with HB.about
タイプにすでに装備されているインスタンスは、HB.about を使用してリストできます。たとえば、次のようになります。

```
> HB.about bool.
HB: bool is canonically equipped with structures:
    - Order.BDistrLattice
      Order.BLattice
      Order.BPOrder
      (from "./ssreflect/order.v", line 6064)
...
```
bool がすでに備えているすべての構造をリストします。


# 4 Porting a MathComp Development to MathComp 2
既存の MathComp 開発を MathComp 2 に移植する基本戦略は、(1) Math-Comp 2 をインストールし、(2) 既存の Coq スクリプトをコンパイルし、(3) エラーを次々に修正することです。 具体的にするために、CompDecModal [5] の移植について説明します。 

``https://github.com/coq-community/comp-dec-modal``
これは、MathComp を適度に使用した開発であり、その移植には、MathComp を使用するほとんどの開発で使用される可能性が高い基本構造のインスタンス化の修正が含まれます。
以下では、問題のあるコマンドが灰色の領域に表示されます。

```coq:mathcomp1
command incompatible with MathComp 2
```
そしてそれらの修正は単独で有名です:

```coq:mathcomp2
MathComp 2 fix for the command above
```

## 4.1 Import the HB Library
まず最初に、HB を使用する Coq ファイルは次で始まる必要があります。

```
From HB Require Import structures.
```

## 4.2 Instantiation of Structures with MathComp 2
MathComp ユーザーの観点から見ると、主な変更点は数学的構造がインスタンス化される方法です。 ほとんどの Canonical (または Canonical Structure) コマンドは HB.instance (セクション2 を参照) に置き換えられ、[subType ...] などの MathComp 表記に小さな変更が加えられています。CompDecModal に関して、最初の問題となるコマンド セットは次のとおりです(file ``theories/libs/fset.v``)。

```coq:mathcomp1
Section FinSets.
  Variable T : choiceType.
  ...
  Canonical Structure fset_subType := [subType for elements by fset_type_rect].
  Canonical Structure fset_eqType := EqType _ [eqMixin of fset_type by <:].
  Canonical Structure fset_predType := PredType (fun (X : fset_type) x => nosimpl x \in elements X).
  Canonical Structure fset_choiceType := Eval hnf in ChoiceType _ [choiceMixin of fset_type by <:].
End FinSets.

Canonical Structure fset_countType (T : countType) :=
  Eval hnf in CountType _ [countMixin of fset_type T by <:].
Canonical Structure fset_subCountType (T : countType) :=
  Eval hnf in [subCountType of fset_type T].
```
コンパイルエラーを順番に考えてみましょう。

```
> Canonical Structure fset_subType := [subType for elements by fset_type_rect].
Error: Syntax error: [reduce] expected after ':=' (in [def_body]).
```
このエラーは、変更ログに記載されている表記の変更が原因です。 たとえば、次のように文字列を検索します。CHANGELOG.md の ``[subType`` :

```
- in `eqtype.v`
  ...
  + notation `[subType for v by rec]`, use `[isSub for v by rec]`
  ...
```
したがって、修正は次のようになります。

```
> HB.instance Definition _ := [isSub for elements by fset_type_rect].
HB_unnamed_factory_3 is defined
fset_fset_type__canonical__eqtype_SubType is defined
```
インスタンスに名前を付ける必要はありません。インスタンスを自動的に見つけるのは HB の仕事であるため、名前を付けないほうがよいことに注意してください。HB が HB.instance への応答として複数のメッセージを表示することを確認することが重要です。そうでない場合、これはインスタンス化の失敗を示している可能性があります。次のコンパイル エラー:

```
> Canonical Structure fset_eqType := EqType _ [eqMixin of fset_type by <:].
Error: The reference EqType was not found in the current environment.
```
このエラーは主に、EqType コンストラクターの削除が原因です [6、セクション 6]。 2.1]。実際、MathComp のほとんどの xyzType コンストラクターはもう必要ありません。 changelog を参照してください。上記の [subType for _ by _] notationと同様に、[eqMixin of _ by <:] は次のように変更されました。

```
- in `eqtype.v`
  ...
  + notation `[eqMixin of T by <:]`, use `[Equality of T by <:]`
  ...
```
したがって、修正は次のようになります。

```
> HB.instance Definition _ := [Equality of fset_type by <:].
HB_unnamed_factory_8 is defined
eqtype_Equality__to__eqtype_hasDecEq is defined
HB_unnamed_mixin_10 is defined
fset_fset_type__canonical__eqtype_Equality is defined
fset_fset_type__canonical__eqtype_SubEquality is defined
```
次の 2 つのコンパイル エラーも同様に、choiceType と CountType の削除と、
``[choiceMixin of _ by <:]`` および ``[countMixin of _ by <:]`` という表記の変更が原因で発生します。

```
> Canonical Structure fset_choiceType := Eval hnf in ChoiceType _ [choiceMixin of fset_type by <:].
Error: The reference ChoiceType was not found in the current environment.
> Canonical Structure fset_countType (T : countType) := Eval hnf in CountType _ [countMixin of fset_type T by <:].
Error: The reference CountType was not found in the current environment.
```
修正はchangelogから再度推測できます。

```
> HB.instance Definition _ := [Choice of fset_type by <:].
HB_unnamed_factory_11 is defined
choice_Choice__to__choice_hasChoice is defined
HB_unnamed_mixin_14 is defined
fset_fset_type__canonical__choice_Choice is defined
fset_fset_type__canonical__choice_SubChoice is defined
> HB.instance Definition _ (T : countType) := [Countable of fset_type T by <:].
T is declared
HB_unnamed_factory_30 is defined
choice_Countable__to__choice_hasChoice is defined
choice_Countable__to__eqtype_hasDecEq is defined
choice_Countable__to__choice_Choice_isCountable is defined
HB_unnamed_mixin_34 is defined
fset_fset_type__canonical__choice_Countable is defined
fset_fset_type__canonical__choice_SubCountable is defined
```
HB は #[hnf] 属性を提供しますが、通常は必要ないことに注意してください。最後に、最後の Canonical コマンドにより、対処する必要がある非推奨の警告が表示されます。

```
> Canonical Structure fset_subCountType (T : countType) :=
>   Eval hnf in [subCountType of fset_type T].
Warning: Notation "[ subCountType of _ ]" is deprecated since mathcomp 2.0.0.
Use SubCountable.clone instead.
[deprecated-notation,deprecated]
fset_subCountType is defined
```
実際、1ステップ戻ると、HB.instance コマンドの出力から、Countable 構造体のインスタンス化がすでに SubCountable 構造体のインスタンス化をトリガーしており、最後の Canonical コマンドが有害になっていることがわかります。 したがって、削除する必要があります。要約すると、完全な修正は次のとおりです。

```coq:mathcomp2
 1 Section FinSets.
 2 Variable T : choiceType.
 3 ...
 4 HB.instance Definition _ := [isSub for elements by fset_type_rect].
 5 HB.instance Definition _ := [Equality of fset_type by <:].
 6 Canonical Structure fset_predType := PredType (fun (X : fset_type) x => nosimpl x \in elements X).
 7 HB.instance Definition _ := [Choice of fset_type by <:].
 8 End FinSets.
 9
10 HB.instance Definition _ (T : countType) := [Countable of fset_type T by <:].
```
実際、さらに一歩先に進むことができます。
5行目で Equality 構造体をインスタンス化し、次に 7行目で Choice 構造体をインスタンス化する代わりに、Choice 構造体をインスタンス化して Equality 構造体を自動的に取得することで、より短い修正は次のようになります。

```coq:mathcomp2
Section FinSets.
  Variable T : choiceType.
  ...
  HB.instance Definition _ := [isSub for elements by fset_type_rect].
  HB.instance Definition _ := [Choice of fset_type by <:].
  Canonical Structure fset_predType := PredType (fun (X : fset_type) x => nosimpl x \in elements X).
End FinSets.

HB.instance Definition _ (T : countType) := [Countable of fset_type T by <:].
```
この小さな例は、MathComp 2 への移植の利点をすでに示しています。

## 4.3 Finitely Iterated Operators
CompDecModal の移植時に発生する次の一連のコンパイル エラーは、ほとんどの MathComp 開発で使用される可能性が高い、有限反復演算子に関するものです。

```coq:mathcomp1
Canonical Structure fsetU_law (T : choiceType) :=
  Monoid.Law (@fsetUA T) (@fset0U T) (@fsetU0 T).
Canonical Structure fsetU_comlaw (T : choiceType) :=
  Monoid.ComLaw (@fsetUC T).
```
最初のコンパイル エラーは、コンストラクターのシグネチャの変更を示します。

```
> Canonical Structure fsetU_law (T : choiceType) :=
> Monoid.Law (@fsetUA T) (@fset0U T) (@fsetU0 T).
Error:
In environment
T : choiceType
The term "fsetUA (T:=T)" has type "forall X Y Z : {fset T}, X `|` (Y `|` Z) = X `|` Y `|` Z"
while it is expected to have type "Type".
```
HB.about を使用して、関連する構造を見つけることができます (セクション 3.2.1 を参照)。

```
> HB.about Monoid.Law.
HB: Monoid.Law.type is a structure (from "./ssreflect/bigop.v", line 415)
...
```
HB.howto を使用して、この構造を構築する方法を確認できるようになりました (セクション 3.2.2 を参照)。

```
> HB.howto Monoid.Law.type
HB: solutions (use 'HB.about F.Build' to see the arguments of each factory F):
    - Monoid.isLaw
    - SemiGroup.isLaw; Monoid.isMonoidLaw
```
最後に、HB.about を使用してコンストラクトのパラメータについて学習できます (セクション 3.2.2 を参照)。

```
> HB.about Monoid.isLaw.Build
...
HB: arguments: Monoid.isLaw.Build T idm op opA op1m opm1
    - T : Type
    - idm : T
    - op : T -> T -> T
    - opA : associative op
    - op1m : left_id idm op
    - opm1 : right_id idm op
```
これで、コンパイル エラーを修正するのに十分な情報が得られました。

```
HB.instance Definition _ (T : choiceType) :=
  Monoid.isLaw.Build {fset T} fset0 fsetU (@fsetUA T) (@fset0U T) (@fsetU0 T).
```
インスタンス化でキー (演算子 fsetU) を明示的にしたことに注意してください。厳密に必要というわけではありませんが、この機会に文書化しておくことをお勧めします。
次のコンパイル エラー:

```
> Canonical Structure fsetU_comlaw (T : choiceType) :=
> Monoid.ComLaw (@fsetUC T).
Error:
In environment
T : choiceType
The term "fsetUC (T:=T)" has type "forall X Y : {fset T}, X `|` Y = Y `|` X"
  while it is expected to have type "Type".
```
これは上記と似ています。Monoid.ComLaw について知るには HB.about を使用し、その構築について調べるには HB.howto を使用します。

```
> HB.howto Monoid.ComLaw.type.
HB: solutions (use 'HB.about F.Build' to see the arguments of each factory F):
    - Monoid.isComLaw
    - SemiGroup.isComLaw; Monoid.isMonoidLaw
    - SemiGroup.isCommutativeLaw; Monoid.isLaw
    - SemiGroup.isLaw; SemiGroup.isCommutativeLaw; Monoid.isMonoidLaw
```
キー fsetU にはすでに Monoid.Law 構造が装備されているため、このキーを追加パラメーターとして HB.howto に追加して、検索を制限できることに注意してください。

```
> HB.howto fsetU Monoid.ComLaw.type.
HB: solutions (use 'HB.about F.Build' to see the arguments of each factory F):
    - SemiGroup.isCommutativeLaw
```
次に、SemiGroup.isCommutativeLaw.Build のパラメーターを確認して、次の修正を考え出します。

```
HB.instance Definition _ (T : choiceType) :=
  SemiGroup.isCommutativeLaw.Build _ fsetU (@fsetUC T).
```
要約すると、以下を使用して有限反復演算子に関するコンパイル エラーを修正します。

```coq:mathcomp2
HB.instance Definition _ (T : choiceType) :=
  SemiGroup.isCommutativeLaw.Build _ fsetU (@fsetUC T).
HB.instance Definition _ (T : choiceType) :=
  Monoid.isLaw.Build {fset T} fset0 fsetU (@fsetUA T) (@fset0U T) (@fsetU0 T).
```
実際、Monoid.ComLaw 構造体のインスタンス化から Monoid.Law 構造体を取得できるため、インスタンス化を 1つだけ行うこともできます。そのため、より良い修正は次のようになります。

```coq:mathcomp2
HB.instance Definition _ (T : choiceType) :=
  Monoid.isComLaw.Build _ _ fsetU (@fsetUA T) (@fsetUC T) (@fset0U T).
```

## 4.4 Other Compilation Errors
他のコンパイル エラーは上ですでに説明したものと似ているため、ここではさらに詳しく説明します。

#### Instantiation of an Equality Structure
次のコンパイル「エラー」はファイル ``K/K_def.v`` にあります：

```coq:mathcomp1
Definition form_eqMixin := EqMixin (compareP eq_form_dec).
Canonical Structure form_eqType := Eval hnf in @EqType form form_eqMixin.
```
この障害は主に EqMixin の削除が原因で発生します。変更ログでは、パラメータを HB.howto で二重チェックできるコンストラクター hasDecEq.Build を使用することを提案しており、これにより次の修正が行われます。

```coq:mathcomp2
HB.instance Definition _ := hasDecEq.Build form (compareP eq_form_dec).
```


#### Instantiation of a Countable Structure
次のコンパイル「エラー」はファイル ``K/K_def.v`` にあります：

```coq:mathcomp1
Definition form_countMixin := PcanCountMixin formChoice.pickleP.
Definition form_choiceMixin := CountChoiceMixin form_countMixin.
Canonical Structure form_ChoiceType := Eval hnf in ChoiceType form form_choiceMixin.
Canonical Structure form_CountType := Eval hnf in CountType form form_countMixin
```
PcanCountMixin が非推奨となり、CountChoiceMixin が廃止されたことがわかりました。 changelog では、PcanCountMixin の代わりに PCanIsCountable を使用することが推奨されています。Locate によると、PCanIsCountable はファイル ``ssreflect/choice.v`` にあり、次のタイプを持っています。

```
PCanIsCountable :
forall [T : countType] [sT : Type] [f : sT -> T] [f' : T -> option sT], pcancel f f' ->
  isCountable.axioms_ sT
```
したがって、この場合の修正は次のようになります。

```coq:mathcomp2
HB.instance Definition _ : isCountable form := PCanIsCountable formChoice.pickleP.
```
インスタンス化を実行するときに推奨されるように、キー (ここではフォーム) を明示するために型情報を追加したことに注意してください。Countable インスタンスとともに Choice インスタンスも生成されるため、この修正で十分です。


#### ``Equality`` 構造体のその他のインスタンス化
ファイル ``Kstar_def.v``、``gen_def.v``、および ``CTL_def.v`` のなかの次のコンパイルエラーは、すでに上で説明したように処理されます。

#### ``rewrite``タクティクの失敗
次のコンパイル「エラー」はファイル ``CTL/demo.v`` にあります。 これは実際には、MathComp 2 へのアップグレードによって実行が大幅に遅くなった戦術です。

```coq:mathcomp1
move => [p' y]. rewrite /MRel /Mstate (negbTE (root_internal _)) [_ && _]/= orbF.
```
問題のある書き換えは orbF によるものです。 以前は、デフォルトで ``<->`` 等価の左側に適用されていましたが、現在では、適切な実行時間を回復するために、ユーザーはパターンで書き換え位置を指定する必要があります。

```coq:mathcomp2
move => [p' y]. rewrite /MRel /Mstate (negbTE (root_internal _)) [_ && _]/=.
rewrite [in X in X <-> _]orbF.
```
ただし、この種の減速はかなり例外的です。
さらにいくつかのコンパイル エラーがありますが、これまで説明したものと似ています。

# 5 Conclusion
このドキュメントでは、典型的な MathComp 開発の MathComp 2 への移植について説明しました。私たちは利用可能なツール (ドキュメントと HB 戦術) をレビューし、多数の具体的なサンプル エラーと警告を調べて説明し、修正しました。CompDecModal の移植例では、HB を使用すると読みやすさの点で Coq スクリプトが改善され、さらには改善が可能になることが実証されました。 完全な修正はオンラインで見つけることができます。編集には 10 個のファイル、35 個の挿入、67 個の削除が含まれており、これはおそらく中程度の作業量に相当します。MathComp 2 への移行プロセスでは、コミュニティが https://coq.zulipchat.com の math-comp ストリームを通じて回答できるさらに多くの質問が確実に生成されるでしょう。


# References
原典を参照してください。追加として、

Reynald Affeldt, "An Introduction to MathComp-Analysis"

``https://staff.aist.go.jp/reynald.affeldt/documents/karate-coq.pdf``
ただし、MathComp2に準拠しているのは5章以降で、3章はMathComp1です。

```
