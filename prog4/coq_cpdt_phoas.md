(**
- CPDT
17.2 Parametric Higher-Order Abstract Syntax


# 17.2 Parametric Higher-Order Abstract Syntax

Here the idea is to parameterize the syntax type by a type family standing for a representation of variables.
ここでの考え方は、変数の表現を表す型ファミリによって構文型をパラメータ化することです。

- Inductive term
Coq はこの定義を受け入れます。なぜなら、埋め込み関数は、任意の項ではなく、単に変数を引数として受け取るからです。ここで、パラメータ var を項自体としてインスタンス化するという、簡単に利用できる抜け穴があるのではないかと疑問に思う人もいるかもしれません。しかし、それを行うには、このネストされた項の言及に対して変数表現を選択し、項の引数への無限降下を通じてこれを続ける必要があります。

var 型ファミリーのすべての可能な選択肢に対して多態的量化を使用して、閉じた項の最終的な型を記述します。

- Definition Term

- Example add
- Example three the hard way


# 17.2.1 Functional Programming with PHOAS

The key to effective deconstruction　of PHOAS terms is one principle: treat　the var parameter as an　unconstrained choice of which data should be annotated on each　variable.
var パラメータを、各変数にどのデータを注釈するかの制約のない選択として扱うことです。PHOAS 項に出現する変数ノードの数を数えるという簡単な例から始めます。

- Fixpoint countVars
- Definition CountVars


Here is a suggestive example, translating　PHOAS terms into strings giving a first-order rendering.
直感的には、PHOAS と任意の適切な一次表現との間で相互変換が可能です。次に、PHOAS 項を一次表現を提供する文字列に変換する、示唆に富む例を示します。

- Fixpoint pretty


However, it is not necessary to convert to first-order form to support many common　operations on terms. For instance, we can implement substitution of terms for variables.
ただし、項に対する多くの一般的な操作をサポートするために、1階形式に変換する必要はありません。たとえば、変数に対する項の置換を実装できます。

The key insight here is to tag variables with terms, so that, on encountering a variable, we　can simply replace it by the term in its tag
ここでの重要な洞察は、変数に項をタグ付けすることです。これにより、変数に遭遇したときに、そのタグ内の項で簡単に置き換えることができます

Note that this function squash is parameterized over a specific var choice.
この関数 squash は、特定の var 選択に対してパラメーター化されることに注意してください。

- Fixpoint squash

To define the final substitution function over terms with single free variables, we define Term1, an analogue to Term that we defined before for closed terms.

単一の自由変数を持つ項に対する最終的な置換関数を定義するために、
閉じた項に対して以前に定義した Term に類似した Term1 を定義します。

- Definition Term1

Subst は、(1) Term1 をインスタンス化して変数に用語をタグ付けし、
(2) 結果を置換する特定の項に適用することで定義されます。
squash のパラメーター var がどのようにインスタンス化されるかに注意してください。
Subst の本体自体は var に対する多態的量化であり、出力用語の変数タグの選択を表します。
そして、その入力を使用して入力用語のタグ選択を計算します。

- Definition Subst

最初は驚くかもしれませんが、さらにもう 1 つの開発は、変数にその表示をタグ付けするときに、通常の項の表示的意味を与える関数も実装できることです。

- Fixpoint termDenote
- Definition TermDenote


# 17.2.2 Verifying Program Transformations

- Fixpoint ident
- Definition Ident
- Theorem IdentSound

- Fixpoint cfold
- Definition Cfold
- Lemma cfoldSound
- Theorem CfoldSound

- Fixpoint unlet
- Definition Unlet
- Definition three a harder way

- Record varEntry

- Inductive wf
- Definition Wf
- Theorem three the hard way Wf

- Lemma unletSound
- Theorem UnletSound

# 17.2.3 Establishing Term Well-Formedness

- Lemma wf monotone

- Lemma unletWf
- Theorem UnletWf


# 17.2.4 A Few More Remarks

- Example Add
- Example Three the hard way

 *)

