Tezos' Michelson small-setp semantics

# はじめに

Tezos' Michelson は、Big-Step で意味が与えられていますが([1.][2.])、
ここでは Small-Step の意味を考えてみようとおもいます。

Michelson は、型つきのスタック指向言語ですが、PostScript や HP電卓のRPMと比べて
特徴的なのは *DIP* 命令です。

DIP命令は、DIP code: Runs code protecting the top of the stack. と定義されていて、
スタックトップを残した状態で引数のコードを実行します([1.]。

``
:: 'b : 'A   ->   'b : 'C
   iff   code :: [ 'A -> 'C ]

> DIP code / x : S  =>  x : S'
    where    code / S  =>  S'
``

スタックトップの値をどこかに保存しておいて、引数のコードを実行し、元に戻す、
必要があります。これを実現するには（DIP命令がネストされることを考慮すると）、
スタックがもうひとつ必要になることがわかります。

ここで示す Small-Step 定義は、コードスタック（継続スタック）と
値スタック（オペランドスタック）を使うものです([3.]。
これに、UPPERスタックを加えたみっつのスタックで定義を考えてみます。

# 文献

[1.] Michelson: the language of Smart Contracts in Tezos,
     https://tezos.gitlab.io/master/whitedoc/michelson.html

[2.] https://gitlab.com/nomadic-labs/mi-cho-coq/tree/master/src/michocott

[3.] 坂口、Coqによる定理証明 Coqでスタック指向プログラミング、Stricter.org


以上
