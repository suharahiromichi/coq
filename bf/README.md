Brainfuck (Brainf\*uck) の Small-Step semantics
-- または、もうひとつの Coq で書いた brainf\*ckインタプリタ

@suharahiromichi

2019_10_26
c


# 初めに

Small-Step semantics を定義して、それを使ってインタプリタを実行する。
実行の繰り返しには、[2.] がLtac の再帰呼び出しを使っていることに対して、
「do !」 つまり repeat タクティクで行っている。

2個スタックのVMでの実装、すなわち Small-Step semantics は [3.] を参考にした。

Coqのコードは、全体的に [1.] の考え方に沿っている。


# 参考

[1.] 坂口、Coqによる定理証明 Coqでスタック指向プログラミング、Stricter.org

[2.] Coqはチューリング完全 -- Ltacでbrainf*ckインタプリタを書いた
     https://qiita.com/erutuf13/items/98f15cc7e74b0570c971

[3.] Cはチューリング完全だった
     https://qiita.com/takl/items/6ffe14db22974b1f74ce

以上
