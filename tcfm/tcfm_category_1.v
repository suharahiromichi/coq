(**
いろいろな具象圏をCoqで実装してみた
----------------------------------------------
*)

(**

# はじめに

## Coqで圏論

Coqで圏論というと、 2016年にすでに素晴らしい記事[1]があり、
また[2]にもとづく[3]もあるので、
私のようなものが書くことはないのですが、
私の興味は[4][5]にあります。

つまり「〜が圏をなすこと」を形式的に証明したい、
さらに、いろいろなものが圏をなすことをいわば手当たり次第に証明できないか、
とも考えました。

プログラマの視点から、
いろいろな圏についてわかりやすく説明したものに[6]があり参考になります。


## Class コマンド と Instance コマンド

「しりとりゲームが圏をなす」、あるいは、集合と関数が圏をなす、半順序が圏をなす、
といった一連のことを証明するのであれば、なんらかの構造的な手法も併用できるはずです。

Coqにはファーストクラスのファシリティとして、Type Class (型クラス）があります[7]。
この Type Class 自体はHaskellに起源をもつものだそうです。
Classで仕様を記述し、Instanceで実体を構成します。
Coqなので、実体の構成には証明を記述することになります。

[8]には、数学への応用が解説されています。
今回はその[8]の6章のCategoryの定義に基づいています。


## Program コマンド

Coq の Programコマンドは、Definition や Fixpoint と組み合わせて使うことが普通ですが、
Instance と組み合わせて使うこともできます。

Program Instnce とすることで、実体を構成するときに大幅な自動化が行われ、
証明責務(Obligation)として必要な箇所だけ、証明を埋めれば完成です。

 *)

(**
# 圏のClass定義

[8] の Class Cagegory の定義を以下にしめします。
Coq 8.8.1 で動作するように修正しています。

Relation と Morphims を使用しています。
Relation は Equivalence のために、
Morphisms は Proper のために使用します。
後者については説明を省きますが[7]を参照してください。
ProofIrrelevance は後で説明します。
 *)

(**

 *)

(**
# 関手の定義
*)


(**
# まとめ

いくつかの具象圏について、
Coqの Class と Program Instance コマンドを使って、
形式的かつ構造的に証明してみました。

Coqを使った形式的な定義というと、補題を積み重ねて定理を証明する、
という、いかにも数学的な流れであることが多いのですが、
証明責務を埋めるやりかたも、おもしろいのではないでしょうか。

最後になりましたが、表題は[4]に敬意を表わしたものです。
*)



(**
[1] https://qiita.com/mathink/items/2067c162fb7cf8f6c83f 

[2] https://global.oup.com/academic/product/category-theory-9780199237180?cc=jp&lang=en&

[3] http://www.megacz.com/berkeley/coq-categories/

[4] http://yosh.hateblo.jp/entry/20090425/p1

[5] http://d.hatena.ne.jp/m-hiyama/20060821/1156120185

[6] http://bitterharvest.hatenablog.com/archive/category/%E7%9B%AE%E6%AC%A1%28Haskell%29

[7] A Gentle Introduction to Type Classes and Relations in Coq

[8] Type Classes for Mathematics in Type Theory

[9] https://coq.inria.fr/refman/addendum/program.html

 *)
