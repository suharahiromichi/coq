https://github.com/LPCIC/coq-elpi/tree/master/examples

の下にある example_XXXX.v を攻略するためのメモ


2023/1/7 @suharahiromichi

q


VSCodeでエラーになる場合は、VSCodeを再起動すること。

##  example_curry_howard_tactics.v

- intro ダクティクの実装例

- auto ダクティクの実装例


##  example_data_base.v

- Dbの一般的な使い方。


##  example_fuzzer.v

- fuzzer コマンド

与えられたプログラムの (?Op ?A ?B) を (AND ?A ?B) にするコマンドである。
実際の ?Op は OR が該当する。

テストの手法のひとつに、文法的に正しいが、意味の壊れたコード与えるという方法がある。
このテストのことをfuzzingまたはfuzz-testといい、
テストコードを生成するプログラムをfuzzerという。
CompCertでの証明の正しさを確かめるために、CSmithというfuzzerを使ったfuzzingを行った。

Software Fundation の後書きに、以下の記述がある；

In 2011, CompCert was included in a landmark study on fuzz-testing a
large number of real-world C compilers using the CSmith tool.


##  example_generalize.v

- generalize コマンド

Coq項{{1}} をλ変数にするコマンド。ただし結果はPrint。
項として与えるために、引数は``()``で囲むこと。

``(2) ====> (fun x => S x)``


##  example_import_projections.v

- import.projections コマンド

不明


##  example_record_expansion.v

- record.expand コマンド

引数をレコードのセレクタで分割する場合、それを展開する。

```
Example:
        Record r := mk { proj1 : T1; proj2 : T2 }.
        Definition f (x : r) := Body(proj1 x,proj2 x).

Is expanded to:
   Definition f1 v1 v2 := Body(v1,v2).
```

##  example_record_to_sigma.v

- UM.expand コマンド

レコードの定義の前につけると、レコードをネストしたsigma-typeで定義することができる。

sigma-type は、Strong dependent sum である sigT を使う。

```
Inductive sigT (A:Type) (P : A -> Type) : Type :=
    existT : forall x:A, P x -> sigT P.
```

実際は、Notationをつかって、``{x : A & (P x)} := sigT A P `` を使用する。


（参考：通常の exists は、sig であり、``P : A -> Prop`` であるところが違う。``{x : A | P x} := sig A P `` ）


##  example_reduction_surgery.v

- reduce タクティク

引数にモジュール名をとり、そこでの定義を展開する。

モジュールToRedの中の定義：

```
Module ToRed.
Definition x := 1.
Definition y := 1.
Definition alias := plus.
End ToRed.
```

```
ToRed.x + ToRed.y = (let z := 1 in S z)
----------------------------------------- elpi reduce "ToRed".
2 = (let z := 1 in S z)
```

## example_reflexive_tactic.v

- monoid タクティク (reflexive normalizer)

モノイド則によってゴールを変形する。
ringタクティクと異なり証明が終わらなくてもよい。


以上
