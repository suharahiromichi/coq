SCDマシンによる Backus' FPの実行

2021/08/08

@suharahiromchi


コピーは浅いコピーでよい。


## 基本操作

### ``sel n``の実行

- Dのリストのn番めの要素をSにpushする。


### ``constructor``の実行

以下をn回繰り返す。

- Dをコピーする。
- 実行して結果をSにpushする。
- Dを捨てる。

- Sの個数分popしてリストをつくり、Sにpushする。


### ``conposition`` の「p ○」実行

- Dを捨てる。                             (conpos)
- SをpopしてDに置く。                     (conpos)
- pを実行する。                           (conpos)


### ``condition p1 p2 p3``

- Dをコピーする。
- p1 を実行して、結果をSにpushする。
- Dを捨てる。

- Dをコピーする。
- Sをpopしてtrueならp1, falseならp2を実行する。
- Dを捨てる。



### 組込関数、定義関数

- Dを参照する。1引数ならD全体が引数である。
- Sのトップに結果をpushする。



## 応用操作

### ``slash p : <o1, o2,.., on-1, on> = p・[sel 1, p・[sel 2, sel 3]]``

Dが3個のリストの場合

- Dをコピーする。                       (constr1)
- sel1 を実行してSにpushする。           (constr1)
- Dを捨てる。                            (constr1)

- Dをコピーする。                       (constr1)

- Dをコピーする。                               (constr2)
- sel2 を実行してSにpushする。                  (constr2)
- Dを捨てる。                                   (constr2)

- Dをコピーする。                               (constr2)
- sel3 を実行してSにpushする。                  (constr2)
- Dを捨てる。                                   (constr2)

- Sの二つをpppして、consしてpushする。          (constr2)

- Dを捨てる。                                           (consps2)
- SをpopしてDに置く。                                   (conpos2)
- pを実行してSにpushする。                              (consps2)

- Dを捨てる。                            (constr1)
- Sの二つをpppして、consしてpushする。   (constr1)

- Dを捨てる。                            (compos1)
- SをpushしてDに置く。                   (compos1)
- pを実行する。                          (compps1)


# ``alpha p : <o1, o2,.., on> = [p・sel 1, p・sel 2,..., p・sel n]

Dがn個のリストの場合

- Dをコピーする。                       (constr)
- sel 1を実行する。                     (constr)

- Dを捨てる。                           (comps)
- Sのトップ(sel 1の結果)を Dに置く。     (comps)
- pを実行する。                         (comps)

- Dを(sel 1の結果)捨てる。              (constr)

繰り返す

- Sの個数分popしてリストをつくり、Sにpushする。(constr)


## 

以上
