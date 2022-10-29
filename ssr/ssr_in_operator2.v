(**
Coq/SSReflect/MathComp の \in 演算子の不思議を納得する
===================

@suharahiromichi

2022/10/23
*)

(**
MathComp の``\in``は、``∈``の意味の二項演算子ですが、右側にはリストでも、集合でも、
型でも、命題でもよいという万能選手です。ここでは、その万能性を実現するしくみを調べて
みます。
また、MathCompの型クラスの機能をつかって、``\in``の右に書ける型を増やしてみます。

このファイルは以下にあります。

https://github.com/suharahiromichi/coq/blob/master/ssr/ssr_in_operator2.v

CoqとMathCompのバージョンは以下の通りです。
```
coq                     8.16.0
coq-mathcomp-ssreflect  1.15.0
```
*)

(**
# 準備

いつも通りにSSReflectをインポートし、
いつものお約束通り、Coqの引数の省略を許します。
*)
From mathcomp Require Import all_ssreflect.
Set Implicit Arguments.                  (* Coqの引数の省略を許す。 *)

(**
省略された引数とコアーションを表示しないようにします。
いずれもディフォルト（省略時解釈）ですが、
今回はこれを切り替えることがあるかもしれないので、最初に明示しておきます。
*)
Unset Printing Implicit.            (* 省略された引数を表示しない。 *)
Unset Printing Coercions.           (* コアーションを表示しない。 *)
Set Printing Notations.             (* Notationを展開しません。 *)

(**
# ``\in``演算子の使用例
*)
Compute 1 \in [:: 1; 2].                    (* リスト *)
Compute 1 \in [tuple 1; 2].                 (* タプル *)
Compute true \in [set true].                (* 有限集合 *)
Compute 1 \in [pred n | n < 3].             (* 命題 *)
Compute 1 \in nat_eqType.                   (* 型 *)

(**
# ``\in``演算子の定義

Locate コマンドを使ってしらべると、``in_mem``と``mem``のふたつの関数で構成されています。
ここで注意すしないといけないのは、``\in``は、スコープで切り替えられる複数の演算子ではな
いことです。
*)
Locate "_ \in _".       (* Notation "x \in A" := (in_mem x (mem A)) *)

(**
これでは、x と A の型が判らないので、以下を試してみると、
*)

Check _ \in _.
(**
```
?x \in ?A : bool
where
?T : [ |- Type]
?x : [ |- ?T]
?pT : [ |- predType ?T]
?A : [ |- pred_sort ?pT]
```  

となり、``T``と``pT``のふたつの型が与えられていることが判ります。
``pred_sort``の説明はあとでしますが、
とりあえず、``x``は任意の型``T``、``A``は``pT``型で、
その``pT``は``predType T``型と思ってください。


これをもとに``x``の型と``A``の型を与えてると、次のようになります。
*)
Check fun (T : Type) (pT : predType T) (x : T) (A : pred_sort pT) =>
        x \in A.

(**
さらに、``\in``を構成する``in_mem``と``mem``の先頭に``@``をつけてみると次のようになり、
``T``も``pT``も``in_mem``と``mem``に与えられていることが判ります。
*)
(*
Set Printing Coercions.
Set Printing Implicit.
Unset Printing Notations.
*)
Check fun (T : Type) (pT : predType T) (x : T) (A : pred_sort pT) =>
        @in_mem T x (@mem T pT A).

(**
# ``predType T``型の定義

``\in``を使うには、``predType T``型が必要だとわかったので、調べてみます。
``predType T``型は、``eqType``型などと同様のMathCompの型クラスです。
型クラスなので、``pT : predType T``なる``pT``は、型インスタンスとなります。

``predType``の実体はStructureで定義される構造体
で、``theories/ssr/ssrbool.v``で、以下のように定義されています。
（改行を変更。また、``pred T = T -> bool``を展開しています。）

(注1) Coqでは、RecordとStructureは同じコマンドです。

(注2) mathcomp/ssreflect/ssrbool.v から、Coq本体のコードツリーに移動されました。

```
Record predType (T : Type) : Type :=
  PredType {
      pred_sort :> Type;
      topred : pred_sort -> T -> bool
  }.
```

これは次のように読みます：

構造体 predType は、型引数``T : Type``をとり、``pred_sort``
と``topred``のふたつのメンバーを持つ。

- ``pred_sort``は、この型の元になる任意の型で、``T``とは無関係です。
ここでは勝手に「台」と呼ぶことにします。
また、``:>``は、``predType T``のインスタンスから「台」のへの型強制（コアーション）が
有効になることを意味します。コアーションは``pred_sort``で行われます。

- ``topred``は、to pred で、「台」と``T``から``bool``型を求めるbool述語ですが、
「台」を``T -> bool``型に変換する関数とも取れるので、以下「変換関数」と呼びます。

このふたつから、``predType T``型のインスタンスを作ることができます。
「台」から``predType T``を求める必要があるので、Coqのカノニカルとして、
（Definitionではなくて）Canonicalコマンドで定義します。
*)  

(**
# ``predType T``型のインスタンスの例

理解の早道は実際に作ってみることなので、やってみましょう。
``predType T``型を実際に作って、``\in``で使えるかためしてみましょう。

直積型(Prod型、Pair)のどちらかならtrueを変返すものを考えます。
例えば次のような例ですが、まだ定義ができていないので、単純のエラーになります。
*)

Fail Compute 1 \in (1, 2).                  (* true *)
Fail Compute 3 \in (1, 2).                  (* false *)

(**
- 「台」は、直積型(Prod型、Pair)とします。
ただし、fstとsndが別の型だと意味がないので、``T * T``とします。

- 「変換関数」は、
``x``がのfstかsndかのどちらかの要素に含まれているかを判定するので、
次のようになります。``==``を使うために``T``は``eqType``にします。
*)
Definition pred_of_eq_pair (T : eqType) (A : T * T) : (T -> bool) :=
  fun (x : T) => (A.1 == x) || (A.2 == x).

(**
「変換関数」単独で動作を確認します。
*)
Compute pred_of_eq_pair nat_eqType (1, 2) 1. (* true *)
Compute pred_of_eq_pair nat_eqType (1, 2) 3. (* false *)

(**
Canonicalコマンドで定義します。
*)
Canonical pair_predType (T : eqType) :=
  {| pred_sort := T * T; topred := pred_of_eq_pair T |}.

(**
PredType を使って定義することもできます。
```
Canonical pair_predType (T : eqType) := @PredType T (T * T) (pred_of_eq_pair T).
```
*)

(**
「台」へのコアーションも機能しています。
*)
Compute pred_sort (pair_predType nat_eqType). (* (nat * nat) *)
Check (1, 2) : (nat * nat).
Check (1, 2) : pair_predType nat_eqType.

(**
所望の動作をしているようです。
*)
Compute 1 \in (1, 2).                       (* true *)
Compute 3 \in (1, 2).                       (* false *)

(**
補足説明：

``pred_of_eq_pair T``を``T : eqType``で定義したため、
``pair_predType T``も``T : eqType``になりますが、
``predType T``の``T``については、eqTypeのコアーションが効いて、``Equality.sort T``
になり、問題ありません。
 *)
(*
(* Set Printing Coercions. *)
Canonical pair_predType (T : eqType) :=
  {| pred_sort := (Equality.sort T) * (Equality.sort T); topred := pred_of_eq_pair T |}.
Check pair_predType : forall (T : eqType), predType (Equality.sort T).
 *)
  
(**
補足説明：

(1) ``\in``の定義に引数をもれなく与えてみます。
*)
Check (fun (T : Type) (pT : predType T) (x : T) (A : pred_sort pT) =>
         @in_mem T x (@mem T pT A))
      nat_eqType
      (pair_predType nat_eqType)
      1
      (1, 2).
(**
(2) ``T``に``nat_eqType``を展開してみます。コアーションが起きます。
*)
Check (fun (pT : predType (Equality.sort nat_eqType))
           (x : Equality.sort nat_eqType) (A : pred_sort pT) =>
         @in_mem nat_eqType x (@mem nat_eqType pT A))
      (pair_predType nat_eqType)
      1
      (1, 2).
(**
(2') ``predType``の引数や``x``の型のコアーションを計算すると、``nat``になります。
*)
Check (fun (pT : predType nat) (x : nat) (A : pred_sort pT) =>
         @in_mem nat_eqType x (@mem nat_eqType pT A))
      (pair_predType nat_eqType)
      1
      (1, 2).
(**
(3) ``pT``を展開します。
*)
Check (fun (x : nat) (A : pred_sort (pair_predType nat_eqType)) =>
         @in_mem nat x (@mem nat (pair_predType nat_eqType) A))
      1
      (1, 2).
(**
(3') ``A``の型のコアーションを計算すると、
``pred_sort (pair_predType nat_eqType))``が``(nat * nat)``になります。
*)
Check (fun (x : nat) (A : (nat * nat)) =>
         @in_mem nat x (@mem nat (pair_predType nat_eqType) A))
      1
      (1, 2).
(**
(4) のこりの値も展開します。それでも、``@mem``の第2引数は``predType T``型が必要です。
*)
Check @in_mem nat 1 (@mem nat (pair_predType nat_eqType) (1, 2)).

(**
# MathCompで定義済みの``predType T``のインスタンス型

既成の``predType T``のインスタンス型を見てみます。
前述のとおり、``predType T``のインスタンス型が、
``pred_sort``のついての正準解になっていることから、
``Canonical Projections`` から``pred_sort``を拾うことで
見つけられます。ここで説明しやすい、いくつかを以下にしめします。
*)

Print Canonical Projections.
(**
```
seq        <- pred_sort ( seq_predType )
tuple_of   <- pred_sort ( tuple_predType )
pred       <- pred_sort ( predPredType )
simpl_pred <- pred_sort ( simplPredType )
```
 *)

(* Set Printing Coercions. *)

(**
## seq_predType

- 「台」seq T
- 「変換関数」pred_of_seq
 *)
Print seq_predType.                         (* 定義 *)
Check [:: 1; 2] : seq nat.                  (* 「台」 *)
Check 1 \in [:: 1; 2].                      (* \in の例 *)
Compute 1 \in [:: 1; 2].                    (* \in の例 *)
Check [:: 1; 2] : seq_predType nat_eqType.
Check seq_predType nat_eqType : predType nat_eqType. (* predType のインスタンス型 *)

(**
## tuple_predType

- 「台」n-tuple T
- 「変換関数」pred_of_seq (tval s))

tval でseqに変換して、pred_of_seq を適用する。
*)
Print tuple_predType.                       (* 定義 *)
Check [tuple 1; 2] : 2.-tuple nat.          (* 「台」 *)
Check 1 \in [tuple 1; 2].                   (* \in の例 *)
Compute 1 \in [tuple 1; 2].                 (* \in の例 *)
Check [tuple 1; 2] : tuple_predType 2 nat_eqType.
Check tuple_predType 2 nat_eqType : predType nat_eqType. (* predType のインスタンス型 *)

(**
## set_predType

``set <- pred_sort ( set_predType )`` がないことから、
これについては、別なメカニズムが働いてると思われる。
ここの記述は不正確かもしれない。

- 「台」set_type T（有限集合）
- 「変換関数」pred_of_set
*)
Print set_predType.                         (* 定義 *)
Check [set true] : set_type bool_finType. (* {set bool} *) (* 「台」 *)
Check true \in [set true].                  (* \in の例 *)
(*
  コアーションを表示すると、
  true \in pred_of_set [set true]
  になっている。変換関数がコアーションに出てくるのはおかしいので、

 *)
Compute true \in [set true].                (* \in の例 *)
Check [set true] : set_predType bool_finType.
Check set_predType bool_finType : predType bool_finType. (* predType のインスタンス型 *)

(**
## predPredType

- 「台」pred T（bool述語、T -> bool）
- 「変換関数」id
 *)
Print predPredType.                         (* 定義 *)
Check [pred n : nat | n < 3] : pred nat.    (* 「台」 *)
Check 1 \in [pred n : nat | n < 3].         (* \in の例 *)
Compute 1 \in [pred n : nat | n < 3].       (* \in の例 *)
Check [pred n : nat | n < 3] : predPredType nat.
Check predPredType nat : predType nat. (* predType のインスタンス型 *)

(**
## simplPredType

- 「台」simpl_pred T
- 「変換関数」pred_of_simpl
 *)
Print simplPredType.                               (* 定義 *)
Check (pred_of_argType nat_eqType) : simpl_pred nat. (* 「台」 *)

(* 趣旨から、\in の右には型を直接書きますが、 *)
Check 1 \in nat_eqType.                     (* \in の例 *)
(* ここの``\in``の右に関しては、コアーションが効いていることに注意してください。 *)
Check nat_eqType : predArgType.
Check pred_of_argType : forall T : predArgType, simpl_pred T.
(* コアーションの説明終わり。 *)

Check 1 \in (pred_of_argType nat_eqType).   (* \in の例 *)
Compute 1 \in (pred_of_argType nat_eqType). (* \in の例 *)
Check (pred_of_argType nat_eqType) : simplPredType nat.
Check simplPredType nat : predType nat. (* predType のインスタンス型 *)

(**
# ``mem``と``in_memの``中身

最後に``mem``と``in_memの``中身をみてみます。
*)

Print mem.
(**
```
fun (T : Type) (pT : predType T) =>
let '{| pred_sort := pred_sort0; topred := toP |} as pT0 :=
     pT return (pT0 -> mem_pred T) in
fun A : {| pred_sort := pred_sort0; topred := toP |} => Mem (T:=T) [eta toP A]
     : forall (T : Type) (pT : predType T), pT -> mem_pred T
```
memの定義は複雑なように見えますが、``predType T``型のインスタンスに
含まれる「変換関数」を``toP``として取り出して、実行しているのが判ります。
*)

Print in_mem.
(**
```
fun (T : Type) (x : T) => pred_of_mem^~ x
     : forall T : Type, T -> mem_pred T -> bool
```
これに対して、in_memは、pred_of_memで型を変換して、
引数の順番を入れ替えているだけのようです。
*)
Check @pred_of_mem : forall T : Type, mem_pred T -> {pred T}.
Check @pred_of_mem : forall T : Type, mem_pred T -> predPredType T.

(**

# まだ説明していないもの

## in_mem 内部使用

```
mem_pred   <- pred_sort ( memPredType )
```

## 他の型

```
bseq_of    <- pred_sort ( bseq_predType )
nat_pred   <- pred_sort ( nat_pred_pred )
bitseq     <- pred_sort ( bitseq_predType )
forall _, _ <- pred_sort ( boolfunPredType )
```
 *)

(* END *)
