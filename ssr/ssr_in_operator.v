(**
\in 二項演算子 の右側が命題でもリストでもよいという不思議を調べてみる。

@suharahiromichi

2015/08/12
*)

Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq.
Require Import ssralg ssrnum ssrint.

Set Implicit Arguments.
Unset Strict Implicit.

Unset Printing Implicit Defensive.
Set Printing All.
Set Printing Coercions.

(**
\in の定義はひとつ。つまり、\inというラベルが使いまわされているわけではない。
 *)
Locate "_ \in _".                           (* @in_mem _ x (@mem _ _ A) *)

(**
しかし、右の引数は命題でもリストでもよい。
 *)
Check 2 \in [pred m : nat | m > 1].
Check 2 \in [:: 1; 2].

(**
``ssrbool.v`` にある \in の定義をもとに、自分で関数in'を定義してみる。
 *)
Definition in' :=
  fun (T : Type)  (S : predType T) (x : T) (A : S) => (@in_mem T x (@mem T S A)).
Check in' : forall (T : Type) (S : predType T), T -> S -> bool.

(**
つまり、第2引数Sが、第4引数(二項演算子\inの右)の型が決まることが判る。
 *)
Check in' 2 [pred m : nat | m > 1] : bool.
Check @in' nat (simplPredType nat) 2 [pred m : nat | m > 1] : bool.
Check [pred m : nat | m > 1] : simplPredType nat : predType nat.

Check in' 2 [:: 1; 2] : bool.
Check @in' nat (seq_predType nat_eqType) 2 [:: 1; 2] : bool.
Check [:: 1; 2] : seq_predType nat_eqType : predType nat.

(**
たしかに、``simplPredType nat`` と ``seq_predType nat_eqType`` とで切り替えられている。

``ssrbool.v`` にあるmem関数の定義から、
``simplPredType nat`` ないし ``seq_predType nat_eqType`` の memフィールドに、
mem関数の第3引数（``[pred m : nat | m > 1]`` ないし ``[:: 1; 2]``) が適用されたの
ものがmem関数の値になる。
*)

(**
``simplPredType nat`` の場合は、memフィールドがpred_of_simplなので、
*)
Check pred_of_simpl [pred m : nat | m > 1] : pred nat. (* nat -> bool *)

(**
``seq_predType nat_eqType`` の場合は、memフィールドがmem_seq（実際のmembership関数）なので、
*)
Check mem_seq [:: 1; 2] : pred nat_eqType.  (* nat_eqType -> bool *)
(* nat_eqTypeからnatへのコアーションが効いている。 *)

(**
``[pred m : nat | m > 1] : simplPredType nat`` は納得できるので、
次に問題になるのは、``[:: 1; 2] : seq_predType nat_eqType`` である。
*)

(**
コアーション：
*)
Print Graph.                                (* [pred_sort] : predType >-> Sortclass *)
(**
predTypeからTypeへのコアーションが有効なので、``seq_predType nat_eqType`` から ``seq nat``
へのコアーションがおこなわれることが判る。（もう少し詳しく）
 *)
Check [:: 1; 2] :                 seq_predType nat_eqType  : predType nat.
Check [:: 1; 2] : pred_sort      (seq_predType nat_eqType) : Type.
Check [:: 1; 2] : @pred_sort nat (seq_predType nat_eqType) : Type.


(**
カノニカル：
*)
Print Canonical Projections.                (* list <- pred_sort ( seq_predType ) *)
(**
seq_predType が predType のカノニカル・インスタンスになっているため、
第2引数にpredType型のseq_predTypeが指定されたとして、
そのコアーションのseq型が、第4引数に受け取ることができる。
 *)

(* END *)
