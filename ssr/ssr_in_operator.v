(**
\in 二項演算子 の右側が命題でもリストでもよいという不思議を調べてみる。

@suharahiromichi

2015/08/12
2015/09/24
*)

Require Import ssreflect ssrbool.
Require Import ssrfun eqtype ssrnat seq.
Require Import ssralg ssrnum ssrint finset fintype.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
(* Set Printing All. *)

(**
## PredType のインスタンス
 *)
Section Sect1.
Variable T : Type.
About pred_of_simpl.
Check @pred_of_simpl T.

About pred_of_mem.
Check @pred_of_mem T.



(**
## ssrbool.v で定義
 *)
Check @mkPredType T (pred T) id.
Compute id [pred n : nat | n < 3] 0.
Canonical predPredType := @mkPredType T (pred T) id.
Check predPredType : predType T.

Check @mkPredType T (simpl_pred T) (@pred_of_simpl T).
Compute pred_of_simpl [pred n : nat | n < 3] 0.
Canonical simplPredType := @mkPredType T (simpl_pred T) (@pred_of_simpl T).
Check simplPredType : predType T.

Check @mkPredType T (mem_pred T) (@pred_of_mem T).
Compute pred_of_mem (mem [:: 0; 1; 2]) 0.
Canonical memPredType := @mkPredType T (mem_pred T) (@pred_of_mem T).
Check memPredType : predType T.

(*
## seq.v で定義
 *)
Variable cT : Equality.type.


About mem_seq.                              (* シンプルなmember関数 *)
Check @mem_seq cT.
Compute mem_seq [:: 0; 1; 2] 0.
Canonical mem_seq_predType := @mkPredType cT (seq cT) (@mem_seq cT).
Check mem_seq_predType : predType cT.

About pred_of_eq_seq.                       (* これはなんのためにあるか？ *)
Check @pred_of_eq_seq cT.
Compute pred_of_eq_seq [:: 0; 1; 2] 0.      (* mem_seq を呼び出している。 *)
Canonical seq_predType := @mkPredType cT (seq cT) (@pred_of_eq_seq cT).
Check seq_predType : predType cT.

End Sect1.

(**
# mem の型
*)
Check @mem : forall (T : Type) (pT : predType T), pT -> mem_pred T.
(**
mem は、
第2引数にpredType Tのインスタンス。
第3引数 （これが \in の右の引数になる) に、その型の値をとる（これをcollective述語という）。

第1引数と第2引数は implicit なので、それを省略するためには、
第2引数（として解釈される型）は、predType T のカノニカル・インスタンスでないといけない。
 *)

(**
memの第3引数にかけそうな型の例：
 *)
Section Sect2.

(* finType のインスタンスも predPredType であるから、書くことができる。  *)
Check bool_finType : finType.
Check bool_finType : predPredType bool.

Goal mem bool_finType true. Proof. done. Qed.
(**
mem や \in や、enum に、
``T : finType`` なる T または、
``T : finType. P : pred T`` なる P が書ける、というのはこれに由来する。
 *)

(* ssrbool.v の例 *)
Check [pred n : nat | n < 3] : pred nat.
(* ↑コアーション *) 
Check [pred n : nat | n < 3] : predPredType nat.

Check [pred n : nat | n < 3] : simpl_pred nat.
Check [pred n : nat | n < 3] : simplPredType nat.

(* 次が、predType nat でないことに注意 *)
Check 'I_3 : predPredType (ordinal 3).

(* seq.v の例 *)
Check [:: 0; 1; 2] : seq nat.
Check [:: 0; 1; 2] : seq_predType nat_eqType.
Check [:: 0; 1; 2] : mem_seq_predType nat_eqType. (* XXX *)

(* finset.v の例 *)
(* 'I_3 === ordinal 3 *)
Check 'I_3 : predArgType.
Check 'I_3 : pred (ordinal 3).              (* pred 'I_3 === 'I_3 -> bool *)
Check 'I_3 : predPredType (ordinal 3).      (* predPTedType 'I_3 *)

Definition p0 : 'I_3. Proof. have : 0 < 3 by []. apply Ordinal. Defined.
Definition p1 : 'I_3. Proof. have : 1 < 3 by []. apply Ordinal. Defined.
Definition p2 : 'I_3. Proof. have : 2 < 3 by []. apply Ordinal. Defined.

(* vector.v の例 *)
(* TBD *)

Compute pred nat.                           (* nat -> bool *)
Compute simpl_pred nat.                     (* simpl_fun nat bool *)
Compute mem_pred nat.                       (* Mem ...  *)


(*
## 実は mem の結果も memPredType である。
 *)
Check mem [pred n : nat | n < 3] : mem_pred nat.
Check mem [pred n : nat | n < 3] : memPredType nat.
Check mem [:: 0; 1; 2] : mem_pred nat.
Check mem [:: 0; 1; 2] : memPredType nat.
Check mem 'I_3 : mem_pred (ordinal 3).
Check mem 'I_3 : memPredType (ordinal 3).

End Sect2.

(*
# \in の定義
*)

Definition in' :=
  fun (T : Type)  (S : predType T) (x : T) (A : S) =>
    (@in_mem T x (@mem T S A)).
Check in' : forall (T : Type) (S : predType T), T -> S -> bool.

(*
## mem 単独でなぜ動くか？
*)
Check mem [:: 0; 1; 2] : mem_pred nat.
Print mem_pred.
Check Mem.

(* 
二重のコアーションを経て nat -> bool と解釈される。
 *)
Check (mem [:: 0; 1; 2]) : mem_pred nat.
Check (mem [:: 0; 1; 2]) : simpl_pred nat.
Check (mem [:: 0; 1; 2]) : pred nat.
Check (mem [:: 0; 1; 2]) : nat -> bool.
Check (pred_of_mem_pred (mem [:: 0; 1; 2])) : simpl_pred nat.
Check (pred_of_simpl (pred_of_mem_pred (mem [:: 0; 1; 2]))) : pred nat.
Check (pred_of_simpl (pred_of_mem_pred (mem [:: 0; 1; 2]))) : nat -> bool.

Compute (mem [:: 0; 1; 2]) 0.

(* 
## in_mem はなにをしているか (その1 引数の順番の入れ替え)
 *)
Unset Printing All.
Print in_mem.
(* fun (T : Type) (x : T) => ((nosimpl pred_of_mem) T)^~ x *)
(* f ^~ x は、xをfの第2引数にわたし、第1引数をopenにしておくこと。 *)
Check in' 0 [:: 0; 1; 2].

(**
## in_mem はなにをしているか (その2 型の変換)
*)

Check @in_mem nat : nat -> mem_pred nat -> bool.
(*
引数の順番を、mem_pred nat -> nat -> bool と入れ替えて考えると、
mem_pred nat 型の関数をもらって、nat -> bool の関数を返すことになる。
*)
Check in_mem 0 : mem_pred nat -> bool.

Check in_mem 0 (mem [:: 0; 1; 2]).
Compute in_mem 0 (mem [:: 0; 1; 2]).


(**
# \in の応用：
*)

(**
実行例をつけること。
*)

Locate "_ =i _".                            (* (eq_mem (mem A) (mem B)) *)
Locate "_ @^-1: _".                         (* preimset f (mem A) *) (* f −1 (A) *)
Locate "_ @: _".                            (* imset f (mem A) *) (* f (A) *)
Locate "_ @2: ( _ , _ )".                   (* imset2 f (mem A) (fun _ =>mem B) *) (* f (A, B) *)

(**
# enum
*)

(**
コアーションを省略せずに定義した場合
説明を補足すること。
*)

Definition enum_mem' (T : finType) (mA : mem_pred T) :=
  [seq x <- Finite.enum T | pred_of_simpl (pred_of_mem_pred mA) x].

Definition enum' (T : finType) (S : predType T) (A : S) :=
  (@enum_mem' T (@mem T S A)).

(**
# mem_seq の定義
*)

Fixpoint mem_seq' {T : eqType} (s : seq T) :=
  if s is y :: s' then xpredU1 y (mem_seq' s') else xpred0.

Compute mem_seq' [:: 0; 1; 2] 0.             (* true *)

(**
xpredU1 の説明
 *)
Compute (xpredU1 0 (mem_seq' [:: 1; 2])) 0. (* 0 = 0 または、*)
Compute (xpredU1 0 (mem_seq' [:: 1; 2])) 1. (* (mem_seq' [:: 1; 2]) 1 が成り立つ。 *)

(**
xpred0 の説明
*)
Compute xpred0 0.                           (* つねに false *)

(**
# 参考

SSReflect の ssrbool.v のコメント

 However, we do define an explicit generic coercion 
・mem : forall (pT : predType), pT -> mem_pred T                           
 where mem_pred T is a variant of simpl_pred T that preserves the infix syntax, i.e., mem
 A x auto-simplifies to x \in A.

以下。。
*)

(* END *)
