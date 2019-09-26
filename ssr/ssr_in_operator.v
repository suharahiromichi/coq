Require Import mathcomp.ssreflect.ssreflect.
From mathcomp Require Import ssrbool ssrfun eqtype ssrnat div seq choice fintype.
From mathcomp Require Import finfun bigop finset.

(**
\in 二項演算子 の右側が命題でも、リストでも、集合でもよいという不思議を調べてみる。

@suharahiromichi

2015/08/12
2015/09/24
2019/09/24
*)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
(* Set Printing All. *)

(*
# 例

そのすべてが predType型のインスタンス型である(collective述語である)ことが判る。

(1) collective述語      predlPredType, simplPredType

(2) seq                 seq_predType, mem_seq_predType

(3) finType

(4) finset              set_predType

このほか、標準で以下がある。
- tuple_predType
- vector_predType
- bitseq_predType
- nat_pred_pred
*)

(**
## (1) collective述語
 *)
Section SectPred.
Variable T : Type.

(**
### ssrbool.v で定義
 *)
About pred_of_simpl.
Check @pred_of_simpl T : simpl_pred T -> pred T.

(* ********************************************* *)
About pred_of_mem.
Check @pred_of_mem T : mem_pred T -> predPredType T.
(* ********************************************* *)

(**
### predType型の型であること。
*)
Check [pred n : nat | n < 3] : predPredType nat. (* **** *)
Check [pred n : nat | n < 3] : simplPredType nat. (* **** *)

(**
### 素朴な使用例
*)
Compute id [pred n : nat | n < 3] 0.        (* true : bool *)
Compute pred_of_simpl [pred n : nat | n < 3] 0. (* true : bool *)

(* ********************************************* *)
Compute pred_of_mem (mem [:: 0; 1; 2]) 0.   (* true : bool *)
(* ********************************************* *)

(**
### カノニカル
*)
Check @mkPredType T (pred T) id : predType T.
Canonical predPredType := @mkPredType T (pred T) id.
Check predPredType : predType T.

Check @mkPredType T (simpl_pred T) (@pred_of_simpl T) : predType T.
Canonical simplPredType := @mkPredType T (simpl_pred T) (@pred_of_simpl T).
Check simplPredType : predType T.

(* ********************************************* *)
Check @mkPredType T (mem_pred T) (@pred_of_mem T) : predType T.
Canonical memPredType := @mkPredType T (mem_pred T) (@pred_of_mem T).
Check memPredType : predType T.
(* ********************************************* *)

(**
### \in の利用
*)
Compute 0 \in [pred n : nat | n < 3].       (* true : bool *)
Goal 0 \in [pred n : nat | n < 3].          (* true : bool *)
Proof. rewrite inE. done. Qed.              (* 0 < 3 *)

End SectPred.

(**
## (2) リスト (seq 型)
 *)
Section SectSeq.
Variable cT : Equality.type.

(**
### seq.v で定義
 *)
About mem_seq.                              (* シンプルなmember関数 *)
Check @mem_seq cT : seq cT -> cT -> bool.

About pred_of_eq_seq.                       (* これはなんのためにあるか？ *)
Check @pred_of_eq_seq cT : eqseq_class cT -> ssrbool.predPredType cT.

(**
### 素朴な使用例
*)
Compute mem_seq [:: 0; 1; 2] 0.             (* true : bool *)
Compute pred_of_eq_seq [:: 0; 1; 2] 0.      (* mem_seq を呼び出している。 *)

(**
### predType型の型であること。
*)
Check [:: 0; 1; 2] : seq nat.
Check [:: 0; 1; 2] : seq_predType nat_eqType. (* **** *)
Check [:: 0; 1; 2] : mem_seq_predType nat_eqType.

(**
### カノニカル
 *)
Check mem_seq_predType : forall T : eqType, predType T.
Canonical mem_seq_predType := @mkPredType cT (seq cT) (@mem_seq cT).
Check mem_seq_predType : predType cT.

Check seq_predType : forall T : eqType, predType T.
Canonical seq_predType := @mkPredType cT (seq cT) (@pred_of_eq_seq cT).
Check seq_predType : predType cT.


(**
### \in の利用
*)
Compute 0 \in [:: 0; 1; 2].                 (* true : bool *)
Goal 0 \in [:: 0; 1; 2].
Proof. rewrite inE. done. Qed.     (* (0 == 0) || (0 \in [:: 1; 2]) *)

End SectSeq.

(**
## (3) 有限型 (T : finType, P : Pred T なる P) または (T : finType なる T)
 *)
Section SectFinType.
  
(* (あ) 'I_5 は finType のインスタンスである。 *)
Goal 'I_5 = ordinal_eqType 5. Proof. done. Qed.

(* (い) 'I_5 は predArgType でもあるので、 *)
Check 'I_5 : predArgType.
Check pred_of_argType : forall T : predArgType, simpl_pred T.
Check pred_of_simpl   : forall T : Type, simpl_pred T -> pred T.
Check (fun T => pred_of_simpl (pred_of_argType T)) : forall T : predArgType, pred T.

(* (pred_of_simpl (pred_of_argType 'I_5)) は、pred 'I_5 型を持つ。 *)
Check pred_of_simpl (pred_of_argType 'I_5) : pred 'I_5. (* 'I_5 -> bool *)
Check pred_of_simpl                  'I_5  : pred 'I_5.
Check                pred_of_argType 'I_5  : pred 'I_5.
Check                                'I_5  : pred 'I_5.
Check pred_of_simpl (pred_of_argType bool_finType) : pred bool.
Check                                bool_finType  : pred bool.

(* (あ)(い) より、 T : finType, P : pred T なる P が、
   (pred_of_simpl (pred_of_argType 'I_5)) にあたる。 これが、mem の引数に書ける。 *)
(* さらに、pred_of_simpl と pred_of_argType も省略できるので、
   T : finType なる T を直接書ける。 *)

Variable i : 'I_5.
Compute mem (pred_of_simpl (pred_of_argType 'I_5)) i. (* true : bool *)
Compute mem (pred_of_simpl                  'I_5)  i. (* true : bool *)
Compute mem (               pred_of_argType 'I_5)  i. (* true : bool *)
Compute mem                                 'I_5   i. (* true : bool *)
Compute mem                           bool_finType true. (* true : bool *)

(* さらに mem も省ける。 *)
Compute (pred_of_simpl (pred_of_argType 'I_5)) i. (* true : bool *)
Compute (pred_of_simpl                  'I_5)  i. (* true : bool *)
Compute (               pred_of_argType 'I_5)  i. (* true : bool *)
Compute                                 'I_5   i. (* true : bool *)
Compute                           bool_finType true. (* true : bool *)

(**
### predType型の型であること。
*)
Check pred_of_simpl (pred_of_argType 'I_5) : predPredType 'I_5. (* **** *)
Check pred_of_simpl                  'I_5  : predPredType 'I_5. (* **** *)
Check                pred_of_argType 'I_5  : predPredType 'I_5. (* **** *)
Check                                'I_5  : predPredType 'I_5. (* **** *)
Check pred_of_simpl (pred_of_argType bool_finType) : predPredType bool. (* **** *)
Check                                bool_finType  : predPredType bool. (* **** *)

(**
### \in の利用
*)

Compute i \in pred_of_simpl (pred_of_argType 'I_5). (* true : bool *)
Compute i \in pred_of_simpl                  'I_5.  (* true : bool *)
Compute i \in                pred_of_argType 'I_5.  (* true : bool *)
Compute i \in                                'I_5.  (* true : bool *)

Goal i \in 'I_5.
Proof. rewrite inE. done. Qed.              (* true *)
  
Compute true \in                             bool_finType. (* true : bool *)
Goal true \in bool_finType.
Proof. rewrite inE. done. Qed.              (* true *)

End SectFinType.

(**
## (4) 有限集合 (finset 型)
 *)
Section SectSet.
Variable T : finType.
  
(**
### finset.v で定義
 *)
About pred_of_set.
Check pred_of_set : forall T : finType,
    set_type T -> fin_pred_sort (ssrbool.predPredType T).

(**
### 素朴な使用例
*)
Variable i : 'I_3.

Compute pred_of_set [set n | n in 'I_3] i.
Compute pred_of_set [set i] i.

(**
### predType型の型であること。
*)
Check [set i] : {set 'I_3}.
Check [set i] : {set ordinal_finType 3}.
Check [set i] : set_predType (ordinal_finType 3). (* **** *)

(**
### カノニカル
 *)
Check @mkPredType _ (unkeyed (set_type T)) (@pred_of_set T) : predType T.
Canonical set_predType T := @mkPredType _ (unkeyed (set_type T)) (@pred_of_set T).

(**
### \in の利用
*)
Compute i \in [set n | n in 'I_3].
Compute i \in [set i].
(* inE は使えない。 *)

End SectSet.

(**
# 説明各論
*)

(**
## mem の型
*)
Check @mem : forall (T : Type) (pT : predType T), pT -> mem_pred T.
(**
mem は、
第2引数にpredType Tのインスタンス。
第3引数 （これが \in の右の引数になる) に、その型の値をとる（これをcollective述語という）。

第1引数と第2引数は implicit なので、それを省略するためには、
第2引数（として解釈される型）は、predType T のカノニカル・インスタンスでないといけない。
 *)

(* (1) ssrbool.v の例 *)
Check [pred n : nat | n < 3] : pred nat.
(* ↑コアーション *) 
Check [pred n : nat | n < 3] : predPredType nat.

Check [pred n : nat | n < 3] : simpl_pred nat.
Check [pred n : nat | n < 3] : simplPredType nat.

(* 次が、predType nat でないことに注意 *)
Check 'I_3 : predPredType (ordinal 3).

(* (2) seq.v の例 *)
Check [:: 0; 1; 2] : seq nat.
Check [:: 0; 1; 2] : seq_predType nat_eqType.
Check [:: 0; 1; 2] : mem_seq_predType nat_eqType. (* XXX *)

(* (3) fintype.v の例 *)
(* 'I_3 === ordinal 3 *)
Check 'I_3 : predArgType.
Check 'I_3 : pred (ordinal 3).              (* pred 'I_3 === 'I_3 -> bool *)
Check 'I_3 : predPredType (ordinal 3).      (* predPTedType 'I_3 *)

Definition p0 : 'I_3. Proof. have : 0 < 3 by []. apply Ordinal. Defined.
Definition p1 : 'I_3. Proof. have : 1 < 3 by []. apply Ordinal. Defined.
Definition p2 : 'I_3. Proof. have : 2 < 3 by []. apply Ordinal. Defined.

(* (4) finset.v の例 *)
Check [set p0] : {set ordinal_finType 3}.
Check [set p0] : set_predType (ordinal_finType 3).
Check [set p0] : set_of_eqType (ordinal_finType 3). (* 直接関係ない？ *)
Check [set p0] : set_of_finType (ordinal_finType 3). (* 直接関係ない？ *)


(* ******************* *)
(* (3) の補足説明 ***** *)
(* ******************* *)

(**
memの第3引数にかけそうな型の例：
 *)
Section Sect2.

(* finType のインスタンスも predPredType であるから、書くことができる。  *)
Check bool_finType : finType.
Check bool_finType : predPredType bool.
(* 実際は、pred_of_argType などの壮大なコアーションである。 *)
(* Set Printing Coercions. *)
Check sort_of_simpl_pred
      (pred_of_argType (Equality.sort (Finite.eqType bool_finType)))
: pred_sort (predPredType bool).
(* わかりやすい範囲を抜き出すと、
eqTypeを経由して、finTypeからpredTypeに変換されている。 *)
Check pred_of_argType : forall T : predArgType, simpl_pred T.
Check Finite.eqType : finType -> eqType.
Check pred_of_argType (Finite.eqType bool_finType) :
  predPredType bool.

Check bool_finType : predPredType bool.
Goal mem bool_finType true. Proof. done. Qed.
(**
mem や \in や、enum に、
``T : finType`` なる T または、
``T : finType. P : pred T`` なる P が書ける、というのはこれに由来する。
 *)


(* ***** *)
(* ***** *)

Compute pred nat.                           (* nat -> bool *)
Compute simpl_pred nat.                     (* simpl_fun nat bool *)
Compute mem_pred nat.                       (* Mem ...  *)


(*
### 実は mem の結果も memPredType である。
 *)
Check mem [pred n : nat | n < 3] : mem_pred nat.
Check mem [pred n : nat | n < 3] : memPredType nat.
Check mem [:: 0; 1; 2] : mem_pred nat.
Check mem [:: 0; 1; 2] : memPredType nat.
Check mem 'I_3 : mem_pred (ordinal 3).
Check mem 'I_3 : memPredType (ordinal 3).

End Sect2.

(*
## \in の定義
*)

Definition in' :=
  fun (T : Type)  (S : predType T) (x : T) (A : S) =>
    (@in_mem T x (@mem T S A)).
Check in' : forall (T : Type) (S : predType T), T -> S -> bool.

(*
### mem 単独でなぜ動くか？
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
### in_mem はなにをしているか (その1 引数の順番の入れ替え)
 *)
Unset Printing All.
Print in_mem.
(* fun (T : Type) (x : T) => ((nosimpl pred_of_mem) T)^~ x *)
(* f ^~ x は、xをfの第2引数にわたし、第1引数をopenにしておくこと。 *)
Check in' 0 [:: 0; 1; 2].

(**
### in_mem はなにをしているか (その2 型の変換)
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
## \in の応用：
*)

Locate "_ =i _".                            (* (eq_mem (mem A) (mem B)) *)
Locate "_ @^-1: _".                         (* preimset f (mem A) *) (* f −1 (A) *)
Locate "_ @: _".                            (* imset f (mem A) *) (* f (A) *)
Locate "_ @2: ( _ , _ )".                   (* imset2 f (mem A) (fun _ =>mem B) *) (* f (A, B) *)

(**
実行例をつけること。
*)
Goal [:: 0; 1; 2] =i [pred n : nat | n < 3].
Proof.
  by case=> [|[|[]]].
Qed.
  

(**
## enum
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
## mem_seq の定義
*)

Fixpoint mem_seq' {T : eqType} (s : seq T) :=
  if s is y :: s' then xpredU1 y (mem_seq' s') else xpred0.

Compute mem_seq' [:: 0; 1; 2] 0.             (* true *)

(**
### xpredU1 の説明
 *)
Compute (xpredU1 0 (mem_seq' [:: 1; 2])) 0. (* 0 = 0 または、*)
Compute (xpredU1 0 (mem_seq' [:: 1; 2])) 1. (* (mem_seq' [:: 1; 2]) 1 が成り立つ。 *)

(**
### xpred0 の説明
*)
Compute xpred0 0.                           (* つねに false *)


(**
# 参考

SSReflect の ssrbool.v のコメント

However, we do define an explicit generic coercion 

``mem : forall (pT : predType), pT -> mem_pred T``
                       
where ``mem_pred T`` is a variant of ``simpl_pred T`` that preserves the infix syntax,
i.e., ``mem A x`` auto-simplifies to ``x \in A``.

以下。。
*)

(* END *)

Check [pick x in 'I_3 | p2.+1 == x].
Check [pred n | n < 3].
Check [pred n | n == p0].
Check [set n in [pred n | n == p0]].
Fail Check [set n in [pred n | n == 0]].

