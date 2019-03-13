From mathcomp Require Import all_ssreflect.

(* total predicate ある型の要素についてすべてtrueを返す関数。 *)
Check fun _ => true.

(* これを母関数としてもつ型 *)

Inductive news : predArgType := n | e | w | s.

Check predArgType : Type.
Check Type : Type.

Check nat : Type.
Check nat : predArgType.

(* 任意の型を Type から predType に変換する。 *)
Check {: nat} : predArgType.


(* Applicative Predicate *)

(* Set Printing All. *)

Check SimplPred nat_eqType : simpl_pred nat. (* ************ *)

Goal SimplPred nat_eqType 1.
Proof.
  simpl.
  done.
Qed.

Goal [pred x | nat_eqType x] 1.
Proof.
  simpl.
  done.
Qed.

Check eq_op 1 =1 eq_op 1.

Goal 1 \in nat_eqType.
Proof.
  simpl.
  done.
Qed.


(* Collective Predicate の定義 *)

Fail Check (0,1) 1.
Fail Check mem (0,1) 1.
Fail Check 1 \in (0,1).
Fail Check (0,1) =i (0,1).


Section Pair.
  
  Variable T : eqType.
  
(*
  Coercion pred_of_eq_pair (s : T * T) : pred_class :=
    fun (x : T) =>  (s.1 == x) || (s.2 == x).
*)
  Coercion pred_of_eq_pair (s : T * T) : pred_class :=
    xpredU (eq_op s.1) (eq_op s.2).
  
  Canonical pair_predType := @mkPredType T (T * T) pred_of_eq_pair.
  
  Canonical mem_pair_predType := mkPredType pred_of_eq_pair.

End Pair.



Check mem (0,1)  : mem_pred nat_eqType.     (* ************ *)

Fail Check (0,1) 1.
Check mem (0,1) 1.
Check 1 \in (0,1).
Check (0,1) =i (0,1).


Compute mem (0,1) 1.
Compute 1 \in (0,1).

Compute 1 \in [predU (0,1) & (0,2)].        (* union *)
Compute 1 \in [predI (0,1) & (0,2)].        (* intersection *)
Compute 1 \in [predD (0,1) & (0,2)].        (* difference *)


Fail Check (0,1) =1 (0,1).                  (* applicative *)
Check mem (0,1) =1 mem (0,1).               (* applicative *)
Check (0,1) =i (0,1).                       (* collective *)


Check 1 \in {: nat}.
Fail Check 1 \in nat.

Goal 1 \in {: nat}.
Proof.
  rewrite /mem /Mem /xpredT.
  simpl.






Check 1 == 1.


Definition P (x : nat) := x == 1.

Check SimplPred P : simpl_pred nat.

Check SimplPred P.
Check predType nat.

Variable n : nat.

Check nat_eqType : pred nat.
Check {: nat} : pred nat.
Check mem [:: 1] : mem_pred nat.

Goal SimplPred P 1.
  simpl.

  Goal 1 \in [predI [::1] & [::1]].
    simpl.

  Goal n \in [pred x | nat_eqType x].
    simpl.
  
Goal SimplPred nat_eqType n.
  simpl.
Admitted.

Goal mem nat_eqType n.
  simpl.
Admitted.


Goal mem {: nat} 1.
  simpl.
Admitted.

Check nat_eqType : pred nat.
Check nat_eqType : simpl_pred nat.

Check SimplPred nat_eqType : pred nat.
Check SimplPred nat_eqType : simpl_pred nat.

Check mem nat_eqType : pred nat.
Check mem nat_eqType : simpl_pred nat.
Check mem nat_eqType : mem_pred nat.

  
Goal SimplPred {: nat} 1.
  simpl.
  Admitted.

Goal nat_eqType  =1 nat_eqType.

Goal {: nat} =1 {: nat}.

Goal [:: 1] =1 [:: 1].
  
  
Check mem P.
Goal mem P n.
  simpl.

About mem_pred.
Print mem_pred.

Check PredType.
Check 1 \in nat_eqType.

Goal nat_eqType 1 .
  simpl.
  
Goal mem nat_eqType 1 .
  simpl.
  simpl.
  
Check mem nat_eqType 1.
Check nat_eqType 1.
Check true \in {: bool}.
Check {: bool} true.

Set Printing All.
Check 1 \in nat_eqType.
Check mem nat_eqType 1.




Compute 1 \in nat_choiceType.

Goal forall (A B C D : Prop),  A \/ B /\ C /\ D -> True.
Proof.
  move=> A B C D.
  case=> [H1|[H2[H3]]].
  
  move=> [H1| H2].
  

Locate "_ \in _".
(* "x \in A" := in_mem x (mem A) : bool_scope (default interpretation) *)
About mem.
About in_mem.

Locate "_ >= _".
Goal 1 >= 0.

  Lemma test (m : nat)( n : bool) : True.
    move: n.
    move: m.
    move=> m.
    move=> n.
    
    move: m n.
    move=> m n.
    
    move=> n m.
    move: n.
    move: m.

  
Check mem P.

Check bool_eqType : eqType.
Compute Equality.sort bool_eqType.           (* nat *)

Check 1 \in nat_eqType.

Check 1 \in 'I_2.

Goal forall (m n : nat), True.
Proof.
  move=> m n.
  case: (leqP m n).
  case : leqP.

Check eqb_id.
Set Printing All.

Check eqb_id.
Variable a : nat.
Check a : nat_eqType.
Variable b : nat_eqType.
Check b : nat.
Check b.

Variable S' : {: bool}.
Variable s : S'.

Check 1 \in {: nat}.
Check mem {: nat}.
Check mem {: bool}.
Check P :  predArgType.
Check {: bool}  : predArgType.
Check [:: true] : predArgType.

Check mem [:: true].
Print mem.


Check mem_pred.
Check in_mem true.

Check mem [:: 1].
Locate "_ \in _".

Set Printing All.
Check mem [:: 1].
Check mem P.
Compute Equality.sort nat_eqType.
Check in_mem 1.

Check (mem P) : mem_pred nat.
Check (mem P).
(* @mem nat (predPredType nat) P *)

Check in_mem 1 : mem_pred nat -> bool.

Check in_mem 1 (mem [::]).

Check (mem [:: 1]).
(* @mem (Equality.sort nat_eqType) (seq_predType nat_eqType) (@cons nat (S O) (@nil nat)) *)
Check 1 \in [:: 1].


(* mathcomp/ssreflect 一式をインポートする。おすすめ。 *)

  (**

## 論理ゲーム(1)

### goalsウィンドウの説明

  X, Y : Prop
  XtoY_is_true : X -> Y
  X_is_true : X
  ============================
  Y

===== の上がコンテキストで、変数の型や、前提である名前のついた命題があります。

===== の下がゴールで、一般に A->B->C のかたちです。
最も外側の->の左(A)をスタックトップといいます。
->は右結合なので、A->(B->C)であることに注意してください。
ゴールが(A->B)->Cなら、(A->B)がスタックトップです。


### intro、generaralize、apply

- move=> H スタックトップを前提Hに移す。intro とも。
- move: H 前提Hをスタックトップに移す。generaralize とも。
- apply スタックトップをゴールの残りの部分に適用する。

- move: H1; apply; move=> H2 は apply: H1 => H2 とかける。


### 適用について (その1)

- ゴールへの適用
ゴールが Y のとき、 (X -> Y) を適用して X を得る。

- 前提への適用
前提 H1が (X -> Y)、前提 H2が X のとき、(H1 H2) は Y である。関数と同じ。

両者の違いは、同じ証明図を下から上のみるが、上から下にみるかの違いによる。

  X     X -> Y
---------------
             Y


### 適用について (その2)

- apply ゴールのスタックトップを残りの部分に適用する。通常は apply: H でつかう。

- apply/H ゴール全体への適用、ビュー付き。

- 前提を前提に適用する。 move: (H1 H2) など。括弧が必要。

- move/H スタックトップ（=前提）への適用、ビュー付き。


### 証明の終わり（ゴールの解消）

ゴールが A -> A になったらdone。
実際には、前提のどれかとゴールとが同じになったらでよい。


### Section セクション

Section のなかの宣言は、Section から出ると、

- Variable X : Prop は、forall (X : Prop), 。。。。
- Hypothesis H : X は、 X -> 。。。。 

Section の中では、最初から intro されているといえる。
   *)

Section ModusPonens.

  Variable X Y : Prop.

  Hypothesis XtoY_is_true : X -> Y.
  Hypothesis X_is_true : X.
  
  (* Goal を X -> Y にする例。 *)
  
  Theorem MP : Y.
  Proof.
    move: X_is_true.
      by [].                                (* done *)
  Qed.

  (* Goal を X にする例。 *)
  
  Theorem MP2 : Y.
  Proof.
    move: XtoY_is_true.
    apply.
      by [].                                (* done *)
  Qed.
  
  (* 一行にまとめられる。 *)
  Theorem MP2' : Y.
  Proof.
    apply: XtoY_is_true.
      by [].                                (* done *)
  Qed.
  
  (* おまけ *)
  Theorem MP2'': Y.
  Proof.
    debug auto.
    (* 
Debug: (* debug auto: *)
Debug: * assumption. (*fail*)
Debug: * intro. (*fail*)
Debug: * simple apply XtoY_is_true. (*success*)
Debug: ** assumption. (*success*)
     *)
  Qed.
  
  Check MP : Y.
  Check MP2 : Y.
  Check MP2' : Y.
  Check MP2'' : Y.
  
End ModusPonens.

(* セクションから出ると。 *)
Check MP : forall X Y : Prop, (X -> Y) -> X -> Y.
Check MP2 : forall X Y : Prop, (X -> Y) -> X -> Y.
Check MP2' : forall X Y : Prop, (X -> Y) -> X -> Y.
Check MP2'' : forall X Y : Prop, (X -> Y) -> X -> Y.

(* END *)
