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
Set Printing All.
Set Printing Coercions.

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
# mem は、第3引数 （これが \in の右の引数になる) に eqType 型をとる。

そのような型の例：
 *)
Section Sect2.
Check @mem.

(* ssrbool.v の例 *)
Check [pred n : nat | n < 3] : pred nat.
Check [pred n : nat | n < 3] : predPredType nat.

Check [pred n : nat | n < 3] : simpl_pred nat.
Check [pred n : nat | n < 3] : simplPredType nat.

(* seq.v の例 *)
Check [:: 0; 1; 2] : seq nat.
Check [:: 0; 1; 2] : seq_predType nat_eqType.
Check [:: 0; 1; 2] : mem_seq_predType nat_eqType. (* XXX *)

(* finset.v の例 *)
Check 'I_3 : predArgType.
Check 'I_3 : pred (ordinal 3).
Check 'I_3 : predPredType (ordinal 3).

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
# Backup
 *)

(* "\in" の説明のあるパッケージを網羅すること。 *)

Print predType.
Check mem_seq.
Compute mem_seq [:: 0; 1; 2] 1.
Check {mem | @isMem _ _ _ mem }.

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
(* -*- coding : utf-8 -*- *)

Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq fintype finfun.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Set Printing Coercions.                     (* コアーションを表示する。 *)

Section test_mem.
  
(* mem の定義 *)
Print predType.
(*
CoInductive mem_pred (T : Type) : Type :=
  Mem : pred T -> mem_pred T

Record predType (T : Type) : Type := PredType {
      pred_sort : Type;
      topred : pred_sort -> pred T;
      _ : {mem : pred_sort -> mem_pred T | isMem topred mem}
    }
 *)

Check @mem : forall (T : Type) (pT : predType T), pT -> mem_pred T.
Print mem.
Print mem_pred.

(* mem の説明 *)
(* mem の引数の順番は、A x で \in とは逆であることに注意。 *)
(* 第2引数 pT : predType T が、Aの型を決める。 *)
Check @mem : forall (T : Type) (pT : predType T), pred_sort pT -> mem_pred T.

Check 'I_3 : predArgType.
Check {set 'I_3 } : predArgType.
Check mem {set 'I_3 } : mem_pred _.
Check @mem _ _ {set 'I_3 } : predPredType _.
Check @mem _ _ {set 'I_3 } : memPredType _.
Check @mem _ _ {set 'I_3 } : mem_pred _.
Check @mem _ _ 'I_3 : mem_pred _.
Check mem 'I_3.
Check simpl_pred.
Compute (pred_of_simpl (@SimplFun bool bool xpred0)).
Compute (fun_of_pred (@SimplFun bool bool xpred0)).
About PredType.
Check exist.
About PredType.
About mkPredType.   (*  (pT -> T -> bool) を与える。 *)
(* mkPredType : forall T pT : Type, (pT -> T -> bool) -> predType T *)
Check pred_of_simpl : forall T : Type, simpl_pred T -> pred T.
Check mkPredType id.
Check mkPredType.
Check mkPredType pred_of_mem.
Check mkPredType pred_of_simpl.

Print mem_pred.

Check [:: 0; 1; 2] : seq_predType nat_eqType.
Check [:: 0; 1; 2] : mem_seq_predType nat_eqType.

Check @mem nat_eqType (seq_predType nat_eqType) [:: 0; 1; 2].
Check mem [:: 0; 1; 2] : mem_pred (Equality.sort nat_eqType).
Check mem [:: 0; 1; 2] : memPredType (Equality.sort nat_eqType).


Check [pred n : nat | n < 3] : simplPredType nat.
Check [pred n : nat | n < 3] : simpl_pred nat.
Check [pred n : nat | n < 3] : predPredType nat.
Check [pred n : nat | n < 3] : boolfunPredType nat.

Check @mem nat (simplPredType nat) [pred n : nat | n < 3].
Check mem [pred n : nat | n < 3] : mem_pred nat.
Check mem [pred n : nat | n < 3] : memPredType nat.




(* mem を使う例 *)
(* x \in A *)
(*
Definition in' (T : Type)  (S : predType T) (x : T) (A : S) :=
  (@in_mem T x (@mem T S A)).
*)
(* in_mem はあまり仕事していない。 *)
Print in_mem.
(*
fun (T : Type) (x : T) => ((nosimpl pred_of_mem) T)^~ x
     : forall T : Type, T -> mem_pred T -> bool
*)

Print pred_of_mem.
(*
fun (T : Type) (mp : mem_pred T) => let 'Mem p := mp in [eta p]
     : forall T : Type, mem_pred T -> pred_class

memの結果が、mem_pred なので、そこから Mem を剥がして pred_class にする。
*)
Check pred_of_mem (mem [:: 0; 1; 2]) : pred_class.
Check pred_of_mem (mem [:: 0; 1; 2]) : pred nat_eqType.
Check pred_of_mem (mem [:: 0; 1; 2]) : pred nat.

(* in_mem は、剥がしてできた pred 型の関数に、引数を摘要する（だけ） *)


Check (mem [:: 0; 1; 2]).
Compute pred_of_mem (mem [:: 0; 1; 2]) 1.
Compute pred_of_mem (mem [:: 0; 1; 2]) 4.


(* enum A *)
Definition enum' (T : finType) (S : predType T) (A : S) :=
  (@enum_mem T (@mem T S A)).

(* enum のほうも、in_mem が顔を出す。 *)
Print enum_mem.
(*
fun (T : finType) (mA : mem_pred (Finite.sort T)) =>
[seq x <- Finite.enum T | pred_of_simpl (pred_of_mem_pred mA) x]
     : forall T : finType, mem_pred (Finite.sort T) -> seq (Finite.sort T)
*)
Print pred_of_mem_pred.
(*
fun (T : Type) (mp : mem_pred T) => [pred x | in_mem x mp]
     : forall T : Type, mem_pred T -> simpl_pred T
*)


(*
\in の応用：
Notation "A =i B" := (eq_mem (mem A) (mem B)).


f @^-1: A        := preimset f (mem A)                (* f −1 (A) *)
f @: A           := imset f (mem A)                   (* f (A) *)
f @2: ( A , B )  := imset2 f (mem A) (fun _ =>mem B)  (* f (A, B) *)
*)

(* mem がなにをするか。 *)
Check mem [:: 0; 1; 2]     : mem_pred nat_eqType.
Check [pred n : nat | n < 3] : pred nat.
Check mem [pred n | n < 3] : mem_pred nat.

Compute mem [pred n | n < 3] 1.             (* true *)
Compute mem [pred n | n < 3] 4.             (* false *)
Compute mem [:: 0; 1; 2] 1.                 (* true *)
Compute mem [:: 0; 1; 2] 4.                 (* false *)

End test_mem.

(* 
 However, we do define an explicit generic coercion   

 mem : forall (pT : predType), pT -> mem_pred T                           
   where mem_pred T is a variant of simpl_pred T that preserves the infix   
   syntax, i.e., mem A x auto-simplifies to x \in A.                        



 Indeed, the infix "collective" operators are notation for a prefix         
 operator with arguments of type mem_pred T or pred T, applied to coerced   
 collective predicates, e.g.,                                               
      Notation "x \in A" := (in_mem x (mem A)).                             
 This prevents the variability in the predicate type from interfering with  
 the application of generic lemmas. Moreover this also makes it much easier 
 to define generic lemmas, because the simplest type -- pred T -- can be    
 used as the type of generic collective predicates, provided one takes care 
 not to use it applicatively; this avoids the burden of having to declare a 
 different predicate type for each predicate parameter of each section or   
 lemma.                                                                     
   This trick is made possible by the fact that the constructor of the      
 mem_pred T type aligns the unification process, forcing a generic          
 "collective" predicate A : pred T to unify with the actual collective B,   
 which mem has coerced to pred T via an internal, hidden implicit coercion, 
 supplied by the predType structure for B. Users should take care not to    
 inadvertently "strip" (mem B) down to the coerced B, since this will       
 expose the internal coercion: Coq will display a term B x that cannot be   
 typed as such. The topredE lemma can be used to restore the x \in B        
 syntax in this case. While -topredE can conversely be used to change       
 x \in P into P x, it is safer to use the inE and memE lemmas instead, as   
 they do not run the risk of exposing internal coercions. As a consequence  
 it is better to explicitly cast a generic applicative pred T to simpl_pred 
 using the SimplPred constructor, when it is used as a collective predicate 
 (see, e.g., Lemma eq_big in bigop).                                        
   We also sometimes "instantiate" the predType structure by defining a     
 coercion to the sort of the predPredType structure. This works better for  
 types such as {set T} that have subtypes that coerce to them, since the    
 same coercion will be inserted by the application of mem. It also lets us  
 turn any Type aT : predArgType into the total predicate over that type,    
 i.e., fun _: aT => true. This allows us to write, e.g., #|'I_n| for the    
 cardinal of the (finite) type of integers less than n.                     
   Collective predicates have a specific extensional equality,             
 *)
