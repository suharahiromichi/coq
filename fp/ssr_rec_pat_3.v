(* -*- coding: utf-8 -*- *)
From mathcomp Require Import all_ssreflect.
Require Import Coq.Lists.Streams.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(**
Dynamorphism 概論 - https://45deg.github.io/rogyAdC2015/

Recursion Schemes - https://scrapbox.io/haskell-shoen/Recursion_Schemes
*)
(**
# fold - catamorphism
 *)

Section Catamorphism.

  Variable A B : Type.
  
  Fixpoint cataNat (b : B) (f : B -> B) (n : nat) : B :=
    match n with
    | O => b
    | S n' => f (cataNat b f n')
    end.

  Fixpoint cataList (b : B) (f : A -> B -> B) (s : seq A) : B :=
    match s with
    | [::] => b
    | a :: a' => f a (cataList b f a')
    end.

  Inductive Tree :=
  | FNode of Tree & Tree
  | FLeaf of B.

  Fixpoint cataTree (f : B -> B -> B) (t : Tree) : B :=
    match t with
    | FNode m n => f (cataTree f m) (cataTree f n)
    | FLeaf x => x
    end.
End Catamorphism.

(**
## コンストラクタ S の消費
 *)
Section ExampleCatamorphism.
(**
### Nat→Int
 *)
  Definition natInt := cataNat 0 succn.
  Compute natInt 10.                        (* 10 *)
(**
### 加算
 *)
  Definition add n := cataNat n succn.
  Compute add 2 3.                          (* 5 *)

(**
### 乗算
*)
  Definition mul n := cataNat 0 (add n).
  Compute mul 2 3.                          (* 6 *)

(**
## コンストラクタ cons の消費

### リストの和
 *)
  Definition sgma := cataList 0 addn.
  Compute sgma [:: 1; 2; 3].                (* 6 *)

(**
### リストの積（階乗）
*)
  Definition pai := cataList 1 muln.
  Compute pai [:: 2; 3; 4].                 (* 24 *)

(**
## コンストラクタ node の消費

### fibAsHylo の後半
 *)
  Definition fibAsHylo2 := cataTree addn.
  Compute fibAsHylo2 (FNode (FNode (FLeaf 0) (FLeaf 1)) (FLeaf 1)). (* 2 *)

(**
# fold - Histomorphism

## コンストラクタ S の消費

### fibAsHist
*)
  Fixpoint fibAsHist' s n :=                (* 汎関数でない。XXXX *)
    match n with
    | 0 => s
    | n'.+1 => match s with
               | m :: n :: _ => fibAsHist' (m + n :: s) n'
               | _ => s
               end
    end.
  Definition fibAsHist m := head 0 (fibAsHist' [:: 1; 0] m.-1).
  Compute fibAsHist 10.

(**
# unfold - anamorphism
 *)
Section Anamorphism.

  Variable A B : Type.
  
  Fixpoint anaList (h : nat) (f : A -> A) (a : A) : seq A :=
    match h with
    | 0 => [::]
    | h'.+1 => a :: (anaList h' f (f a))
    end.

  Fixpoint amoList (h : nat) (f : A * B -> A * B) (b : A * B) : seq A :=
    match h with
    | 0 => [::]
    | h'.+1 => let x := f b in x.1 :: (amoList h' f x)
    end.

End Anamorphism.

Section ExampleAnamorphism.
(**
## コンストラクタ cons の生成

### iota (有限版)
 *)
  Definition iota h := anaList h succn 1.
  Compute iota 10.          (* = [:: 1; 2; 3; 4; 5; 6; 7; 8; 9; 10] *)

(**
### fact.

TBD これは具体例なし。XXXXX
*)          

(**
### fib (有限版)
*)          
  Definition fibAsAmo h := amoList h (fun a => let (x, y) := a in (y, x + y)) (0, 1).
  Compute fibAsAmo 10.   (* = [:: 1; 1; 2; 3; 5; 8; 13; 21; 34; 55] *)
  (* 無限版は、 ssr_rec_pat_2.v を参照のこと。 *)
    
(**
## コンストラクタ node の生成

### fibAsHylo の前半
 *)
  Definition psi n := (n.-2, n.-1).
  Fixpoint fibAsHylo1 h x :=                (* 汎関数でない。XXXX *)
    match h with
    | 0 => FLeaf x
    | h'.+1 =>
      match psi x with
      | (0, n) => FLeaf n
      | (1, n) => FLeaf n
      | (m, n) => FNode (fibAsHylo1 h' m) (fibAsHylo1 h' n)
      end
    end.
  Compute fibAsHylo1 10 5.
  
End ExampleAnamorphism.

Section Example.
(**
# unfold-fold - hylomorphism

## コンストラクタ cons

### 階乗
*)
  Definition factAsHylo := pai \o iota.
  Compute factAsHylo 5.                     (* 120 *)

(*
## コンストラクタ node

### fibAsHylo
*)
  Definition fibAsHylo x := fibAsHylo2 (fibAsHylo1 100 x).
  Compute fibAsHylo 10.                     (* 55 *)
  
End Example.

(* END *)
