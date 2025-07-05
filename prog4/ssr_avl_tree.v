(**
AVL Tree

https://zenn.dev/blackenedgold/books/introduction-to-idris/viewer/dependent-avl-tree
*)
From Equations Require Import Equations.
From mathcomp Require Import all_ssreflect.
From mathcomp Require Import ssrZ zify ring lra.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(**
# 依存型を使ったAVL木の定義
*)
Section t.

  Variable a : Type.
  
  Inductive Balance : nat -> nat -> nat -> Type :=
  | Lefty  n : Balance n.+1 n.+2 n
  | Mid    n : Balance n    n.+1 n
  | Righty n : Balance n    n.+2 n.+1.
  (*                   左の木の高さ *)
  (*                        全体の木の高さ *)
  (*                             右の木の高さ *)

  Inductive Tree : nat -> Type :=
  | Leaf : Tree 0
  | Node l n r : Balance l n r -> Tree l -> a -> Tree r -> Tree n.

End t.

(**
# AVL木の簡単な操作
 *)
Section s.

  Variable a : Type.
  Variable x : a.
  
  Check Leaf a : Tree a 0.
  Check Node _ (Node _ _ _ _) _ (Node _ _ _ _) : Tree _ _.

  Definition empty := Leaf a.
  Check empty : Tree a 0.

  Definition singleton x := Node (Mid 0) empty x empty.
  Check singleton : a -> Tree a 1.
  Inductive Ord :=
  | LT
  | EQ
  | GT.
  
  Check empty : Tree a 0.
  
  Check Leaf _ : Tree a _.
  Check Node _ _ _ _ : Tree a _.
  
  Fixpoint member (n : nat) (cmp : a -> a -> Ord) (x : a) (t : Tree a n) : bool :=
    match t with
    | Leaf => false
    | Node l _ r _ tl v tr =>
        match (cmp x v) with
        | LT => member cmp x tl
        | EQ => true
        | GT => member cmp x tr
        end
    end.

End s.

Section n.

  Definition compare x v :=
    if (x < v) then LT else if (x == v) then EQ else GT.

  Check @member nat 0 compare 1 (empty nat).
  Check member compare 1 (empty nat).
  Compute member compare 1 (empty nat).     (* false *)
  Compute member compare 1 (singleton 1).   (* true *)
  
End n.

(**
# AVL木への挿入
 *)
Section s.
  
  Variable a : Type.
  Variable x y : a.

  Definition createR {n : nat} := @Node a n    n.+2 n.+1 (Righty n).
  Definition createM {n : nat} := @Node a n    n.+1 n    (Mid n).
  Definition createL {n : nat} := @Node a n.+1 n.+2 n    (Lefty n).

  Section n.
    Variable n : nat.
    
    Check createR : Tree a n -> a -> Tree a n.+1 -> Tree a n.+2.
    Check createM : Tree a n -> a -> Tree a n -> Tree a n.+1.
    Check createL : Tree a n.+1 -> a -> Tree a n -> Tree a n.+2.
  End n.

  Check createR (empty a) x (singleton y).
  Check createM (empty a) x (empty a).
  Check createL (singleton y) x (empty a).
  
  
(* END *)

