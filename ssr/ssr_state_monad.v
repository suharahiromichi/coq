(** The Hoare State Monad - Proof Pearl, Wouter Swierstra *)
(** その前半部分 State Monad *)
(* @suharahiromichi 2014_01_13 *)

From mathcomp Require Import ssreflect ssrbool ssrnat seq eqtype.
From mathcomp Require Import ssrfun.
Require Import String.                      (* Error *)
Require Import Program.                     (* Program *)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Inductive Tree (a : Set) : Set :=
| Leaf : a -> Tree a
| Node : Tree a -> Tree a -> Tree a.

Fixpoint relabel' (a : Set) (t : Tree a) (s : nat) : Tree nat * nat
  :=
    match t with
      | Leaf _ =>
        (Leaf s, s.+1)
      | Node l r =>
        let (l , s ) := relabel' l s in
        let (r , s ) := relabel' r s in
        (Node l r , s )
   end.

Section state_monad.

Variable st : Set.
  
Definition State (a : Set) : Type :=
  st -> a * st.

Definition ret {a : Set} : a -> State a := fun x s => (x , s).

Definition bind {a b : Set} : State a -> (a -> State b) -> State b
  := fun c1 c2 s1 =>
       let (x , s2 ) := c1 s1 in c2 x s2 .

Definition bind2 {a b : Set} : State a -> State b -> State b
  := fun p1 p2 =>
       bind p1 (fun _ => p2).               (* p1 >>= (fun _ => p2) *)

Definition get : State st :=
  fun s => (s, s).

Definition put : st -> State unit :=
  fun s _ => (tt, s).

End state_monad.
Infix ">>=" := bind (right associativity, at level 71).
Infix ">>>" := bind2 (right associativity, at level 71).

Fixpoint relabel {a : Set} (t : Tree a) : State nat (Tree nat)
  :=
    match t with
      | Leaf _ =>
        @get nat >>=
            fun n => @put nat n.+1 >>>
                          ret (Leaf n)
      | Node l r =>
        relabel l >>=
        fun l => relabel r >>=
                 fun r => ret (Node l r)
    end.

(* END *)
