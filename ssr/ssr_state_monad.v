(** The Hoare State Monad - Proof Pearl, Wouter Swierstra *)
(** その前半部分 State Monad *)
(* @suharahiromichi 2014_01_13 *)

Require Import ssreflect ssrbool ssrnat seq eqtype.
Require Import ssrfun.
Require Import String.                      (* Error *)
Require Import Program.                     (* Program *)

Inductive Tree (a : Set) : Set :=
| Leaf : a -> Tree a
| Node : Tree a -> Tree a -> Tree a.

Implicit Arguments Leaf [[a]].
Implicit Arguments Node [[a]].

Fixpoint relabel' (a : Set) (t : Tree a) (s : nat) : Tree nat * nat
  :=
    match t with
      | Leaf _ =>
        (Leaf s, 1 + s)
      | Node l r =>
        let (l , s ) := relabel' a l s in
        let (r , s ) := relabel' a r s in
        (Node l r , s )
   end.

Definition s := nat.

Definition State (a : Set) : Type :=
  s -> a * s.

Definition ret {a : Set} : a -> State a := fun x s => (x , s).

Definition bind {a b : Set} : State a -> (a -> State b) -> State b
  := fun c1 c2 s1 =>
       let (x , s2 ) := c1 s1 in c2 x s2 .
Infix ">>=" := bind (right associativity, at level 71).

Definition bind2 {a b : Set} : State a -> State b -> State b
  := fun p1 p2 =>
       p1 >>= fun _ => p2.
Infix ">>>" := bind2 (right associativity, at level 71).

Definition get : State s :=
  fun s => (s, s).

Definition put : s -> State unit :=
  fun s _ => (tt, s).

Fixpoint relabel {a : Set} (t : Tree a) : State (Tree nat)
  :=
    match t with
      | Leaf _ =>
        get >>=
            fun n => put (S n) >>>
                         ret (Leaf n)
      | Node l r =>
        relabel l >>=
        fun l => relabel r >>=
                 fun r => ret (Node l r)
    end.

(* END *)
