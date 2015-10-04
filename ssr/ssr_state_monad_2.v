(** The Hoare State Monad - Proof Pearl, Wouter Swierstra *)
(** その前半部分 State Monad *)
(* @suharahiromichi 2014_01_13 *)
(* Monad Class を使って書き直す。 *)
(* @suharahiromichi 2015_10_04 *)

Require Import ssreflect ssrbool ssrnat seq eqtype.
Require Import Program.                     (* Program *)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Notation "f $ x" := (f x) (at level 65, right associativity, only parsing).

Inductive Tree (a : Set) : Set :=
| Leaf : a -> Tree a
| Node : Tree a -> Tree a -> Tree a.

Fixpoint relabel' (a : Set) (t : Tree a) (s : nat) : Tree nat * nat
  :=
    match t with
      | Leaf _ =>
        (Leaf s, 1 + s)
      | Node l r =>
        let (l , s ) := relabel' l s in
        let (r , s ) := relabel' r s in
        (Node l r , s )
   end.

Delimit Scope monad_scope with monad.
Open Scope monad_scope.

Definition s := nat.

Class Monad (T : Type -> Type) :=
  {
    ret : forall {X : Type}, X -> T X;
    bind : forall {X Y : Type}, (X -> T Y) -> (T X -> T Y)
  }.
(* モナド則付きの Monad でも全く同じことができる *)
Bind Scope monad_scope with Monad.

Infix ">>=" := bind (right associativity, at level 71).
Notation "m >>> n" := (m >>= (fun _ => n)) (at level 50, left associativity).

Notation "x <- m ; p" := (m >>= fun x => p%monad)
                           (at level 68, right associativity,
                            format "'[' x  <-  '[' m ']' ; '//' '[' p ']' ']'"): monad_scope.

(*
Definition State (a : Set) : Type :=
  s -> a * s.

Definition ret {a : Set} : a -> State a := fun x s => (x , s).

Definition bind {a b : Set} : State a -> (a -> State b) -> State b
  := fun c1 c2 s1 =>
       let (x , s2 ) := c1 s1 in c2 x s2 .
*)

Definition state (a : Type) : Type := s -> a * s.
(*
CoInductive state (a : Type) : Type :=
  Sta : s -> state a.
*)

Check @ret  : forall T : Type -> Type, Monad T ->
                                       forall X : Type, X -> T X.
Check @bind : forall T : Type -> Type, Monad T ->
                                       forall X Y : Type, (X -> T Y) -> T X -> T Y.
Instance State : Monad state :=
  {
    ret X x := fun (s1 : s)  => (x , s1);    (* state X *)
(* ret の引数
X : Type
x : X
*)
    bind X Y c1 c2 := fun (s1 : s) =>
                        let (x , s2) := (c2 s1) in (c1 x s2) (* state Y *)
                     (* let (y , s3) := (f x s2) in (y , s3) *)
(* bind の引数
X : Type
Y : Type
c1 : X -> state Y     (X -> T Y)
c2 : state X          T X
*)
  }.

Definition get : state s := fun s => (s, s).
Definition put : s -> state unit := fun s _ => (tt, s).

Check get >>= put.

(* ここまで *)

Definition bind2 {a b : Set} : state a -> state b -> state b
  := fun p1 p2 =>
       p1 >>= fun _ => p2.


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
