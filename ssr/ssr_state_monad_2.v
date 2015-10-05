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

Fixpoint relabel' (a : Set) (t : Tree a) (s : nat) : Tree nat * nat :=
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

Definition s := nat.                        (* 状態をひとつの自然数とする。 *)

Class Monad (T : Type -> Type) :=
  {
    ret : forall {a : Type}, a -> T a;
    bind : forall {a b : Type}, T a -> (a  -> T b) -> T b
  }.
(* モナド則付きの Monad でも全く同じことができる *)
Bind Scope monad_scope with Monad.

Infix ">>=" := bind (right associativity, at level 71).
Notation "m >>> n" := (m >>= (fun _ => n)) (at level 50, left associativity).

Notation "x <- m ; p" := (m >>= fun x => p%monad)
                           (at level 68, right associativity,
                            format "'[' x  <-  '[' m ']' ; '//' '[' p ']' ']'"): monad_scope.

(*
Classをつかわずに、直接定義する場合：

Definition State (a : Set) : Type := s -> a * s.

Definition ret {a : Set} : a -> State a := fun x s => (x , s).

Definition bind {a b : Set} : State a -> (a -> State b) -> State b :=
  fun c1 c2 s1 => let (x , s2 ) := c1 s1 in c2 x s2 .
*)

Definition state (a : Type) : Type := s -> a * s.

Check @ret  : forall T : Type -> Type, Monad T ->
                                       forall a : Type, a -> T a.
Check @bind : forall T : Type -> Type, Monad T ->
                                       forall a b : Type, T a -> (a -> T b) -> T b.
Instance State : Monad state :=
  {
    ret a x s1 := (x , s1);                 (* state a *)
(* ret の引数
a : Type
x : a
s1 : s
*)
    bind a b c1 c2 s1 :=
      let (x , s2) := (c1 s1) in (c2 x s2)  (* state b *)
(* bind の引数
a : Type
b : Type
c1 : state a          T a
c2 : a -> state b     (a -> T b)
s1 : s
*)
  }.

Definition get : state s := fun s => (s, s).
Definition put : s -> state unit := fun s _ => (tt, s).

Check ret 1 : state s.
Check get : state s.

Check @bind state _ s unit get put : state ().
Check bind get put : state ().
Check get >>= put : state ().
Check (ret 1) >>= put : state ().

Definition bind2 {a b : Set} : state a -> state b -> state b :=
  fun p1 p2 => p1 >>= fun _ => p2.

Fixpoint relabel {a : Set} (t : Tree a) : state (Tree nat)
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
