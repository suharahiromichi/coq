(** The Hoare State Monad - Proof Pearl, Wouter Swierstra *)
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

Fixpoint relabel'' {a : Set} (t : Tree a) : State (Tree nat)
  :=
    match t with
      | Leaf _ =>
        get >>=
            fun n => put (S n) >>>
                         ret (Leaf n)
      | Node l r =>
        relabel'' l >>=
        fun l => relabel'' r >>=
                 fun r => ret (Node l r)
    end.

Fixpoint flatten {a : Set} (t : Tree a) : list a
  :=
    match t with
      | Leaf x => x :: nil
      | Node l r => flatten l ++ flatten r
    end.

Definition Pre : Type := s -> Prop.

Definition Post (a : Set) : Type := s -> a -> s -> Prop.

Program Definition HoareState (pre : Pre) (a : Set) (post : Post a) : Set
  :=
  forall (i : {t : s | pre t}),
    {(x, f) : a * s | post i x f }.

Definition top : Pre := fun s => True.

Program Definition ret' (a : Set) :
  forall x, HoareState top a (fun i y f => i = f /\ y = x)
  :=
  fun x s => (x, s).

Program Definition bind' :
  forall a b P1 P2 Q1 Q2,
    (HoareState P1 a Q1) ->
    (forall (x : a), HoareState (P2 x) b (Q2 x)) ->
    HoareState (fun s1 => P1 s1 /\ forall x s2, Q1 s1 x s2 -> P2 x s2)
               b
               (fun s1 y s3 => exists x, exists s2, Q1 s1 x s2 /\ Q2 x s2 y s3)
  :=
  fun {a b} P1 P2 Q1 Q2 c1 c2 s1 =>
    match c1 s1 with
        (x, s2) => c2 x s2
    end.
Next Obligation.
  admit.
Qed.

Next Obligation.
  admit.
Qed.

Check bind'.
Infix ">>='" := bind' (right associativity, at level 71).

Check bind'.
Definition bind2' {a b : Set} : State a -> State b -> State b
  := fun p1 p2 =>
       p1 >>=' fun _ => p2.
Infix ">>>'" := bind2 (right associativity, at level 71).

(* END *)
