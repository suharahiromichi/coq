(** The Hoare State Monad - Proof Pearl, Wouter Swierstra *)
(** その前半部分 State Monad *)
(* @suharahiromichi 2014_01_13 *)
(* Monad Class を使って書き直す。 *)
(* @suharahiromichi 2015_10_04 *)

From mathcomp Require Import ssreflect ssrbool ssrnat seq eqtype.
Require Import Program.                     (* Program *)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

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

Notation "f $ x" := (f x) (at level 65, right associativity, only parsing).
Reserved Notation "c1 >>= c2" (at level 42, left associativity).
Reserved Notation "c1 >>> c2" (at level 42, left associativity).

Class Monad (T : Type -> Type) :=
  {
    ret : forall {a : Type}, a -> T a;
    bind : forall {a b : Type}, T a -> (a  -> T b) -> T b
       where "c1 >>= c2" := (bind c1 c2);
    monad_1 : forall (a : Type) (x : a) (f : a -> T a),
                ret x >>= f = f x;
    monad_2 : forall (a : Type) (m : T a),
                m >>= ret = m;
    monad_3 : forall (a : Type) (f g : a -> T a) (m : T a),
                (m >>= f) >>= g = m >>= fun x => f x >>= g
  }.

Notation "s1 >>= s2" := (bind s1 s2).
Notation "s1 >>> s2" := (s1 >>= fun _ => s2).
Bind Scope monad_scope with Monad.

(* monad_scope *)
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

Definition state {st : Set} (a : Type) : Type := st -> a * st.

Check @ret  : forall T : Type -> Type, Monad T ->
                                       forall a : Type, a -> T a.
Check @bind : forall T : Type -> Type, Monad T ->
                                       forall a b : Type, T a -> (a -> T b) -> T b.

Axiom functional_extensionality' :
  forall {st : Set} {T : Type} {f g : state T},
    (forall (q : st), f q = g q) -> f = g.

Program Instance State {st : Set} : Monad (@state st) :=
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
Obligation 2.
Proof.
  apply functional_extensionality'.
  by move=> q; elim: m.
Qed.
Obligation 3.
Proof.
  apply functional_extensionality'.
  by move=> q; elim: m.
Qed.

Definition get {st : Set} : state st := fun s => (s, s).
Definition put {st : Set} : st -> state unit := fun s _ => (tt, s).

Definition bind2 {st : Set} {a b : Set} : @state st a -> state b -> state b :=
  fun p1 p2 => p1 >>= fun _ => p2.

Fixpoint relabel'' {a : Set} (t : Tree a) : state (Tree nat) :=
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

(* テスト *)
Check ret 1 : state nat.
Check get : state nat.

Check @bind state _ nat unit get put : state ().
Check bind get put : state ().
Check get >>= put : state ().
Check x <- get; put x : state ().
Check ret 1 >>= put : state ().


Definition Do {X: Type} (m: X) := m.
Arguments Do {X} (m)%monad.
Notation "'DO' m 'OD'":= (Do m) (at level 69, format "DO '[' m ']'  OD").

Fixpoint relabel {a : Set} (t : Tree a) : state (Tree nat) :=
  match t with
    | Leaf _ =>
      DO
        n <- get;
        _ <- put (n + 1);
        ret $ Leaf n
      OD
    | Node l r =>
      DO
        l <- relabel l;
        r <- relabel r;
        ret $ Node l r
      OD
  end.

Close Scope monad_scope.

(* END *)
