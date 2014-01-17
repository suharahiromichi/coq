(** The Hoare State Monad - Proof Pearl, Wouter Swierstra *)
(** 後半 HoareState モナド *)
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

Fixpoint flatten {a : Set} (t : Tree a) : list a
  :=
    match t with
      | Leaf x => x :: nil
      | Node l r => flatten l ++ flatten r
    end.

Definition s := nat.

Definition Pre : Type := s -> Prop.

Definition Post (a : Set) : Type := s -> a -> s -> Prop.

Program Definition HoareState (pre : Pre) (a : Set) (post : Post a) : Set
  :=
  forall (i : {t : s | pre t}),
    {(x, f) : a * s | post i x f }.

Definition top : Pre := fun s => True.

Program Definition ret {a : Set} :
  forall x, HoareState top a (fun i y f => i = f /\ y = x)
  :=
  fun x s => (x, s).

Program Definition bind :
  forall {a b P1 P2 Q1 Q2},
    (HoareState P1 a Q1) ->
    (forall (x : a), HoareState (P2 x) b (Q2 x)) ->
    HoareState (fun s1 => P1 s1 /\ forall x s2, Q1 s1 x s2 -> P2 x s2)
               b
               (fun s1 y s3 => exists x, exists s2, Q1 s1 x s2 /\ Q2 x s2 y s3)
  :=
  fun {a b P1 P2 Q1 Q2} c1 c2 s1 =>
    match c1 s1 with
        (x, s2) => c2 x s2
    end.
Obligation 2.
  admit.
Qed.

Obligation 3.
  admit.
Qed.

Check bind.
Infix ">>=" := bind (right associativity, at level 71).

Program Definition bind2 :
  forall {a b P1 P2 Q1 Q2},
    (HoareState P1 a Q1) -> (HoareState P2 b Q2) -> (HoareState P2 b Q2)
  :=
  fun {a b P1 P2 Q1 Q2} c1 c2 =>
    c1 >>= fun _ => c2.
Obligation 1.
  admit.
Qed.

Obligation 2.
  admit.
Qed.
Infix ">>>" := bind2 (right associativity, at level 71).

Program Definition get : HoareState top s (fun i x f => i = f /\ x = i)
  := fun s => (s, s).

Program Definition put (x : s) : HoareState top unit (fun _ _ f => f = x)
  := fun _ => (tt, x).

Fixpoint size {a : Set} (t : Tree a) : nat :=
  match t with
    | Leaf x => 1
    | Node l r => size l + size r
  end.

Fixpoint seq (x n : nat) : list nat :=
  match n with
    | 0 => nil
    | S k => x :: seq (S x) k
  end.

Program Fixpoint relabel (a : Set) (t : Tree a) :
  HoareState top
             (Tree nat)
             (fun i t f => f = i + size t /\ flatten t = seq i (size t))
  :=
    match t with
      | Leaf x =>
        get >>= fun n =>
                  put (n + 1) >>>
                      ret (Leaf n)
      | Node l r =>
        relabel a l >>=
                fun l => relabel a r >>=
                                  fun r => ret (Node l r)
    end.
Next Obligation.
  admit.
Defined.

Next Obligation.
  admit.
Qed.

Next Obligation.
Admitted.

Check relabel.

(* END *)
