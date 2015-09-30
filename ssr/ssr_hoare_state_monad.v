(* -*- coding: utf-8 -*- *)
(** The Hoare State Monad - Proof Pearl, Wouter Swierstra *)
(* http://www.staff.science.uu.nl/~swier004/Publications/HoareLogicStateMonad.pdf *)
(* 後半、HoareState の証明 *)
(* @suharahiromichi 2014_01_25 *)

Require Import ssreflect ssrbool ssrnat seq.
Require Import Program.                     (* Program *)

Inductive Tree (a : Set) : Set :=
| Leaf : a -> Tree a
| Node : Tree a -> Tree a -> Tree a.

Implicit Arguments Leaf [[a]].
Implicit Arguments Node [[a]].

Fixpoint flatten {a : Set} (t : Tree a) : list a :=
  match t with
    | Leaf x => x :: nil
    | Node l r => flatten l ++ flatten r
  end.

Definition s := nat.

Definition Pre : Type := s -> Prop.

Definition Post (a : Set) : Type := s -> a -> s -> Prop.

Program Definition HoareState (pre : Pre) (a : Set) (post : Post a) : Set :=
  forall (i : {t : s | pre t}), {(x, f) : a * s | post i x f }.

Definition top : Pre := fun s => True.

Program Definition ret {a : Set} :
  forall x, HoareState top a (fun i y f => i = f /\ y = x) :=
  fun x s => (x, s).

Program Definition bind :
  forall {a b P1 P2 Q1 Q2},
    (HoareState P1 a Q1) ->
    (forall (x : a), HoareState (P2 x) b (Q2 x)) ->
    HoareState (fun s1 => P1 s1 /\ (forall x s2, Q1 s1 x s2 -> P2 x s2))
               b
               (fun s1 y s3 => exists x, exists s2, Q1 s1 x s2 /\ Q2 x s2 y s3) :=
  fun {a b P1 P2 Q1 Q2} c1 c2 s1 =>
    match c1 s1 with
      | (x, s2) => c2 x s2
    end.
Obligation 2.
Proof.
  elim: c1 Heq_anonymous => x0 H0 /= Heq_anonymous.
  rewrite <- Heq_anonymous in H0.
  by apply/p0/H0.
Qed.
Obligation 3.
Proof.
  elim: (c2 x) => /=.
  elim=> a' s' H1.
  exists x s2.
  split.
  (* Q1 s1 x s2 *)
  - elim: c1 Heq_anonymous => x0 /= H0 Heq_anonymous.
    rewrite <- Heq_anonymous in H0.
    by apply: H0.
  (* Q2 x s2 b0 s0 *)    
  - by apply: H1.
Qed.
Check bind.
Infix ">>=" := bind (right associativity, at level 71).

Program Definition bind2 :
  forall {a b P1 P2 Q1 Q2},
    (HoareState P1 a Q1) ->
    (HoareState P2 b Q2) ->
    HoareState (fun s1 => P1 s1 /\ (forall x s2, Q1 s1 x s2 -> P2 s2))
               b
               (fun s1 y s3 => exists x, exists s2, Q1 s1 x s2 /\ Q2 s2 y s3) :=
  fun {a b P1 P2 Q1 Q2} c1 c2 =>
    c1 >>= fun _ => c2.
Check bind2.
Infix ">>>" := bind2 (right associativity, at level 71).

Program Definition get : HoareState top s (fun i x f => i = f /\ x = i) :=
  fun s => (s, s).

Program Definition put (x : s) : HoareState top unit (fun _ _ f => f = x) :=
  fun _ => (tt, x).

Fixpoint size {a : Set} (t : Tree a) : nat :=
  match t with
    | Leaf x => 1
    | Node l r => size l + size r
  end.

Fixpoint sequence (x n : nat) : list nat :=
  match n with
    | 0 => nil
    | S k => x :: sequence (S x) k
  end.

Lemma SequenceSplit : forall y x z,
                        sequence x (y + z) = sequence x y ++ sequence (x + y) z.
Proof.
  elim=> [| y IHy] x z /=.
  (* y = 0 *)
  - by rewrite add0n addn0.
  (* y = y.+1 *)
  - by rewrite (IHy x.+1 z) addSn addnS.
Qed.

Program Fixpoint relabel {a : Set} (t : Tree a) {struct t} :
  HoareState top
             (Tree nat)
             (fun i t f => f = i + size t /\ flatten t = sequence i (size t)) :=
    match t with
      | Leaf x =>
        get >>= fun n =>
                  put (n + 1) >>>
                      ret (Leaf n)
      | Node l r =>
        relabel l >>=
                fun l' => relabel r >>=
                                  fun r' => ret (Node l' r')
    end.
Obligation 4.
Locate "`".                            (* proj1_sig *)
(* ProofCafe 2014_01_25 で教えていただいた証明。 *)
Proof.
  (* ``let (x0, f) := ` xx in yy`` の xx 部分を場合分けする。 *)
  case: (relabel a l >>= _) => /=.
  case=> x' n [t1] [n2] [[H0 H1] H2].
  case: H2 => t2 [n3] [[H3 H4] [H5 H6]].
  rewrite H6.
  split.
  - (* n = x + size (Node t1 t2) *)
    by rewrite addnA -H0 -H3.
  - (* flatten (Node t1 t2) = sequence x (size (Node t1 t2)) *)
    by rewrite SequenceSplit /= H1 H4 H0.
Defined.
Check relabel.

(* OCaml 3.12.1 *)
(* coq-8.4pl2 *)
(* ssreflect-1.4 *)

(* END *)
