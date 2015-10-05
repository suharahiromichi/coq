(* -*- coding: utf-8 -*- *)
(** The Hoare State Monad - Proof Pearl, Wouter Swierstra *)
(* http://www.staff.science.uu.nl/~swier004/Publications/HoareLogicStateMonad.pdf *)
(* 後半、HoareState の証明 *)
(* @suharahiromichi 2014_01_25 *)

Require Import ssreflect ssrbool ssrnat seq.
Require Import Program.                     (* Program *)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Inductive Tree (a : Set) : Set :=
| Leaf : a -> Tree a
| Node : Tree a -> Tree a -> Tree a.

Fixpoint flatten {a : Set} (t : Tree a) : list a :=
  match t with
    | Leaf x => x :: nil
    | Node l r => flatten l ++ flatten r
  end.

Definition s := nat.                        (* 自然数1個を状態として持つ。
                                             getとputの対象になる。 *)


Definition State (a : Set) : Type := s -> a * s. (* State Monad、比較のために掲げる。 *)
(* 
p.3 最後

instead of accepting any initial state of type s, it requires an initial state that
satisfies a given precondition. 

型sの任意の状態を受け入れるのではなく、与えられたprecondition(事前条件)を満たすinitail
stateを必要とする。


instead of returning any pair, it guarantees that the resulting pair satisfies a
postcondition relating the initial state, resulting value, and final state.

任意のペアを返すのではなく、initial stateと返値とfinal stateに関連したpostconditionを満たす
ことを保証する。
 *)

Definition Pre : Type := s -> Prop.

Definition Post (a : Set) : Type := s -> a -> s -> Prop.
(* initial state, 返値, final state を意味する。 *)

Program Definition HoareState (pre : Pre) (a : Set) (post : Post a) : Set :=
  forall (i : {t : s | pre t}), {(x, f) : a * s | post i x f }.

Definition top : Pre := fun s => True.

Program Definition ret {a : Set} :
  forall (x : a),
    @HoareState top a (fun (i : s) (y : a) (f : s) => i = f /\ y = x) :=
  fun x s => (x, s).
(**
- i = f は、状態について initial と final がおなじであること。
- y = x は、返値が、ret の引数と同じであること。
  を意味する。ただし、
  返値は、ret の引数の型なので、いろいろな型を取る。
 *)

(**
p.5

bindの返す型の説明：

So clearly the precondition of the composite computation

composite computation の precondition は明白である。

should be imply the precondition of the first computation c1 — otherwise we could not
justify running c1 with the initial state s1 .

c1のprecondition P1 が 導出されるべきである。さもなければ、c1がs1で実行できるか判断できない。


Furthermore the postcondition of the first computation should imply the precondition of
the second computation—if this wasn’t the case, we could not give grounds for the call
to c2 . These considerations lead to the following choice of precondition for the
composite computation:

c1のpostcondition Q1 は、c2のprecondition P2を導出するべきである。もしそうでないと、c2を呼
び出す土台が与えられない。

These considerations lead to the following choice of precondition for the composite
computation:

以上より、composite computation のprecondition は以下のように与える。

``(fun s1 => P1 s1 /\ (forall x s2, Q1 s1 x s2 -> P2 x s2))``

-----

What about the postcondition? Recall that a postcondition is a relation between the
initial state, resulting value, and the final state. 

We would expect the postcondition of both argument computations to hold after executing
the composite computation resulting from a call to bind. 

This composite computation, however, cannot refer to the initial state passed to the
second computation or the results of the first computation: it can only refer to its own
initial state and results. 

このcomposite computationは、c2に渡されたinitial state や c1 の結果を参照することができない。
自身のinitial stateと結果だけ参照できる。

To solve this we existentially quantify over the results of the first computation,
yielding the following postcondition for the bind operation:

これを解決するために、c1の結果を限量化（∃）し、後続のpostconditionに与えることにした。


``(fun s1 y s3 => exists x, exists s2, Q1 s1 x s2 /\ Q2 x s2 y s3)``

In words, the postcondition of the composite computation states that there is an
intermediate state s2 and a value x resulting from the first computation, such that these
satisfy the postcondition of the first computation Q1.

中間状態s2と c1の結果x があり、それらば、c1のpostcondition Q1 を満たす。

Furthermore, the postcondition of the second computation Q2 relates these intermediate
results to the final state s3 and the final value y.

c2のpostcondition Q2 は、final state s3 と 最終の値 y を結果とする中間結果に関係する。
*)

Program Definition bind :
  forall {a b P1 P2 Q1 Q2},
    (@HoareState P1 a Q1) ->
    (forall (x : a), @HoareState (P2 x) b (Q2 x)) ->
    @HoareState (fun s1 => P1 s1 /\ (forall x s2, Q1 s1 x s2 -> P2 x s2))
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
    (@HoareState P1 a Q1) ->
    (@HoareState P2 b Q2) ->
    @HoareState (fun s1 => P1 s1 /\ (forall x s2, Q1 s1 x s2 -> P2 s2))
               b
               (fun s1 y s3 => exists x, exists s2, Q1 s1 x s2 /\ Q2 s2 y s3) :=
  fun {a b P1 P2 Q1 Q2} c1 c2 =>
    c1 >>= fun _ => c2.
Check bind2.
Infix ">>>" := bind2 (right associativity, at level 71).

Program Definition get : @HoareState top s (fun i x f => i = f /\ x = i) :=
  fun s => (s, s).

Program Definition put (x : s) : @HoareState top unit (fun _ _ f => f = x) :=
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
  @HoareState top
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

(* DO 記法 *)
Notation "f $ x" := (f x) (at level 65, right associativity, only parsing).

(*
Delimit Scope monad_scope with monad.
Open Scope monad_scope.

Notation "x <- m ; p" := (m >>= fun x => p)%monad
    (at level 68, right associativity,
     format "'[' x  <-  '[' m ']' ; '//' '[' p ']' ']'") : monad_scope.
Notation "m ; p" := (m >>= fun x => p)%monad
    (at level 68, right associativity,
     format "'[' '[' m ']' ; '//' '[' p ']' ']'") : monad_scope.

Close Scope monad_scope.
Notation "'DO' m 'OD'" := (m)%monad (at level 69, format "DO  '[' m ']'  OD").
*)

Notation "'DO' a <- A ; B 'OD'" := (A >>= fun a => B)
                                     (at level 100, right associativity).
Notation "'DO' A ; B 'OD'" := (A >>> B)
                                (at level 100, right associativity).
Notation "'DO' a <- A ; b <- B ; C 'OD'" := (A >>= fun a => B >>= fun b => C)
                                              (at level 100, right associativity).
Notation "'DO' A ; b <- B ; C 'OD'" := (A >>> B >>= fun b => C)
                                         (at level 100, right associativity).
Notation "'DO' a <- A ; B ; C 'OD'" := (A >>= fun a => B >>> C)
                                         (at level 100, right associativity).
Notation "'DO' A ; B ; C 'OD'" := (A >>> B >>> C)
                                    (at level 100, right associativity).

Program Fixpoint relabel' {a : Set} (t : Tree a) {struct t} :
  @HoareState top
             (Tree nat)
             (fun i t f => f = i + size t /\ flatten t = sequence i (size t)) :=
    match t with
      | Leaf x =>
        DO
          n <- get;
          put (n + 1);                      (* _ <- put (n + 1) *)
          ret $ Leaf n
        OD
      | Node l r =>
        DO
          l <- relabel' l;
          r <- relabel' r;
          ret $ Node l r
        OD
    end.
Obligation 4.
Proof.
  case: (relabel' a l >>= _) => /=.
  case=> x' n [t1] [n2] [[H0 H1] H2].
  case: H2 => t2 [n3] [[H3 H4] [H5 H6]].
  rewrite H6.
  split.
  - (* n = x + size (Node t1 t2) *)
    by rewrite addnA -H0 -H3.
  - (* flatten (Node t1 t2) = sequence x (size (Node t1 t2)) *)
    by rewrite SequenceSplit /= H1 H4 H0.
Defined.

(* もう少し遊んでみる *)
(* get と put だけからなるプログラム *)
Check get : HoareState top (fun i x f : s => i = f /\ x = i).
Check put : forall x : s, HoareState top (fun (i : s) (a : ()) (f : s) => f = x).
Check get >>= put :
  @HoareState
    (fun s1 : s => top s1 /\ _)
    ()                                      (* put の返値 *)
    (fun (s1 : s) (y : ()) (s3 : s) => exists x s2 : s, _).

(* 1 という定数を返す。 *)
Check ret 1 : @HoareState top nat (fun (i : s) (y : nat) (f : s) => i = f /\ y = 1).
Check ret 1 >>= put :
  @HoareState
    (fun s1 : s => top s1 /\ _)
    ()                                      (* put の返値 *)
    (fun (s1 : s) (y : ()) (s3 : s) => exists x s2 : s, _).

Check put 1 :
  @HoareState
    top
    ()
    (fun (_ : s) (_ : ()) (f : s) => f = 1).

Fail Check ret 1 >>= put = put 1.           (* モナド則は成立しない。 *)

(* END *)
