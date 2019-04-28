From mathcomp Require Import all_ssreflect.
Require Import ssr_frap.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
(* Set Print All. *)

(* 
equality は、intuition congruence または congruence
congruence は subst よりも強力である。

cases X は、case H : X (または destruct X eqn:H) でよかろう。ここでHは自動生成の前提名
Hを作るかどうか、Hを消すかどうかを判断しているだけなので。

simplify は、とりあえず、 simpl または simpl in *
unifyTails は、 Set.v にあるが、当面使わない。
normalize_set は、 Set.v にあるが、当面使わない。
doSubtract は、使うかもしれない。

 *)

(* Perhaps the essence of effective programming is division of large tasks into
 * smaller ones, and *data abstraction* is a key technique to that end.
 * We provide a clear separation between *interfaces* and *implementations*.
 * The author of a library can take responsibility for making it implement an
 * interface faithfully, *encapsulating* private state and other implementation
 * details in a way that client code can't observe.  Then that client code can
 * mix and match implementations of some well-specified functionality.
 *
 * As part of our quick tour through effective Coq programming, we will dwell on
 * patterns for data abstraction, including how to state it formally, from the
 * perspectives of both libraries and client code. *)


(** * Specification styles for data abstraction *)

(* One of the classic formalisms for data abstraction is the *algebraic* style,
 * where requirements on implementations are written out as quantified
 * equalities.  Any implementation must satisfy these equalities, but we grant
 * implementations freedom in internal details. *)
Module Algebraic.
  (* Here's an example of an algebraic interface or *specification* ("spec" for
   * short).  It's for purely functional queues, which follow first-in-first-out
   * disciplines. *)
  Module Type QUEUE.
    Parameter t : Set -> Set.
    (* An implementation must include some data type [t].
     * Actually, it's more of a *type family*, e.g. like [list] and some other
     * polymorphic container types we looked at last time. *)

    Parameter empty : forall A, t A.
    (* For any type [A] of data, we can build a queue for that element type. *)
    Parameter enqueue : forall A, t A -> A -> t A.
    (* Enqueue a new element, in the functional style, where we build a new
     * queue instead of modifying the original. *)
    Parameter dequeue : forall A, t A -> option (t A * A).
    (* Given a queue, either return [None] if it is empty or [Some (q', v)] for
     * the result of dequeuing one element, where [q'] is the new queue (now
     * one element shorter) and [v] is the element we dequeue. *)

    (* Which algebraic properties characterize correct queues? *)

    (* First, [dequeue] returns [None] exactly on empty queues. *)
    Axiom dequeue_empty : forall A,
        dequeue (empty A) = None.
    Axiom empty_dequeue : forall A (q : t A),
        dequeue q = None -> q = empty A.

    (* Second, [dequeue] forms a kind of inverse for [enqueue]. *)
    Axiom dequeue_enqueue : forall A (q : t A) x,
        dequeue (enqueue q x) = Some (match dequeue q with
                                      | None => (empty A, x)
                                      | Some (q', y) => (enqueue q' x, y)
                                      end).

    (* These properties turn out to be enough to prove interesting properties
     * about client code that uses queues.  Before we get there, we should
     * define some concrete queue implementations.  (If we don't give an
     * implementation, we often realize that the spec is *unrealizable*!) *)
  End QUEUE.

  (* First, there is a fairly straightforward implementation with lists. *)
  Module ListQueue : QUEUE.
    Definition t : Set -> Set := seq.
    (* Note that we use identifier [list] alone as a first-class type family,
     * without specifying a parameter explicitly. *)

    (* We follow the convention of enqueuing onto the front of lists and
     * dequeuing from the back, so the first two operations are just the first
     * two constructors of [list]. *)
    Definition empty A : t A := nil.
    Definition enqueue A (q : t A) (x : A) : t A := x :: q.

    (* [dequeue] is a little more work: we use recursion to step down to the
     * last element of a list. *)
    Fixpoint dequeue A (q : t A) : option (t A * A) :=
      match q with
      | [::] => None
      | x :: q' =>
        match dequeue q' with
        | None => Some ([::], x)
        | Some (q'', y) => Some (x :: q'', y)
        end
      end.

    (* Applying our experience so far with Coq proofs, the algebraic laws are
     * unremarkable to establish. *)

    Theorem dequeue_empty {A} : dequeue (empty A) = None.
    Proof.
      simplify.
      by equality.
    Qed.

    Theorem empty_dequeue {A} (q : t A) : dequeue q = None -> q = empty A.
    Proof.
      case: q => [H | a q H].
      - by equality.                        (* done *)
      - simplify.
        cases (dequeue q).                  (* destruct (dequeue q) eqn: H0 *)
        (*  だと、p が _a_ になり、取り出せない。 *)
        
        (* dequeue q = Some p の場合 *)
        + cases p.                          (* case: p H0 H *)
            by equality.                    (* done *)
        (* dequeue q = None の場合 *)
        + by equality.                      (* done *)
    Qed.
    
    Theorem dequeue_enqueue {A} (q : t A) x :
      dequeue (enqueue q x) = Some (match dequeue q with
                                    | None => (empty A, x)
                                    | Some (q', y) => (enqueue q' x, y)
                                    end).
    Proof.
      simplify.
      case: (dequeue q) => [p |].           (* cases *)
      - case: p.                            (* cases *)
        by equality.
      - by equality.
    Qed.
    
  End ListQueue.



End Algebraic.
    
(* END *)
