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
    Parameter t : eqType -> eqType.         (* Set -> Set. *)
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
    Definition t : eqType -> eqType := seq_eqType. (* Set -> Set *)
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
      done.                               (* simplify. by equality. *)
    Qed.
    
    Theorem empty_dequeue {A} (q : t A) : dequeue q = None -> q = empty A.
    Proof.
      case: q => [H | a q H].
      - done.                               (* equality *)
      - simpl in *.                         (* simplify *)
        destruct (dequeue q) as [p |] eqn: H0.
(*
  case H0 : (dequeue q) だと、 p が _a_ になり、取り出せない。
*)  
        (* dequeue q = Some p の場合 *)
        + case: p H0 H.
          done.                          (* equality *)
        (* dequeue q = None の場合 *)
        + done.                             (* equality *)
    Qed.
    
    Theorem dequeue_enqueue {A} (q : t A) x :
      dequeue (enqueue q x) = Some (match dequeue q with
                                    | None => (empty A, x)
                                    | Some (q', y) => (enqueue q' x, y)
                                    end).
    Proof.
      simpl.                                (* simplify *)
      case: (dequeue q) => [p |].           (* cases *)
      - case: p.                            (* cases *)
        done.                               (* equality *)
      - done.                               (* equality *)
    Qed.
    
  End ListQueue.
  
  (* There are software-engineering benefits to interface-implementation
   * separation even when one only bothers to build a single implementation.
   * However, often there are naive and clever optimized versions of a single
   * interface.  Queues are no exception.  Before we get to a truly clever
   * version, we'll demonstrate with a less obviously better version:
   * enqueuing at the back and dequeuing from the front. *)
  Module ReversedListQueue : QUEUE.
    Definition t : eqType -> eqType := seq_eqType. (* Set -> Set := list. *)
    (* Still the same internal queue type, but note that Coq's type system
     * prevents client code from knowing that fact!  [t] appears *opaque*
     * or *abstract* from the outside, as we'll see shortly. *)

    (* The first two operations are similar, but now we enqueue at the
     * list end. *)
    Definition empty A : t A := [::].
    Definition enqueue A (q : t A) (x : A) : t A := q ++ [:: x].

    (* [dequeue] is now constant time, with no recursion and just a single
     * pattern match. *)
    Definition dequeue A (q : t A) : option (t A * A) :=
      match q with
      | [::] => None
      | x :: q' => Some (q', x)
      end.

    (* The proofs of the laws are still boring. *)

    Theorem dequeue_empty {A} : dequeue (empty A) = None.
    Proof.
      done.                                 (* simplify. equality. *)
    Qed.

    Theorem empty_dequeue {A} (q : t A) : dequeue q = None -> q = empty A.
    Proof.
      simplify.
      case: q H.                            (* cases q *)
      - simplify.
        by equality.
      - simplify.
        by equality.
    Qed.
    
    Theorem dequeue_enqueue {A} (q : t A) x :
      dequeue (enqueue q x) = Some (match dequeue q with
                                    | None => (empty A, x)
                                    | Some (q', y) => (enqueue q' x, y)
                                    end).
    Proof.
      simplify.
      rewrite /dequeue /enqueue.
      case: q; simplify.                    (* cases q; simplify. *)
      - by equality.
      - by equality.
    Qed.
  End ReversedListQueue.

  (* Let's take a look at some client code that is agnostic to queue
   * implementation details.  We have been using Coq's *module system*, inspired
   * by those of the ML programming languages, to encode interfaces and
   * implementations.  Coq also adopts from ML the idea of *functors*, or
   * functions from modules to modules. *)
  Module DelayedSum (Q : QUEUE).
    (* The code in this scope may refer to some unknown implementation [Q] of
     * the [QUEUE] interface. *)

    (* We will only use a simple example here: enqueue the first [n] natural
     * numbers and then successively dequeue them, computing the sum as we
     * go. *)

    (* First, the function to enqueue the first [n] natural numbers. *)
    Fixpoint makeQueue (n : nat) (q : Q.t nat_eqType) : Q.t nat_eqType :=
      match n with
      | 0 => q
      | S n' => makeQueue n' (Q.enqueue q n')
      end.

    (* Next, the function to dequeue repeatedly, keeping a sum. *)
    Fixpoint computeSum (n : nat_eqType) (q : Q.t nat_eqType) : nat_eqType :=
      match n with
      | 0 => 0
      | S n' => match Q.dequeue q with
                | None => 0
                | Some (q', v) => v + computeSum n' q'
                end
      end.

    (* This function gives the expected answer, in a simpler form, of
     * [computeSum] after [makeQueue]. *)
    Fixpoint sumUpto (n : nat_eqType) : nat_eqType :=
      match n with
      | 0 => 0
      | S n' => n' + sumUpto n'
      end.

    (* A crucial lemma: what results from dequeuing out of a [makeQueue]
     * call?  The answer depends on whether the initial queue [q] has anything
     * to dequeue. *)
    Lemma dequeue_makeQueue n q :
      Q.dequeue (makeQueue n q)
      = match Q.dequeue q with
          | Some (q', v) =>
            (* The queue we started with had content.  We dequeue from it. *)
            Some (makeQueue n q', v)
          | None =>
            (* No content in initial queue.  We get [n-1] (unless [n = 0]). *)
            match n with
            | 0 => None
            | S n' => Some (makeQueue n' q, n')
            end
          end.
    Proof.
      elim: n q => [| n IHn] q.

      - simplify.
        cases (Q.dequeue q).
        + cases p.
          by equality.
        + by equality.

      - simplify.
        rewrite IHn.
        rewrite Q.dequeue_enqueue.
        (* ^-- Crucial step!  First use of a law from the interface. *)
        cases (Q.dequeue q).
        + cases p.
            by equality.

        + rewrite (Q.empty_dequeue (q := q)).
          (* ^-- Another law! *)
          * by equality.
          * done.
    Qed.
    
    (* Now we can tackle the final property directly by induction. *)
    Theorem computeSum_ok n :
      computeSum n (makeQueue n (Q.empty nat_eqType)) = sumUpto n.
    Proof.
      elim: n => [| n IHn].

      - simplify.
        by equality.

      - simplify.
        rewrite dequeue_makeQueue.
        rewrite Q.dequeue_enqueue.
        rewrite Q.dequeue_empty.
        rewrite IHn.
        by equality.
    Qed.
  End DelayedSum.
End Algebraic.

(* There is a famous implementation of queues with two stacks, achieving
 * amortized constant time for all operations, in contrast to the worst-case
 * quadratic time of both queue implementations we just saw.  However, to
 * justify this fancy implementation, we will need to choose a more permissive
 * interface, based on the idea of parameterizing over an arbitrary *equivalence
 * relation* between queues, which need not be simple equality. *)
Module AlgebraicWithEquivalenceRelation.
  Module Type QUEUE.
    (* We still have a type family of queues, plus the same three operations. *)
    Parameter t : eqType -> eqType.         (* Set -> Set. *)
    (* equiv を bool で定義するため。 *)

    Parameter empty : forall (A : eqType), t A.
    Parameter enqueue : forall (A : eqType), t A -> A -> t A.
    Parameter dequeue : forall (A : eqType), t A -> option (t A * A).

    (* What's new?  This equivalence relation.  The type [Prop] stands for
     * logical truth values, so a function returning it can be seen as a
     * relation in the usual mathematical sense.  This is a *binary* relation,
     * in particular, since it takes two arguments. *)
    Parameter equiv : forall (A : eqType), t A -> t A -> bool. (* Prop *)

    (* Let's declare convenient syntax for the relation. *)
    Infix "~=" := equiv (at level 70).

    (* It really is an equivalence relation, as formalized by the usual three
     * laws. *)
    Axiom equiv_refl : forall (A : eqType) (a : t A), a ~= a.
    Axiom equiv_sym : forall (A : eqType) (a b : t A), a ~= b -> b ~= a.
    Axiom equiv_trans : forall (A : eqType) (a b c : t A), a ~= b -> b ~= c -> a ~= c.

    (* It must be the case that enqueuing elements preserves the relation. *)
    Axiom equiv_enqueue : forall (A : eqType) (a b : t A) (x : A),
        a ~= b
        -> enqueue a x ~= enqueue b x.

    (* We define a derived relation for results of [dequeue]: either both
     * [dequeue]s failed to return anything, or both returned the same data
     * value along with new queues that are themselves related. *)
    Definition dequeue_equiv (A : eqType) (a b : option (t A * A)) : bool :=
      match a, b with
      | None, None => true                  (* True *)
      | Some (qa, xa), Some (qb, xb) => (qa ~= qb) && (xa == xb)
      | _, _ => false
      end.

    Infix "~~=" := dequeue_equiv (at level 70).

    Axiom equiv_dequeue : forall (A : eqType) (a b : t A),
        a ~= b
        -> dequeue a ~~= dequeue b.

    (* We retain the three axioms from the prior interface, using our fancy
     * relation instead of equality on queues. *)

    Axiom dequeue_empty : forall (A : eqType), dequeue (empty A) = None.
    Axiom empty_dequeue : forall(A : eqType) (q : t A),
        dequeue q = None -> q ~= empty A.

    Axiom dequeue_enqueue : forall (A : eqType) (q : t A) x,
        dequeue (enqueue q x)
        ~~= match dequeue q with
            | None => Some (empty A, x)
            | Some (q', y) => Some (enqueue q' x, y)
            end.
  End QUEUE.

  Ltac equality_new :=
    intros;
    (repeat bool2prop_hypo; bool2prop_goal; equality)
    with bool2prop_hypo :=
      match goal with
      | H : is_true (_ == _) |- _ => move/eqP: H => H
      | H : is_true (_ && _) |- _ => move/andP: H; case: H
      | H : is_true (_ || _) |- _ => move/orP: H; case: H
      end
    with bool2prop_goal :=
      match goal with
      | |- is_true (_ == _) => apply/eqP
      | |- is_true (_ && _) => apply/andP; split; equality_new
      | |- is_true (_ || _) => apply/orP; try (left; ssromega); try (right; ssromega)
      | |- _ => idtac
      end.

  (* It's easy to redo [ListQueue], specifying normal equality for the
   * equivalence relation. *)
  Module ListQueue : QUEUE.
(*    Variable A : eqType.          (* equiv を bool で定義するため。 *) *)

    Definition t (A : eqType) : eqType := seq_eqType A. (* Set -> Set := seq. *)

    Definition empty (A : eqType) : t A := nil.
    Definition enqueue (A : eqType) (q : t A) (x : A) : t A := x :: q.
    Fixpoint dequeue (A : eqType) (q : t A) : option (t A * A) :=
      match q with
      | [::] => None
      | x :: q' =>
        match dequeue q' with
        | None => Some ([::], x)
        | Some (q'', y) => Some (x :: q'', y)
        end
      end.

    Definition equiv (A : eqType) (a b : t A) := a == b.
    Infix "~=" := equiv (at level 70).

    Theorem equiv_refl (A : eqType) (a : t A) : a ~= a.
    Proof.
      rewrite /equiv.
        by equality_new.
    Qed.

    Theorem equiv_sym (A : eqType) (a b : t A) : a ~= b -> b ~= a.
    Proof.
      rewrite /equiv.
        by equality_new.
    Qed.
    
    Theorem equiv_trans (A : eqType) (a b c : t A) : a ~= b -> b ~= c -> a ~= c.
    Proof.
      rewrite /equiv.
        by equality_new.
    Qed.

    Theorem equiv_enqueue (A : eqType) (a b : t A) (x : A) :
      a ~= b
      -> enqueue a x ~= enqueue b x.
    Proof.
      rewrite /equiv.
        by equality_new.
    Qed.

    Definition dequeue_equiv (A : eqType) (a b : option (t A * A)) : bool :=
      match a, b with
      | None, None => true                  (* True *)
      | Some (qa, xa), Some (qb, xb) => (qa ~= qb) && (xa == xb)
      | _, _ => false                       (* False *)
      end.

    Infix "~~=" := dequeue_equiv (at level 70).

    Theorem equiv_dequeue (A : eqType) (a b : t A) :
      a ~= b
      -> dequeue a ~~= dequeue b.
    Proof.
      simplify.
      rewrite /dequeue_equiv /equiv.        (* 順番は変えた。 *)
      rewrite /equiv in H.                  (* Mathcomp では in * は使えない。 *)
      move/eqP in H.
      rewrite H.
      
      cases (dequeue b).
      - cases p.
        by equality_new.
      - done.                               (* propositional. *)
    Qed.
    
    Theorem dequeue_empty (A : eqType) : dequeue (empty A) = None.
    Proof.
      simplify.
      equality.
    Qed.

    Theorem empty_dequeue (A : eqType) (q : t A) :
      dequeue q = None -> q ~= empty A.
    Proof.
      simplify.
      destruct q as [| s p p'] eqn: H'.      (* cases q. *)
      - simplify.
        unfold equiv.
        by equality_new.
        
      - simplify.
        destruct (dequeue p) as [p' |].     (* cases (dequeue p)  *)
        + cases p'.                         (* let 式を分解する。 *)
            by equality_new.
        + done.
    Qed.
    
    Theorem dequeue_enqueue (A : eqType) (q : t A) x :
        dequeue (enqueue q x)
        ~~= match dequeue q with
            | None => Some (empty A, x)
            | Some (q', y) => Some (enqueue q' x, y)
            end.
    Proof.
      rewrite /equiv /dequeue_equiv.
      elim: q => /= [|p q IHq].
      - by equality_new.
      - destruct (dequeue q) as [p0 |] eqn: H'. (* cases (dequeue q) *)
        + cases p0.
          rewrite /equiv.
          by equality_new.
        + rewrite /equiv.
          by equality_new.
    Qed.
    
  End ListQueue.

  (* However, now we can implement the classic two-stacks optimized queue! *)
  Module TwoStacksQueue : QUEUE.
    (* Every queue is a pair of stacks: one for enqueuing and one for
     * dequeuing. *)
    Record stackpair (A : eqType) := {
      EnqueueHere : seq_eqType A;
      (* This stack has more recently enqueued elements closer to the front,
       * making enqueuing constant-time. *)

      DequeueHere : seq_eqType A
      (* This stack has least recently enqueued elements closer to the front,
       * making dequeuing constant-time. *)
    }.
    (* What's the catch?  Sometimes we need to reverse [EnqueueHere] and
     * transfer it to [DequeueHere], or otherwise there would never be anything
     * to dequeue!  Luckily, the work we do in transfering is bounded
     * asymptotically by the total number of enqueue/dequeue operations, so
     * we get *amortized* constant time. *)

    (* By the way, the [Record] feature we used above is similar to e.g. structs
     * in C. *)

    Definition eqStackpair (A : eqType) (a b : stackpair A) : bool :=
      (EnqueueHere a == EnqueueHere b)
        && (DequeueHere a == DequeueHere b).

    Lemma stackpair_eqP (A : eqType) (a b : stackpair A) :
      reflect (a = b) (eqStackpair a b).
    Proof.
      rewrite /eqStackpair.
      apply: (iffP idP).
      - case: a => /= a1 a2.
        case: b => /= b1 b2.
          by move=> /andP [/eqP -> /eqP ->].
      - move=> H.
        rewrite -H.
          by apply/andP.
    Qed.
    
    Definition stackpair_eqMixin (A : eqType) :=
      @EqMixin (@stackpair A) (@eqStackpair A) (@stackpair_eqP A).
    Canonical stackpair_eqType (A : eqType) :=
      @EqType (@stackpair  A) (@stackpair_eqMixin A).

    Definition t (A : eqType) := stackpair_eqType A.
    Check t : eqType -> eqType.

    Definition empty A : t A := {|
      EnqueueHere := [::];
      DequeueHere := [::]
    |}.
    Definition enqueue A (q : t A) (x : A) : t A := {|
      EnqueueHere := x :: q.(EnqueueHere);
      DequeueHere := q.(DequeueHere)
    |}.
    Definition dequeue A (q : t A) : option (t A * A) :=
      match q.(DequeueHere) with
      | x :: dq => Some ({| EnqueueHere := q.(EnqueueHere);
                            DequeueHere := dq |}, x)
      | [::] =>
        (* Out of dequeuable elements.  Reverse enqueued elements
         * and transfer to the other stack. *)
        match rev q.(EnqueueHere) with
        | [::] => None
        | x :: eq => Some ({| EnqueueHere := [::];
                              DequeueHere := eq |}, x)
        end
      end.

    (* This function explains which simple queue representation we have in mind,
     * for each fancy two-stack representation. *)
    Definition elements A (q : t A) : list A :=
      q.(EnqueueHere) ++ rev q.(DequeueHere).

    (* That function is useful to define our equivalence relation. *)
    Definition equiv A (a b : t A) : bool :=
      elements a == elements b.
    Infix "~=" := equiv (at level 70).

    Theorem equiv_refl A (a : t A) : a ~= a.
    Proof.
      rewrite /equiv.
        by equality_new.
    Qed.

    Theorem equiv_sym A (a b : t A) : a ~= b -> b ~= a.
    Proof.
      rewrite /equiv.
        by equality_new.
    Qed.

    Theorem equiv_trans A (a b c : t A) : a ~= b -> b ~= c -> a ~= c.
    Proof.
      rewrite /equiv.
        by equality_new.
    Qed.

    (* Now it is mostly routine to prove the laws, though a few tricks may
     * be worth reading through. *)

    Theorem equiv_enqueue A (a b : t A) (x : A) :
        a ~= b
        -> enqueue a x ~= enqueue b x.
    Proof.
      unfold equiv, elements; simplify.
        by equality_new.
    Qed.

    Definition dequeue_equiv A (a b : option (t A * A)) :=
      match a, b with
      | None, None => true
      | Some (qa, xa), Some (qb, xb) => (qa ~= qb) && (xa == xb)
      | _, _ => false
      end.

    Infix "~~=" := dequeue_equiv (at level 70).

    Lemma rev_a (A : eqType) (a : A) : rev [:: a] = [:: a].
    Proof.
      done.
    Qed.
    
(*
    Lemma app_inj_tail (A : eqType) (x y : seq A) (a b : A) :
      x ++ [:: a] = y ++ [:: b] -> x = y /\ a = b.
    Proof.
      move/eqP.
      rewrite 2!cats1 eqseq_rcons.
      move/andP=> [H1 H2].
      move/eqP in H1.
      move/eqP in H2.
      (* inversion H2. *)
        by rewrite H1.
    Qed.
*)
    Lemma app_inj_tail (A : eqType) (x y : seq A) (a b : A) :
      x ++ [:: a] == y ++ [:: b] -> (x == y) && (a == b).
    Proof.
      rewrite 2!cats1 eqseq_rcons.
      move/andP=> [H1 H2].
      move/eqP in H1.
      move/eqP in H2.
      rewrite H1 H2.
        by apply/andP; split.
    Qed.
(*    
    Lemma app_inj_head (A : eqType) (a b : A) (x y : seq A) :
      [:: a] ++ x = [:: b] ++ y -> a = b /\ x = y.
    Proof.
      rewrite eqseq_cons.                   (* eqseq_cat *)
      move/andP=> [H1 H2].
      move/eqP in H1.
      move/eqP in H2.
      (* inversion H1. *)
        by rewrite H2.
    Qed.
*)    
    Lemma app_inj_head (A : eqType) (a b : A) (x y : seq A) :
      [:: a] ++ x == [:: b] ++ y -> (a == b) && (x == y).
    Proof.
      rewrite eqseq_cons.                   (* eqseq_cat *)
      move/andP=> [H1 H2].
      move/eqP in H1.
      move/eqP in H2.
      rewrite H1 H2.
        by apply/andP; split.
    Qed.
    
    Theorem equiv_dequeue A (a b : t A) :
        a ~= b
        -> dequeue a ~~= dequeue b.
    Proof.
      unfold equiv, dequeue_equiv, elements, dequeue; simplify.
      cases (DequeueHere a); simplify.
      - cases (rev (EnqueueHere a)); simplify.
        + cases (DequeueHere b); simplify.
          * cases (rev (EnqueueHere b)); simplify.
            ** done.                        (* propositional. *)
            ** rewrite !cats0 in H.
                 by equality_new.
          * cases (EnqueueHere a); simplify.
            ** cases (EnqueueHere b); simplify.
               *** rewrite -cat1s rev_cat in H. (* **** *)
                   cases (rev s0); simplify.
                   **** rewrite rev_a in H. (* **** *)
                        done.
                   **** done.
               *** done.
            ** rewrite rev_cons in Heq0.    (* **** *)
               cases (rev s2); simplify.
               *** done.
               *** done.
               
        + cases (DequeueHere b); simplify.
          * cases (rev (EnqueueHere b)); simplify.
            ** rewrite !cats0 in H.
               move/eqP in H.
               rewrite H in Heq0.
               rewrite Heq2 in Heq0.
               done.
            ** rewrite !cats0 in H.
               move/eqP in H.
               rewrite H in Heq0.
               rewrite Heq2 in Heq0.
               inversion Heq0.
               rewrite /equiv.
               equality_new.
          * rewrite cats0 in H.           (* rewrite app_nil_r in H *)
            move/eqP in H.
            rewrite H in Heq0.
            SearchRewrite (rev (_ ++ _)).
            rewrite rev_cat in Heq0.
            rewrite revK in Heq0.           (* rev rev *)
            rewrite -cat1s in Heq0.
            simplify.
            inversion Heq0.
            unfold equiv, elements.
            simplify.
            apply/andP.
            split.
            ** by rewrite rev_cat revK.
            ** done.
      - cases (DequeueHere b); simplify.
        + cases (rev (EnqueueHere b)); simplify.
          * rewrite cats0 in H.
            move/eqP in H.
            rewrite <- H in Heq1.
            cases (EnqueueHere a); simplify.
            ** cases (rev s0); simplify.
               *** by rewrite revK in Heq1.
               *** rewrite revK in Heq1.
                   done.
            ** rewrite rev_cons in Heq1.
               rewrite rev_cons in Heq1.
               rewrite -!cats1 in Heq1.
               rewrite catA in Heq1.
               rewrite rev_cat in Heq1.
               rewrite rev_a in Heq1.
               rewrite cat1s in Heq1.
                   rewrite cat_cons in Heq1.
               done.
          * unfold equiv, elements.
            simplify.
            rewrite cats0 in H.
            move/eqP in H.
            rewrite <- H in Heq1.
            rewrite rev_cat in Heq1.
            rewrite revK in Heq1.
            rewrite cat_cons in Heq1.
            inversion Heq1.
            rewrite rev_cat revK.
            by equality_new.    (* apply/andP. by split; apply/eqP. *)
        + unfold equiv, elements.
          simplify.
          Check app_inj_tail.
          apply: app_inj_tail.
          rewrite -2!catA.
          rewrite 2!cats1 -2!rev_cons.
          done.
    Qed.
    
    Theorem dequeue_empty A : dequeue (empty A) = None.
    Proof.
      simplify.
      equality.
    Qed.

    Theorem empty_dequeue A (q : t A) :
        dequeue q = None -> q ~= empty A.
    Proof.
(*
      simplify.
      cases q.
      unfold dequeue in *.
      simplify.
      cases DequeueHere0.
      cases (rev EnqueueHere0).
      cases EnqueueHere0.
      equality.
      simplify.
      cases (rev EnqueueHere0); simplify.
      equality.
      equality.
      equality.
      equality.
    Qed.
 *)
    Admitted.

    Theorem dequeue_enqueue A (q : t A) x :
        dequeue (enqueue q x)
        ~~= match dequeue q with
            | None => Some (empty A, x)
            | Some (q', y) => Some (enqueue q' x, y)
            end.
    Proof.
(*
      unfold dequeue_equiv, equiv; simplify.
      cases q; simplify.
      unfold dequeue, enqueue; simplify.
      cases DequeueHere0; simplify.

      cases (rev EnqueueHere0); simplify.

      equality.

      unfold elements; simplify.
      SearchRewrite (rev (_ ++ _)).
      rewrite rev_app_distr.
      simplify.
      equality.

      equality.
    Qed.
 *)
    Admitted.
      
  End TwoStacksQueue.

(****************

(* まちかったところから、とってきた *)

  Module TwoStacksQueue : QUEUE.

    Record stackpair (A : eqType) :=
      {
        EnqueueHere : seq_eqType A;
        DequeueHere : seq_eqType A
      }.

    Definition eqStackpair (A : eqType) (a b : stackpair A) : bool :=
      (EnqueueHere a == EnqueueHere b)
        && (DequeueHere a == DequeueHere b).

    Lemma stackpair_eqP (A : eqType) (a b : stackpair A) :
      reflect (a = b) (eqStackpair a b).
    Proof.
      rewrite /eqStackpair.
      apply: (iffP idP).
      - admit.
      - move=> H.
        rewrite -H.
        by apply/andP.
    Admitted.

    Definition stackpair_eqMixin (A : eqType) :=
      @EqMixin (@stackpair A) (@eqStackpair A) (@stackpair_eqP A).
    Canonical stackpair_eqType (A : eqType) :=
      @EqType (@stackpair  A) (@stackpair_eqMixin A).

    Definition t (A : eqType) := stackpair_eqType A.
    Check t : eqType -> eqType.

    Definition empty (A : eqType) : t A := {|
      EnqueueHere := [::];
      DequeueHere := [::]
    |}.
    Definition enqueue (A : eqType) (q : t A) (x : A) : t A := {|
      EnqueueHere := x :: q.(EnqueueHere);
      DequeueHere := q.(DequeueHere)
    |}.
    Definition dequeue (A : eqType) (q : t A) : option (t A * A) :=
      match q.(DequeueHere) with
      | x :: dq => Some ({| EnqueueHere := q.(EnqueueHere);
                            DequeueHere := dq |}, x)
      | [::] =>
        match rev q.(EnqueueHere) with
        | [::] => None
        | x :: eq => Some ({| EnqueueHere := [::];
                              DequeueHere := eq |}, x)
        end
      end.

    Definition rep (A : eqType) (q : t A) : seq A :=
      q.(EnqueueHere) ++ rev q.(DequeueHere).

    Theorem empty_rep (A : eqType) :
        rep (empty A) = [::].
    Proof.
      equality.
    Qed.

    Theorem enqueue_rep (A : eqType) (q : t A) x :
        rep (enqueue q x) = x :: rep q.
    Proof.
      equality.
    Qed.
    
    (* notu *)
    Lemma rev_a (A : eqType) (a : A) : rev [:: a] = [:: a].
    Proof.
      done.
    Qed.
    
    Theorem dequeue_empty : forall (A : eqType) (q : t A),
        rep q = [::]
        -> dequeue q = None.
    Proof.
      unfold rep, dequeue; simplify.
      cases (DequeueHere q); simplify.
      - rewrite cats0 in H.               (* rewrite app_nil_r in H *)
        rewrite H.
        done.
      - cases (EnqueueHere q).
        + rewrite -cat1s rev_cat in H.      (* simplify *)
          cases (rev s0); simplify.         (* XXXX *)
          * done.
          * done.
        + done.
          (* rewrite -cat1s -[s :: l]cat1s rev_cat rev_a in H. *)
    Qed.
    
    Theorem dequeue_nonempty (A : eqType) (q : t A) xs x :
        rep q = xs ++ [:: x]
        -> exists q', dequeue q = Some (q', x) /\ rep q' = xs.
    Proof.
      unfold rep, dequeue; simplify.

      cases (DequeueHere q); simplify.

      - rewrite cats0 in H.               (* rewrite app_nil_r in H *)
        rewrite H.
        rewrite rev_cat; simplify. (* rewrite rev_app_distr; simplify. *)
        exists {| EnqueueHere := [::]; DequeueHere := rev xs |}.
        simplify.
        rewrite revK.                    (* rewrite rev_involutive. *)
          by equality.
        
      - exists {| EnqueueHere := EnqueueHere q; DequeueHere := s0 |}. (* XXXX *)
        simplify.
        rewrite -cat1s rev_cat catA rev_a in H. (* rewrite app_assoc in H. *)
        move/app_inj_tail: H => [H1 H2].
          by rewrite H1 H2.
    Qed.

  End TwoStacksQueue.

**************)

(* END *)
