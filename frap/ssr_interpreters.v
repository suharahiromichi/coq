From mathcomp Require Import all_ssreflect.
Require Import FunctionalExtensionality. (* functional_extensionality *)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
(* Set Print All. *)

Require Import ssr_frap.
Require Import ssr_var.
Require Import ssr_map.

(* We begin with a return to our arithmetic language from the last chapter,
 * adding subtraction*, which will come in handy later.
 * *: good pun, right? *)
Inductive arith : Set :=
| Const (n : nat)
| Var (x : Literal)
| Plus (e1 e2 : arith)
| Minus (e1 e2 : arith)
| Times (e1 e2 : arith).

Example ex1 := Const 42.
Example ex2 := Plus (Var Literal.y) (Times (Var Literal.x) (Const 3)).

(* The above definition only explains what programs *look like*.
 * We also care about what they *mean*.
 * The natural meaning of an expression is the number it evaluates to.
 * Actually, it's not quite that simple.
 * We need to consider the meaning to be a function over a valuation
 * to the variables, which in turn is itself a finite map from variable
 * names to numbers.  We use the book library's [map] type family. *)
Definition valuation := fmap var nat.
(* That is, the domain is [var] (a synonym for [string]) and the codomain/range
 * is [nat]. *)

(* The interpreter is a fairly innocuous-looking recursive function. *)
Fixpoint interp (e : arith) (v : valuation) : nat :=
  match e with
  | Const n => n
  | Var x =>
    (* Note use of infix operator to look up a key in a finite map. *)
    match v $? x with
    | None => 0 (* goofy default value! *)
    | Some n => n
    end
  | Plus e1 e2 => interp e1 v + interp e2 v
  | Minus e1 e2 => interp e1 v - interp e2 v
                   (* For anyone who's wondering: this [-] sticks at 0,
                    * if we would otherwise underflow. *)
  | Times e1 e2 => interp e1 v * interp e2 v
  end.

(* Here's an example valuation, using an infix operator for map extension. *)
Definition valuation0 : valuation :=
  $0 $+ (Literal.x, 17) $+ (Literal.y, 3).

(* Unfortunately, we can't execute code based on finite maps, since, for
 * convenience, they use uncomputable features.  The reason is that we need a
 * comparison function, a hash function, etc., to do computable finite-map
 * implementation, and such things are impossible to compute automatically for
 * all types in Coq.  However, we can still prove theorems about execution of
 * finite-map programs, and the [simplify] tactic knows how to reduce the
 * key constructions. *)
Theorem interp_ex1 : interp ex1 valuation0 = 42.
Proof.
  simplify.
  equality.
Qed.

Theorem interp_ex2 : interp ex2 valuation0 = 54.
Proof.
  unfold valuation0.
  simplify.
  (* FrapWithoutSets.v の simpl_map を見よ。 *)
  rewrite lookup_add_eq.                    (* y = 3 を取り出す。 *)
  rewrite lookup_add_ne.                    (* スキップする。 *)
  rewrite lookup_add_eq.                    (* x = 17 を取り出す。 *)
  - done.                                   (* 計算する。 *)
  - done.                                   (* x = x *)
  - done.                                   (* x <> y *)
  - done.                                   (* y = y *)
Qed.

(* Here's the silly transformation we defined last time. *)
Fixpoint commuter (e : arith) : arith :=
  match e with
  | Const _ => e
  | Var _ => e
  | Plus e1 e2 => Plus (commuter e2) (commuter e1)
  | Minus e1 e2 => Minus (commuter e1) (commuter e2)
                   (* ^-- NB: didn't change the operand order here! *)
  | Times e1 e2 => Times (commuter e2) (commuter e1)
  end.

(* Instead of proving various odds-and-ends properties about it,
 * let's show what we *really* care about: it preserves the
 * *meanings* of expressions! *)
Theorem commuter_ok v e : interp (commuter e) v = interp e v.
Proof.
  elim: e => //= [e1 H1 e2 H2 | e1 H1 e2 H2 | e1 H1 e2 H2].
  - by linear_arithmetic.
  - by linear_arithmetic.
  - rewrite H1 H2. ring.
Qed.
(* Well, that's a relief! ;-) *)

(* Let's also revisit substitution. *)
Fixpoint substitute (inThis : arith) (replaceThis : var) (withThis : arith) : arith :=
  match inThis with
  | Const _ => inThis
  | Var x => if x == replaceThis then withThis else inThis
  | Plus e1 e2 =>
    Plus (substitute e1 replaceThis withThis) (substitute e2 replaceThis withThis)
  | Minus e1 e2 =>
    Minus (substitute e1 replaceThis withThis) (substitute e2 replaceThis withThis)
  | Times e1 e2 =>
    Times (substitute e1 replaceThis withThis) (substitute e2 replaceThis withThis)
  end.

Theorem substitute_ok v replaceThis withThis inThis :
  interp (substitute inThis replaceThis withThis) v
  = interp inThis (v $+ (replaceThis, interp withThis v)).
Proof.
(*
  induct inThis; simplify; try equality.

  (* One case left after our basic heuristic:
   * the variable case, naturally! *)
  cases (x ==v replaceThis); simplify; try equality.
 *)
  elim: inThis => //= [x | e1 H1 e2 H2 | e1 H1 e2 H2 | e1 H1 e2 H2].
  - case: ifP => Heq.              (* case Heq : (x == replaceThis) *)
    + rewrite lookup_add_eq //=.
      by move/eqP in Heq.
    + rewrite lookup_add_ne //=.
      by move/eqP in Heq.
  - by rewrite H1 H2.
  - by rewrite H1 H2.
  - by rewrite H1 H2.
Qed.
(* Great; we seem to have gotten that one right, too. *)

(* Let's also defined a pared-down version of the expression-simplificaton
 * functions from last chapter. *)
Fixpoint doSomeArithmetic (e : arith) : arith :=
  match e with
  | Const _ => e
  | Var _ => e
  | Plus (Const n1) (Const n2) => Const (n1 + n2)
  | Plus e1 e2 => Plus (doSomeArithmetic e1) (doSomeArithmetic e2)
  | Minus e1 e2 => Minus (doSomeArithmetic e1) (doSomeArithmetic e2)
  | Times (Const n1) (Const n2) => Const (n1 * n2)
  | Times e1 e2 => Times (doSomeArithmetic e1) (doSomeArithmetic e2)
  end.

(* 補題を追加した。 suhara *)
Lemma interp_plusE e1 e2 v : interp (Plus e1 e2) v = interp e1 v + interp e2 v.
Proof. done. Qed.

Lemma interp_minusE e1 e2 v : interp (Minus e1 e2) v = interp e1 v - interp e2 v.
Proof. done. Qed.

Lemma interp_timesE e1 e2 v : interp (Times e1 e2) v = interp e1 v * interp e2 v.
Proof. done. Qed.

Theorem doSomeArithmetic_ok e v :
  interp (doSomeArithmetic e) v = interp e v.
Proof.
(*
  induct e; simplify; try equality.

  cases e1; simplify; try equality.
  cases e2; simplify; equality.

  cases e1; simplify; try equality.
  cases e2; simplify; equality.
*)
(* ***** *)
(*
  elim: e => //=.
  - case => [c1 | v1 | e11 e12 | e11 e12 | e11 e12] H1.
    + case => [c2 | v2 | e21 e22 | e21 e22 | e21 e22] H2.
      * done.
      * done.
      * rewrite interp_plusE.
          by rewrite H1 H2.
      * rewrite interp_plusE.
          by rewrite H1 H2.
      * rewrite interp_plusE.
          by rewrite H1 H2.
    + case => [c2 | v2 | e21 e22 | e21 e22 | e21 e22] H2.
      * done.
      * done.
      * rewrite interp_plusE.
          by rewrite H1 H2.
      * rewrite interp_plusE.
          by rewrite H1 H2.
      * rewrite interp_plusE.
          by rewrite H1 H2.
    + case => [c2 | v2 | e21 e22 | e21 e22 | e21 e22] H2.
      * rewrite interp_plusE.
          by rewrite H1 H2.
      * rewrite interp_plusE.
          by rewrite H1 H2.
      * rewrite interp_plusE.
          by rewrite H1 H2.
      * rewrite interp_plusE.
          by rewrite H1 H2.
      * rewrite interp_plusE.
          by rewrite H1 H2.
    + case => [c2 | v2 | e21 e22 | e21 e22 | e21 e22] H2.
      * rewrite interp_plusE.
        rewrite interp_minusE.
          by rewrite H1 H2.
      * rewrite interp_plusE.
        rewrite interp_minusE.
          by rewrite H1 H2.
      * rewrite interp_plusE.
        rewrite interp_minusE.
          by rewrite H1 H2.
      * rewrite interp_plusE.
        rewrite interp_minusE.
          by rewrite H1 H2.
      * rewrite interp_plusE.
        rewrite interp_minusE.
          by rewrite H1 H2.
    + case => [c2 | v2 | e21 e22 | e21 e22 | e21 e22] H2.
      * rewrite interp_plusE.
        rewrite interp_timesE.
          by rewrite H1 H2.
      * rewrite interp_plusE.
        rewrite interp_timesE.
          by rewrite H1 H2.
      * rewrite interp_plusE.
        rewrite interp_timesE.
          by rewrite H1 H2.
      * rewrite interp_plusE.
        rewrite interp_timesE.
          by rewrite H1 H2.
      * rewrite interp_plusE.
        rewrite interp_timesE.
          by rewrite H1 H2.
  - move=> e1 H1 e2 H2.
      by rewrite H1 H2.
  - case => [c1 | v1 | e11 e12 | e11 e12 | e11 e12] H1.
    + case => [c2 | v2 | e21 e22 | e21 e22 | e21 e22] H2.
      * done.
      * done.
      * rewrite interp_timesE.
          by rewrite H1 H2.
      * rewrite interp_timesE.
          by rewrite H1 H2.
      * rewrite interp_timesE.
          by rewrite H1 H2.
    + case => [c2 | v2 | e21 e22 | e21 e22 | e21 e22] H2.
      * done.
      * done.
      * rewrite interp_timesE.
          by rewrite H1 H2.
      * rewrite interp_timesE.
          by rewrite H1 H2.
      * rewrite interp_timesE.
          by rewrite H1 H2.
    + case => [c2 | v2 | e21 e22 | e21 e22 | e21 e22] H2.
      * rewrite interp_plusE.
        rewrite interp_timesE.
          by rewrite H1 H2.
      * rewrite interp_plusE.
        rewrite interp_timesE.
          by rewrite H1 H2.
      * rewrite interp_plusE.
        rewrite interp_timesE.
          by rewrite H1 H2.
      * rewrite interp_plusE.
        rewrite interp_timesE.
          by rewrite H1 H2.
      * rewrite interp_plusE.
        rewrite interp_timesE.
          by rewrite H1 H2.
    + case => [c2 | v2 | e21 e22 | e21 e22 | e21 e22] H2.
      * rewrite interp_timesE.
        rewrite interp_minusE.
          by rewrite H1 H2.
      * rewrite interp_timesE.
        rewrite interp_minusE.
          by rewrite H1 H2.
      * rewrite interp_timesE.
        rewrite interp_minusE.
          by rewrite H1 H2.
      * rewrite interp_timesE.
        rewrite interp_minusE.
          by rewrite H1 H2.
      * rewrite interp_timesE.
        rewrite interp_minusE.
          by rewrite H1 H2.
    + case => [c2 | v2 | e21 e22 | e21 e22 | e21 e22] H2.
      * rewrite interp_timesE.
          by rewrite H1 H2.
      * rewrite interp_timesE.
          by rewrite H1 H2.
      * rewrite interp_timesE.
          by rewrite H1 H2.
      * rewrite interp_timesE.
          by rewrite H1 H2.
      * rewrite interp_timesE.
          by rewrite H1 H2.
 *)
  elim: e => //=.
    by case => [c1 | v1 | e11 e12 | e11 e12 | e11 e12] H1;
                 case => [c2 | v2 | e21 e22 | e21 e22 | e21 e22] H2;
                           try rewrite interp_plusE;
                           try rewrite interp_minusE;
                           try rewrite H1 H2.
    by move=> _ -> _ -> //=.
    by case => [c1 | v1 | e11 e12 | e11 e12 | e11 e12] H1;
                 case => [c2 | v2 | e21 e22 | e21 e22 | e21 e22] H2;
                           try rewrite interp_timesE;
                           try rewrite interp_minusE;
                           try rewrite H1 H2.
Qed.

(* Of course, we're going to get bored if we confine ourselves to arithmetic
 * expressions for the rest of our journey.  Let's get a bit fancier and define
 * a *stack machine*, related to postfix calculators that some of you may have
 * experienced. *)
Inductive instruction :=
| PushConst (n : nat)
| PushVar (x : var)
| Add
| Subtract
| Multiply.

(* What does it all mean?  An interpreter tells us unambiguously! *)
Definition run1 (i : instruction) (v : valuation) (stack : list nat) : list nat :=
  match i with
  | PushConst n => n :: stack
  | PushVar x => (match v $? x with
                  | None => 0
                  | Some n => n
                  end) :: stack
  | Add =>
    match stack with
    | arg2 :: arg1 :: stack' => arg1 + arg2 :: stack'
    | _ => stack (* arbitrary behavior in erroneous case (stack underflow) *)
    end
  | Subtract =>
    match stack with
    | arg2 :: arg1 :: stack' => arg1 - arg2 :: stack'
    | _ => stack (* arbitrary behavior in erroneous case *)
    end
  | Multiply =>
    match stack with
    | arg2 :: arg1 :: stack' => arg1 * arg2 :: stack'
    | _ => stack (* arbitrary behavior in erroneous case *)
    end
  end.

(* That function explained how to run one instruction.
 * Here's how to run several of them. *)
Fixpoint run (ins : seq instruction) (v : valuation) (stack : seq nat) : seq nat :=
  match ins with
  | nil => stack
  | i :: is' => run is' v (run1 i v stack)
  end.

(* Instead of writing fiddly stack programs ourselves, let's *compile*
 * arithmetic expressions into equivalent stack programs. *)
Fixpoint compile (e : arith) : seq instruction :=
  match e with
  | Const n => PushConst n :: nil
  | Var x => PushVar x :: nil
  | Plus e1 e2 => compile e1 ++ compile e2 ++ [:: Add]
  | Minus e1 e2 => compile e1 ++ compile e2 ++ [:: Subtract]
  | Times e1 e2 => compile e1 ++ compile e2 ++ [:: Multiply]
  end.

(* Now, of course, we should prove our compiler correct.
 * Skip down to the next theorem to see the overall correctness statement.
 * It turns out that we need to strengthen the induction hypothesis with a
 * lemma, to push the proof through. *)
Lemma compile_ok' e v ins stack :
  run (compile e ++ ins) v stack = run ins v (interp e v :: stack).
Proof.
  elim: e v ins stack =>
  //= [e1 IHe1 e2 IHe2 | e1 IHe1 e2 IHe2 | e1 IHe1 e2 IHe2] v ins stack.
  (*
    e1 と e2 をコンパイルしてAddと一緒にインストラクション列に追加したものを実行した結果は、
    e1 と e2 を実行て+したものをスタックトップに追加したものと同じ。
   *)
  (* Here we want to use associativity of [++], to get the conclusion to match
   * an induction hypothesis.  Let's ask Coq to search its library for lemmas
   * that would justify such a rewrite, giving a pattern with wildcards, to
   * specify the essential structure that the rewrite should match. *)
  SearchRewrite ((_ ++ _) ++ _).
  (* Ah, we see just the one! *)
(*
  rewrite app_assoc_reverse.
  rewrite IHe1.
  rewrite app_assoc_reverse.
  rewrite IHe2.
  simplify.
  equality.

  rewrite app_assoc_reverse.
  rewrite IHe1.
  rewrite app_assoc_reverse.
  rewrite IHe2.
  simplify.
  equality.

  rewrite app_assoc_reverse.
  rewrite IHe1.
  rewrite app_assoc_reverse.
  rewrite IHe2.
  simplify.
  equality.
 *)
  by rewrite -catA IHe1 -catA IHe2 /=.
  by rewrite -catA IHe1 -catA IHe2 /=.
  by rewrite -catA IHe1 -catA IHe2 /=.
Qed.

(* The overall theorem follows as a simple corollary. *)
Theorem compile_ok e v : run (compile e) v nil = [:: interp e v].
Proof.
(*
  simplify.
*)
(*
  (* To match the form of our lemma, we need to replace [compile e] with
   * [compile e ++ nil], adding a "pointless" concatenation of the empty list.
   * [SearchRewrite] again helps us find a library lemma. *)
  SearchRewrite (_ ++ nil).
  rewrite (app_nil_end (compile e)).
  (* Note that we can use [rewrite] with explicit values of the first few
   * quantified variables of a lemma.  Otherwise, [rewrite] picks an
   * unhelpful place to rewrite.  (Try it and see!) *)
   *)
  rewrite -[compile e]cats0.

  apply: compile_ok'.
  (* Direct appeal to a previously proved lemma *)
Qed.


(* Let's get a bit fancier, moving toward the level of general-purpose
 * imperative languages.  Here's a language of commands, building on the
 * language of expressions we have defined. *)
Inductive cmd :=
| Skip
| Assign (x : var) (e : arith)
| Sequence (c1 c2 : cmd)
| Repeat (e : arith) (body : cmd).

(* That last constructor is for repeating a body command some number of
 * times.  Note that we sneakily avoid constructs that could introduce
 * nontermination, since Coq only accepts terminating programs, and we want to
 * write an interpreter for commands.
 * In contrast to our last one, this interpreter *transforms valuations*.
 * We use a helper function for self-composing a function some number of
 * times. *)

Fixpoint selfCompose {A} (f : A -> A) (n : nat) : A -> A :=
  match n with
  | O => fun x => x
  | S n' => fun x => selfCompose f n' (f x)
  end.

Fixpoint exec (c : cmd) (v : valuation) : valuation :=
  match c with
  | Skip => v
  | Assign x e => v $+ (x, interp e v)
  | Sequence c1 c2 => exec c2 (exec c1 v)
  | Repeat e body => selfCompose (exec body) (interp e v) v
  end.

(* Let's define some programs and prove that they operate in certain ways. *)

Example factorial_ugly :=
  Sequence
    (Assign Literal.a (Const 1))            (* "output" *)
    (Repeat (Var Literal.b)                 (* "input" *)
            (Sequence
               (Assign Literal.a (Times (Var Literal.a) (Var Literal.b)))
               (Assign Literal.b (Minus (Var Literal.b) (Const 1))))).

(* Ouch; that code is hard to read.  Let's introduce some notations to make the
 * concrete syntax more palatable.  We won't explain the general mechanisms on
 * display here, but see the Coq manual for details, or try to reverse-engineer
 * them from our examples. *)
Coercion Const : nat >-> arith.
Coercion Var : Literal >-> arith.  (* Coercion Var : var >-> arith. *)
Infix "+" := Plus : arith_scope.
Infix "-" := Minus : arith_scope.
Infix "*" := Times : arith_scope.
Delimit Scope arith_scope with arith.
Notation "x <- e" := (Assign x e%arith) (at level 75).
Infix ";" := Sequence (at level 76).
Notation "'repeat' e 'doing' body 'done'" := (Repeat e%arith body) (at level 75).

(* OK, let's try that program again. *)
Example factorial :=
  Literal.a <- 1;
  repeat Literal.b doing
    Literal.a <- Literal.a * Literal.b;
    Literal.b <- Literal.b - 1
  done.

(* Now we prove that it really computes factorial.
 * First, a reference implementation as a functional program. *)
Fixpoint fact (n : nat) : nat :=
  match n with
  | O => 1
  | S n' => n * fact n'
  end.

(* To prove that [factorial] is correct, the real action is in a lemma, to be
 * proved by induction, showing that the loop works correctly.  So, let's first
 * assign a name to the loop body alone. *)
Definition factorial_body :=
  Literal.a <- Literal.a * Literal.b;
  Literal.b <- Literal.b - 1.

(* Now for that lemma: self-composition of the body's semantics produces the
 * expected changes in the valuation.
 * Note that here we're careful to put the quantified variable [input] *first*,
 * because the variables coming after it will need to *change* in the course of
 * the induction.  Try switching the order to see what goes wrong if we put
e * [input] later. *)
Lemma factorial_ok' input output v :
  v $? Literal.b = Some input
  -> v $? Literal.a = Some output
  -> selfCompose (exec factorial_body) input v
     = v $+ (Literal.b, 0) $+ (Literal.a, output * fact input).
Proof.
(*
  induct input; simplify.

  maps_equal.
  (* [maps_equal]: prove that two finite maps are equal by considering all
   *   the relevant cases for mappings of different keys. *)

  rewrite H0.
  f_equal.
  linear_arithmetic.

  trivial.
  (* [trivial]: Coq maintains a database of simple proof steps, such as proving
   *   a fact by direct appeal to a matching hypothesis.  [trivial] asks to try
   *   all such simple steps. *)

  rewrite H, H0.
  (* Note the two arguments to one [rewrite]! *)
  rewrite (IHinput (output * S input)).
  (* Note the careful choice of a quantifier instantiation for the IH! *)
  maps_equal.
  f_equal; ring.
  simplify; f_equal; linear_arithmetic.
  simplify; equality.
 *)
  elim: input output v => /= [|n IHn] output v H1 H2.
  - apply: fmap_ext.
    move=> k.
Admitted.

(* Finally, we have the natural correctness condition for factorial as a whole
 * program. *)
Theorem factorial_ok : forall v input,
  v $? Literal.b = Some input
  -> exec factorial v $? Literal.a = Some (fact input).
Proof.
(*
  simplify.
  rewrite H.
  rewrite (factorial_ok' input 1); simplify.
  f_equal; linear_arithmetic.
  trivial.
  trivial.
*)
  simplify.
  rewrite lookup_add_ne.
  rewrite H.
  Check @factorial_ok' input 1.
  rewrite (@factorial_ok' input 1); simplify.
  - by f_equal; linear_arithmetic.
  - by apply: H.
  - reflexivity.
  - by [].
Qed.


(* One last example: let's try to do loop unrolling, for constant iteration
 * counts.  That is, we can duplicate the loop body instead of using an explicit
 * loop. *)

Fixpoint seqself (c : cmd) (n : nat) : cmd :=
  match n with
  | O => Skip
  | S n' => Sequence c (seqself c n')
  end.

Fixpoint unroll (c : cmd) : cmd :=
  match c with
  | Skip => c
  | Assign _ _ => c
  | Sequence c1 c2 => Sequence (unroll c1) (unroll c2)
  | Repeat (Const n) c1 => seqself (unroll c1) n
  (* ^-- the crucial case! *)
  | Repeat e c1 => Repeat e (unroll c1)
  end.

(* This obvious-sounding fact will come in handy: self-composition gives the
 * same result, when passed two functions that map equal inputs to equal
 * outputs. *)
Lemma selfCompose_extensional {A} (f g : A -> A) n x :
  (forall y, f y = g y)
  -> selfCompose f n x = selfCompose g n x.
Proof.
(*
  induct n; simplify; try equality.

  rewrite H.
  apply IHn.
  trivial.
 *)
  elim: n x => //= [n IHn] x H.
  rewrite H.
  by apply: IHn.
Qed.

(* Crucial lemma: [seqself] is acting just like [selfCompose], in a suitable
 * sense. *)
Lemma seqself_ok c n v :
  exec (seqself c n) v = selfCompose (exec c) n v.
Proof.
(*
  induct n; simplify; equality.
 *)
  by elim: n v => //= [n IHn] v.
Qed.

(* The two lemmas we just proved are the main ingredients to prove the natural
 * correctness condition for [unroll]. *)
Theorem unroll_ok c v : exec (unroll c) v = exec c v.
Proof.
(*
  induct c; simplify; try equality.

  cases e; simplify; try equality.

  rewrite seqself_ok.
  apply selfCompose_extensional.
  trivial.

  apply selfCompose_extensional.
  trivial.

  apply selfCompose_extensional.
  trivial.

  apply selfCompose_extensional.
  trivial.

  apply selfCompose_extensional.
  trivial.
 *)

  elim: c v => //= [c1 IHc1 c2 IHc2 v | e c IHc v].
  - by rewrite IHc1 IHc2.
  - case: e => /= [n | x | e1 e2 | e1 e2 | e1 e2].
    + rewrite seqself_ok.
      by apply: selfCompose_extensional.
    + by apply: selfCompose_extensional.
    + by apply: selfCompose_extensional.
    + by apply: selfCompose_extensional.
    + by apply: selfCompose_extensional.
(*
  induct c; simplify; try equality.

  cases e; simplify; try equality.

  rewrite seqself_ok.
  apply selfCompose_extensional.
  trivial.

  apply selfCompose_extensional.
  trivial.

  apply selfCompose_extensional.
  trivial.

  apply selfCompose_extensional.
  trivial.

  apply selfCompose_extensional.
  trivial.
*)
Qed.

(* END *)
