From mathcomp Require Import all_ssreflect.
Require Import ssr_frap.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
(* Set Print All. *)

Module ArithWithVariables.

  Inductive arith : Set :=
  | Const (n : nat)
  | Var (x : var)
  | Plus (e1 e2 : arith)
  | Times (e1 e2 : arith).

  Example ex1 := Const 42.
  Example ex2 := Plus (Const 1) (Times (Var "x") (Const 3)).

  Fixpoint size (e : arith) : nat :=
    match e with
    | Const _ => 1
    | Var _ => 1
    | Plus e1 e2 => (size e1 + size e2).+1
    | Times e1 e2 => (size e1 + size e2).+1
    end.

  Compute size ex1.
  Compute size ex2.

  Fixpoint depth (e : arith) : nat :=
    match e with
    | Const _ => 1
    | Var _ => 1
    | Plus e1 e2 => (maxn (depth e1) (depth e2)).+1
    | Times e1 e2 => (maxn (depth e1) (depth e2)).+1
    end.

  Compute depth ex1.
  Compute depth ex2.

  Lemma max_le_add m1 n1 m2 n2 : m1 <= m2 -> n1 <= n2 ->
                                 maxn m1 n1 <= m2 + n2.
  Proof.
    rewrite /maxn.
    case H : (m1 < n1) => Hm Hn. (* destruct (m1 < n1) eqn:H => Hm Hn *)
    - rewrite -[n1]add0n. by apply: leq_add.
    - rewrite addnC -[m1]add0n. by apply: leq_add.

    Restart.
    rewrite /maxn.
    case H : (m1 < n1) => Hm Hn.
    - by ssromega.
    - by ssromega.

    Restart.
      by linear_arithmetic.
  Qed.
  
  Theorem depth_le_size e : depth e <= size e.
  Proof.
    elim: e => [n | x | e1 He1 e2 He2 | e1 He1 e2 He2] //=;
      (* rewrite -addnA leq_add2l; *)
      by apply: max_le_add.
    
    Restart.
      by elim: e => //=; linear_arithmetic.
  Qed.
  
  Fixpoint commuter (e : arith) : arith :=
    match e with
    | Const _ => e
    | Var _ => e
    | Plus e1 e2 => Plus (commuter e2) (commuter e1)
    | Times e1 e2 => Times (commuter e2) (commuter e1)
    end.

  Compute commuter ex1.
  Compute commuter ex2.

  Theorem size_commuter e : size (commuter e) = size e.
  Proof.
    by elim: e => //=; linear_arithmetic.
  Qed.
  
  Theorem depth_commuter e : depth (commuter e) = depth e.
  Proof.
    elim: e => //= [e1 He1 e2 He2 | e1 He1 e2 He2];
                 (* congr (_ + _) *)
                 by rewrite He1 He2 maxnC.
  Qed.
  
  Theorem commuter_inverse e : commuter (commuter e) = e.
  Proof.
      by elim: e => //= [e1 He1 e2 He2 | e1 He1 e2 He2]; rewrite He1 He2.
  Qed.

  (* **** *)
  
  Fixpoint substitute (inThis : arith) (replaceThis : var) (withThis : arith) : arith :=
    match inThis with
    | Const _ => inThis
    | Var x =>
      if x == replaceThis then withThis else inThis (* eqType の == を使う。 *)
    | Plus e1 e2 =>
      Plus (substitute e1 replaceThis withThis) (substitute e2 replaceThis withThis)
    | Times e1 e2 =>
      Times (substitute e1 replaceThis withThis) (substitute e2 replaceThis withThis)
    end.

  Lemma max_le_add_c m1 n1 m2 n2 c : m1 <= m2 + c -> n1 <= n2 + c ->
                                 maxn m1 n1 <= maxn m2 n2 + c.
  Proof.
    by linear_arithmetic.
    
    Restart.
    (* linear_arithemtic' の repeat が効いている例 *)
    move=> Hm Hn.
    rewrite {1}/maxn.
    case H1 : (m1 < n1).
    - rewrite /maxn.
      case H2 : (m2 < n2); by ssromega.
    - rewrite /maxn.
      case H2 : (m2 < n2); by ssromega.
  Qed.
  
  Theorem substitute_depth replaceThis withThis inThis :
    depth (substitute inThis replaceThis withThis) <= depth inThis + depth withThis.
  Proof.
    elim: inThis => //= [x | e1 He1 e2 He2 | e1 He1 e2 He2].
    - case H : (x == replaceThis).
      + by linear_arithmetic.
      + rewrite /depth.
        by linear_arithmetic.
    - (* rewrite -addnA leq_add2l. *)
        by apply: max_le_add_c.
    - (* rewrite -addnA leq_add2l. *)
        by apply: max_le_add_c.
  Qed.

  Theorem substitute_self replaceThis inThis :
    substitute inThis replaceThis (Var replaceThis) = inThis.
  Proof.
    elim: inThis => //= [x | e1 He1 e2 He2 | e1 He1 e2 He2].
    - case H : (x == replaceThis).
      + move/eqP in H.
        by rewrite H.
      + done.
    - by rewrite He1 He2.
    - by rewrite He1 He2.
  Qed.
  
  Theorem substitute_commuter replaceThis withThis inThis :
    commuter (substitute inThis replaceThis withThis)
    = substitute (commuter inThis) replaceThis (commuter withThis).
  Proof.
    elim: inThis => //= [x | e1 He1 e2 He2 | e1 He1 e2 He2].
    - by case H : (x == replaceThis).
    - by rewrite He1 He2.
    - by rewrite He1 He2.
  Qed.
  
  (* *Constant folding* is one of the classic compiler optimizations.
   * We repeatedly find opportunities to replace fancier expressions
   * with known constant values. *)
  Fixpoint constantFold (e : arith) : arith :=
    match e with
    | Const _ => e
    | Var _ => e
    | Plus e1 e2 =>
      let e1' := constantFold e1 in
      let e2' := constantFold e2 in
      match e1', e2' with
      | Const n1, Const n2 => Const (n1 + n2)
      | Const 0, _ => e2'
      | _, Const 0 => e1'
      | _, _ => Plus e1' e2'
      end
    | Times e1 e2 =>
      let e1' := constantFold e1 in
      let e2' := constantFold e2 in
      match e1', e2' with
      | Const n1, Const n2 => Const (n1 * n2)
      | Const 1, _ => e2'
      | _, Const 1 => e1'
      | Const 0, _ => Const 0
      | _, Const 0 => Const 0
      | _, _ => Times e1' e2'
      end
    end.

  (* This is supposed to be an *optimization*, so it had better not *increase*
   * the size of an expression!
   * There are enough cases to consider here that we skip straight to
   * the automation.
   * A new scripting construct is [match] patterns with dummy bodies.
   * Such a pattern matches *any* [match] in a goal, over any type! *)
  Theorem size_constantFold e : size (constantFold e) <= size e.
  Proof.
    induction e; simpl;
      repeat match goal with
             | [ |- context[match ?E with _ => _ end] ] =>
               destruct E; simpl in *
             end;
        by ssromega.
  Qed.
  
  (* Business as usual, with another commuting law *)
  Theorem commuter_constantFold e :
    commuter (constantFold e) = constantFold (commuter e).
  Proof.
    (*
    induction e; simpl;
    repeat match goal with
           | [ |- context[match ?E with _ => _ end] ] => destruct E; simpl; simpl in *
           | [ H : ?f _ = ?f _ |- _ ] => inversion H
           | [ |- ?f _ = ?f _ ] => f_equal
           end.
     *)
    (* Error: Out of memory. *)
    Admitted.

  (* To define a further transformation, we first write a roundabout way of
   * testing whether an expression is a constant.
   * This detour happens to be useful to avoid overhead in concert with
   * pattern matching, since Coq internally elaborates wildcard [_] patterns
   * into separate cases for all constructors not considered beforehand.
   * That expansion can create serious code blow-ups, leading to serious
   * proof blow-ups! *)
  Definition isConst (e : arith) : option nat :=
    match e with
    | Const n => Some n
    | _ => None
    end.
  
  (* Our next target is a function that finds multiplications by constants
   * and pushes the multiplications to the leaves of syntax trees,
   * ideally finding constants, which can be replaced by larger constants,
   * not affecting the meanings of expressions.
   * This helper function takes a coefficient [multiplyBy] that should be
   * applied to an expression. *)
  Fixpoint pushMultiplicationInside' (multiplyBy : nat) (e : arith) : arith :=
    match e with
    | Const n => Const (multiplyBy * n)
    | Var _ => Times (Const multiplyBy) e
    | Plus e1 e2 => Plus (pushMultiplicationInside' multiplyBy e1)
                         (pushMultiplicationInside' multiplyBy e2)
    | Times e1 e2 =>
      match isConst e1 with
      | Some k => pushMultiplicationInside' (k * multiplyBy) e2
      | None => Times (pushMultiplicationInside' multiplyBy e1) e2
      end
    end.

  (* The overall transformation just fixes the initial coefficient as [1]. *)
  Definition pushMultiplicationInside (e : arith) : arith :=
    pushMultiplicationInside' 1 e.

  (* Let's prove this boring arithmetic property, so that we may use it below. *)
  Lemma n_times_0 n : n * 0 = 0.
  Proof.
      by linear_arithmetic.
  Qed.
  
  (* A fun fact about pushing multiplication inside:
   * the coefficient has no effect on depth!
   * Let's start by showing any coefficient is equivalent to coefficient 0. *)
  Lemma depth_pushMultiplicationInside'_irrelevance0 e multiplyBy :
    depth (pushMultiplicationInside' multiplyBy e)
    = depth (pushMultiplicationInside' 0 e).
  Proof.
    elim: e multiplyBy => //= [e1 IHe1 e2 IHe2 n | e1 IHe1 e2 IHe2 n].
    - move: (IHe1 n) (IHe2 n).
        by linear_arithmetic.
    - case H : (isConst e1) => /=.
      + rewrite IHe2 n_times_0.
        by linear_arithmetic.
      + rewrite IHe1.
        by linear_arithmetic.
  Qed.
  
  (* It can be remarkably hard to get Coq's automation to be dumb enough to
   * help us demonstrate all of the primitive tactics. ;-)
   * In particular, we can redo the proof in an automated way, without the
   * explicit rewrites. *)
  Lemma depth_pushMultiplicationInside'_irrelevance0_snazzy e multiplyBy :
    depth (pushMultiplicationInside' multiplyBy e)
    = depth (pushMultiplicationInside' 0 e).
  Proof.
    elim: e multiplyBy => //= [e1 IHe1 e2 IHe2 n | e1 IHe1 e2 IHe2 n];
    try match goal with
        | [ |- context[match ?E with _ => _ end] ] => destruct E; simpl
        end; congruence.
    (* オリジナルでは cases と simplify で、
       最後は、equality (= intuition congruence) である。 *)
  Qed.

  (* Now the general corollary about irrelevance of coefficients for depth. *)
  Lemma depth_pushMultiplicationInside'_irrelevance e multiplyBy1 multiplyBy2 :
    depth (pushMultiplicationInside' multiplyBy1 e)
    = depth (pushMultiplicationInside' multiplyBy2 e).
  Proof.
    transitivity (depth (pushMultiplicationInside' 0 e)).
    (* [transitivity X]: when proving [Y = Z], switch to proving [Y = X]
     * and [X = Z]. *)
    - by apply: depth_pushMultiplicationInside'_irrelevance0.
    (* [apply H]: for [H] a hypothesis or previously proved theorem,
     *   establishing some fact that matches the structure of the current
     *   conclusion, switch to proving [H]'s own hypotheses.
     *   This is *backwards reasoning* via a known fact. *)
    - symmetry.
    (* [symmetry]: when proving [X = Y], switch to proving [Y = X]. *)
        by apply: depth_pushMultiplicationInside'_irrelevance0.
  Qed.
  
  (* Let's prove that pushing-inside has only a small effect on depth,
   * considering for now only coefficient 0. *)
  Lemma depth_pushMultiplicationInside' e :
    depth (pushMultiplicationInside' 0 e) <= (depth e).+1.
  Proof.
    elim: e => //= [e1 IHe1 e2 IHe2 | e1 IHe1 e2 IHe2].
    - by linear_arithmetic.
    - case H : (isConst e1) => /=.
      + rewrite n_times_0.
          by linear_arithmetic.
      + by linear_arithmetic.
  Qed.
  
  Hint Rewrite n_times_0.
  (* Registering rewrite hints will get [simplify] to apply them for us
   * automatically! *)
  
  Lemma depth_pushMultiplicationInside'_snazzy e :
    depth (pushMultiplicationInside' 0 e) <= (depth e).+1.
  Proof.
    elim: e => //= [e1 IHe1 e2 IHe2 | e1 IHe1 e2 IHe2];
    try match goal with
        | [ |- context[match ?E with _ => _ end] ] =>
          destruct E; try autorewrite with core; simpl
        end; linear_arithmetic.
    (* オリジナルでは、cases と simplify *)
  Qed.
  
  Theorem depth_pushMultiplicationInside e :
    depth (pushMultiplicationInside e) <= (depth e).+1.
  Proof.
    unfold pushMultiplicationInside.
    (* [unfold X]: replace [X] by its definition. *)
    rewrite depth_pushMultiplicationInside'_irrelevance0.
    by apply depth_pushMultiplicationInside'.
  Qed.
  
End ArithWithVariables.

(* END *)
