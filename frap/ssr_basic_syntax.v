From mathcomp Require Import all_ssreflect.
Require Import Omega.
(*
(* https://github.com/affeldt-aist/seplog/blob/master/lib/ssrnat_ext.v *)
Require Import ssrnat_ext.                  (* ssromega *)
*)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
(* Set Print All. *)

Require Import Ascii.
Require Import String.
Open Scope string_scope.

Ltac ssromega :=
  (repeat ssrnat2coqnat_hypo ;
   ssrnat2coqnat_goal ;
   omega)
with ssrnat2coqnat_hypo :=
  match goal with
    | H : context [?L < ?R] |- _ => move/ltP: H => H
    | H : context [?L <= ?R] |- _ => move/leP: H => H
    | H : context [?L < ?M < ?R] |- _ => let H1 := fresh in case/andP: H => H H1
    | H : context [?L <= ?M < ?R] |- _ => let H1 := fresh in case/andP: H => H H1
    | H : context [?L <= ?M <= ?R] |- _ => let H1 := fresh in case/andP: H => H H1
    | H : context [addn ?L ?R] |- _ => rewrite <- plusE in H
    | H : context [muln ?L ?R] |- _ => rewrite <- multE in H
    | H : context [subn ?L ?R] |- _ => rewrite <- minusE in H
    | H : ?x == _ |- _ => match type of x with nat => move/eqP in H end; idtac x
    | H : _ == ?x |- _ => match type of x with nat => move/eqP in H end; idtac x
    | H : _ != ?x |- _ => match type of x with nat => move/eqP in H end
  end
with ssrnat2coqnat_goal :=
  rewrite -?plusE -?minusE -?multE;
  match goal with
    | |- is_true (_ < _)%nat => apply/ltP
    | |- is_true (_ <= _)%nat => apply/leP
    | |- is_true (_ && _) => apply/andP; split; ssromega
    | |- is_true (?x != _) => match type of x with nat => apply/eqP end
    | |- is_true (_ != ?x) => match type of x with nat => apply/eqP end
    | |- is_true (?x == _) => match type of x with nat => apply/eqP end
    | |- is_true (_ == ?x) => match type of x with nat => apply/eqP end
    | |- _ /\ _ => split; ssromega
    | |- _ \/ _ => (left; ssromega) || (right; ssromega)
    | |- _ => idtac
  end.

Goal forall x y : nat, x + 4 - 2 > y + 4 -> (x + 2) + 2 >= y + 6.
Proof.
  intros.
  ssromega.
Qed.


(* どちらも、m < n での場合分けで良い。 *)
Print maxn.            (* = fun m n : nat => if m < n then n else m *)
Print minn.            (* = fun m n : nat => if m < n then m else n *)

Ltac linear_arithmetic' :=
  intros;
  repeat match goal with
         | [ |- context[maxn ?a ?b] ] =>
           rewrite {1}/maxn; case: (leqP b a); intros

         | [ H : context[maxn ?a ?b] |- _ ] =>
           let H' := fresh in
           rewrite {1}/maxn in H; case: (leqP b a) => H'; try rewrite H' in H

         | [ |- context[minn ?a ?b] ] =>
           rewrite {1}/minn; case: (leqP b a); intros

         | [ H : context[minn ?a ?b] |- _ ] =>
           let H' := fresh in
           rewrite {1}/minn in H; case: (leqP b a) => H';
           try (rewrite leqNgt in H'; move/Bool.negb_true_iff in H'; rewrite H' in H)

         | _ => idtac
         end.
(* case H' : (a < b) の H' が展開できないため、それを使うのを避ける。 *)

Ltac linear_arithmetic :=
  linear_arithmetic';
  try ssromega;
  rewrite //=.

(* sample *)

Goal forall n m, maxn n m = n <-> m <= n.
Proof.
  split.
  - move=> H.
    rewrite {1}/maxn in H.
    case: (leqP m n) => H'.
    + done.
    + rewrite H' in H.
      by ssromega.
  - move=> H.
    rewrite {1}/maxn.
    case: (leqP m n) => H'.
    + done.
    + ssromega.

  Restart.
  
  split.
  - by linear_arithmetic.
  - by linear_arithmetic.
Qed.

Lemma leq_ltF m n : m <= n <-> (n < m) = false.
Proof.
  rewrite leqNgt.
  split.
  - by move/Bool.negb_true_iff.
  - by move=> H; apply/Bool.negb_true_iff.
Qed.

Goal forall n m, minn n m = n <-> n <= m.
Proof.
  split.
  - move=> H.
    rewrite {1}/minn in H.
    case: (leqP m n) => H'.
    + move/leq_ltF in H'.
      rewrite H' in H.
      by ssromega.
    + by ssromega.

  - move=> H.
    rewrite {1}/minn.
    case: (leqP m n) => H'.
    + by ssromega.
    + done.
    
  Restart.
    
  split.
  - by linear_arithmetic.
  - by linear_arithmetic.
Qed.

Goal forall m1 n1 m2 n2, m1 <= m2 -> n1 <= n2 -> maxn m1 n1 <= m2 + n2.
Proof.
  linear_arithmetic'.
  - ssromega.
  - ssromega.

  Restart.
    
  move=> m1 n1 m2 n2.
  rewrite /maxn.
  Check leqP n1 m1.
  case: (leqP n1 m1) => H1 H2 H'.
  - ssromega.
  - ssromega.
Qed.

(* ***** *)

Section SSRAscii.

  Definition eqAscii (a b : ascii) : bool :=
    match ascii_dec a b with
    | left _ => true
    | right _ => false
    end.

  Compute eqAscii "a" "a".                  (* true *)
  Compute eqAscii "a" "b".                  (* false *)
  
  Lemma ascii_eqP (a b : ascii) : reflect (a = b) (eqAscii a b).
  Proof.
    rewrite /eqAscii.
    (* reflect (a = b) (if ascii_dec a b then true else false) *)
    apply: (iffP idP); by case: (ascii_dec a b).
  Qed.
  
  Fail Canonical ascii_eqType := [eqType of ascii].

  Definition ascii_eqMixin := @EqMixin ascii eqAscii ascii_eqP.
  Canonical ascii_eqType := @EqType ascii ascii_eqMixin.

  Canonical ascii_eqType' := [eqType of ascii].
End SSRAscii.

Check ascii_eqType : eqType.
Check "a"%char : ascii.
Check "a"%char : ascii_eqType.

Check true : bool.
Check true : bool_eqType.

Check 1 : nat.
Check 1 : nat_eqType.
  
Section SSRString.
  
  Definition eqString (s t : string) : bool :=
    match string_dec s t with
    | left _ => true
    | right _ => false
    end.
  
  Compute eqString "aaaa" "aaaa".             (* true *)
  Compute eqString "aaaa" "aa".               (* false *)
  
  Lemma string_eqP (x y : string) : reflect (x = y) (eqString x y).
  Proof.
    rewrite /eqString.
    apply: (iffP idP); by case: (string_dec x y).
  Qed.        
  
  Definition string_eqMixin := @EqMixin string eqString string_eqP.
  Canonical string_eqType := @EqType string string_eqMixin.

End SSRString.

Check "aaa" = "aaa" : Prop.
Check "aaa" == "aaa" : bool.
Check "aaa" == "aaa" : Prop.

Notation var := string.

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
    case H : (m1 < n1) => Hm Hn.
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
        end; intuition congruence.
    (* オリジナルでは cases と simplify である。 *)
  Qed.

  (* Now the general corollary about irrelevance of coefficients for depth. *)
  Lemma depth_pushMultiplicationInside'_irrelevance e multiplyBy1 multiplyBy2 :
    depth (pushMultiplicationInside' multiplyBy1 e)
    = depth (pushMultiplicationInside' multiplyBy2 e).
  Proof.
    transitivity (depth (pushMultiplicationInside' 0 e)).
    (* [transitivity X]: when proving [Y = Z], switch to proving [Y = X]
     * and [X = Z]. *)
    apply: depth_pushMultiplicationInside'_irrelevance0.
    (* [apply H]: for [H] a hypothesis or previously proved theorem,
     *   establishing some fact that matches the structure of the current
     *   conclusion, switch to proving [H]'s own hypotheses.
     *   This is *backwards reasoning* via a known fact. *)
    symmetry.
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
    elim: e => //= [e1 IHe1 e2 IHe2 | e1 IHe1 e2 IHe2].
    try match goal with
        | [ |- context[match ?E with _ => _ end] ] => destruct E; simpl
        end; linear_arithmetic.
  Admitted.                                 (* XXXX *)
  
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
