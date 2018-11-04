Require Import Morphisms Program Unicode.Utf8.

(* So far so good, but the variable-less scenario isn't really
 interesting. We now rework approach B to include quotation of
 holes/variables, including recognition of syntactically identical
 ones. *)

Module with_vars.
(* Some random utilities : *)

Lemma sum_assoc {A B C} : (A + B) + C → A + (B + C). intuition. Defined.
Lemma bla {A B C} : (A + B) → A + (B + C). intuition. Defined.
Lemma monkey {A B} : False + A → A + B. intuition. Defined.

(* Again our example term language, this time without plus/one
(they're boring), but with Var added : *)

Inductive Expr (V : Type) :=
| Mult (a b : Expr V)
| Zero
| Var (v : V).

Implicit Arguments Var [[V]].
Implicit Arguments Zero [[V]].
Implicit Arguments Mult [[V]].

(* The expression type is parameterized over the set of variable
 indices. Hence, we diverge from Claudio, who uses nat indices for
 variables, thereby introducing bounds problems and dummy variables
 and other nastiness. *)

(* An expression is only meaningful in the context of a variable assignment : *)

Definition Value := nat.
Definition Vars V := V → Value.

Fixpoint eval {V} (vs : Vars V) (e : Expr V) : Value :=
  match e with
  | Zero => 0
  | Mult a b => eval vs a * eval vs b
  | Var v => vs v
  end.

Instance eval_proper V : Proper (pointwise_relation _ eq ==> eq ==> eq) (@eval V).
Proof.
 repeat intro. subst.
 induction y0; simpl.
 + congruence.
 + reflexivity.
 + now apply H.
Qed.

(* Some simple combinators for variable packs : *)

Definition novars : Vars False := False_rect _.
Definition singlevar (x : Value) : Vars unit := fun _ => x.
Definition merge {A B} (a : Vars A) (b : Vars B) : Vars (A + B) :=
  fun i => match i with
           | inl j => a j
           | inr j => b j
           end.

(* These last two combinators are the "constructors" of an implicitly defined subset of
 Gallina terms (representing Claudio's "heaps") for which we implement syntactic
 lookup with type classes : *)

Section Lookup.
  (* Given a heap and value, Lookup instances give the value's index in the heap : *)

  Class Lookup {A} (x : Value) (f : Vars A) :=
    {
      lookup : A;
      lookup_correct : f lookup = x
    }.
  
  Global Implicit Arguments lookup [[A] [Lookup]].
  
  Context (x : Value) {A B} (va : Vars A) (vb : Vars B).

  (* If the heap is a merge of two heaps and we can find the value's
   index in the left heap, we can access it by indexing the merged
   heap : *)
  
  Global Instance lookup_left `{!Lookup x va} : Lookup x (merge va vb) | 2 :=
    {
      lookup := inl (lookup x va)
    }.
  Proof.
    apply lookup_correct.
  Defined.
  
  (* And vice-versa : *)

  Global Instance lookup_right `{!Lookup x vb} : Lookup x (merge va vb) | 1 :=
    {
      lookup := inr (lookup x vb)
    }.
  Proof.
    apply lookup_correct.
  Defined.
  
  (* If the heap is just a singlevar, we can easily index it. *)

  (* 
  Global Program Instance : Lookup x (singlevar x) := { lookup := tt }.
  説明のため、名前をつける。
   *)
  Global Instance lookup_single : Lookup x (singlevar x) :=
    {
      lookup := tt
    }.
  Proof.
    unfold singlevar.
    reflexivity.
  Defined.
  
  (* Note that we don't have any fallback/default instances at this
  point. We /will/ introduce such an instance for our Quote class
  later on, which will add a new variable to the heap if another Quote
  instance that relies on Lookup into the "current" heap fails. *)
End Lookup.

(* 追加 *)
Section Test.
  (*
    f k = x のとき、lookup x f = k 
   *)
  Variables x y :Value.
  
  Definition f0 := merge (singlevar x) novars.
  Compute f0 (inl tt).                      (* x *)
  Compute lookup x f0.                      (* inl tt *)
  (* inl tt *)
  Check @lookup_left x                      (* Value *)
        unit False                          (* Type *)
        (singlevar x) novars                (* Vars _ *)
        (lookup_single x).                  (* Lookup _ _ *)
  Compute @lookup (unit + False) x f0
          (@lookup_left x                    (* Value *)
                        unit False           (* Type *)
                        (singlevar x) novars (* Vars _ *)
                        (lookup_single x)).  (* Lookup _ _ *)
  
  (* ********** *)
  
  Definition f1 := merge
                     (merge (singlevar x) (singlevar y))
                     (merge (singlevar x) novars).
  Compute f1 (inr (inl tt)) .               (* x *)
  Compute f1 (inl (inl tt)) .               (* x *)
  
  Compute lookup x f1.                      (* inl (inl tt) 優先順位 l , r のとき。 *)
  Compute lookup x f1.                      (* inr (inl tt) 優先順位 r , l のとき。 *)
  Compute @lookup ((unit + unit) + (unit + False)) x f1
          _.
  
  (* 第6引数まで指定すると、有線順位の影響を受けなくなる。 *)
  (* inl (inl tt) *)
  Check @lookup_left x
        (unit + unit) (unit + False)
        (merge (singlevar x) (singlevar y)) (merge (singlevar x) novars)
        (@lookup_left x                           (* Value *)
                      unit unit                   (* Type *)
                      (singlevar x) (singlevar y) (* Vars _ *)
                      (lookup_single x)).         (* Lookup _ _ *)
  Compute @lookup ((unit + unit) + (unit + False)) x f1
          (@lookup_left x
                        (unit + unit) (unit + False)
                        (merge (singlevar x) (singlevar y)) (merge (singlevar x) novars)
                        (@lookup_left x         (* Value *)
                                      unit unit (* Type *)
                                      (singlevar x) (singlevar y) (* Vars _ *)
                                      (lookup_single x))). (* Lookup _ _ *)
  (* inr (inl tt) *)
  Check @lookup_right x
        (unit + unit) (unit + False)
        (merge (singlevar x) (singlevar y)) (merge (singlevar x) novars)
        (@lookup_left x                     (* Value *)
                      unit False            (* Type *)
                      (singlevar x) novars  (* Vars _ *)
                      (lookup_single x)).   (* Lookup _ _ *)
  Compute @lookup ((unit + unit) + (unit + False)) x f1
          (@lookup_right x
                         (unit + unit) (unit + False)
                         (merge (singlevar x) (singlevar y)) (merge (singlevar x) novars)
                         (@lookup_left x          (* Value *)
                                       unit False (* Type *)
                                       (singlevar x) novars (* Vars _ *)
                                       (lookup_single x))). (* Lookup _ _ *)
End Test.

(* One useful operation we need before we get to Quote relates to
 variables and expression evaluation. As its name suggests, map_var
 maps an expression's variable indices. *)

Definition map_var {V W : Type} (f : V → W) : Expr V → Expr W :=
  fix F (e : Expr V) : Expr W :=
    match e with
    | Mult a b => Mult (F a) (F b)
    | Zero => Zero
    | Var v => Var (f v)
    end.

(* An obvious identity is : *)

Lemma eval_map_var {V W} (f : V → W) v e :
  eval v (map_var f e) = eval (v ∘ f) e.
Proof.
 induction e; simpl; try reflexivity.
 rewrite IHe1, IHe2.
 reflexivity.
Qed.

(* Finally, Quote itself : *)

Section Quote.
  (* In Quote, the idea is that V, l, and n are all "input" variables,
  while V' and r are "output" variables (in the sense that we will
  rely on unification to generate them. V and l represent the "current
  heap", n represents the value we want to quote, and V' and r'
  represent the heap of newly encountered variables during the
  quotation.  This explains the type of quote : it is an expression
  that refers either to variables from the old heap, or to newly
  encountered variables.  eval_quote is the usual correctness
  property, which now merges the two heaps. *)

  Class Quote {V} (l : Vars V) (n : Value) {V'} (r : Vars V') :=
    {
      quote : Expr (V + V');
      eval_quote : @eval (V + V') (merge l r) quote = n
    }.

  Implicit Arguments quote [[V] [l] [V'] [r] [Quote]].

  (* Our first instance for Zero is easy. The "novars" in the result
   type reflects the fact that no new variables are encountered. The
   correctness proof is easy enough for Program. *)

  Global Program Instance quote_zero V (v : Vars V) : Quote v 0 novars :=
    {
      quote := Zero
    }.

  (* The instance for multiplication is a bit more complex. The first
   line is just boring variable declarations. The second line is
   important. "Quote x y z" must be read as "quoting y with existing
   heap x generates new heap z", so the second line basically just
   shuffles heaps around.  The third line has some ugly map_var's in
   it because the heap shuffling must be reflected in the variable
   indices, but apart from that it's just constructing a Mult term
   with quoted subterms. *)

  Global Program Instance quote_mult V (v : Vars V) n
         V' (v' : Vars V') m
         V'' (v'' : Vars V'')
         `{!Quote v n v'}
         `{!Quote (merge v v') m v''} : Quote v (n * m) (merge v' v'') :=
    {
      quote := Mult (map_var bla (quote n)) (map_var sum_assoc (quote m))
    }.
  Next Obligation.
  Proof with auto.
    destruct Quote0, Quote1.
    subst. simpl.
    do 2 rewrite eval_map_var.
    f_equal; apply eval_proper; auto; intro; intuition.
  Qed.
  
  (* Now follows the instance where we recognize values that are
   already in the heap. This is expressed by the Lookup requirement,
   which will only be fulfilled if the Lookup instances defined above
   can find the value in the heap. The novars in the [Quote v x
   novars] result reflects that this quotation does not generate new
   variables. *)

  Global Program Instance quote_old_var V (v : Vars V) x {i : Lookup x v} :
    Quote v x novars | 8 :=
    {
      quote := Var (inl (lookup x v))
    }.
  Next Obligation.
  Proof.
    apply lookup_correct.
  Qed.

  (* Finally, the instance for new variables. We give this lower
   priority so that it is only used if Lookup fails. *)

  Global Program Instance quote_new_var V (v : Vars V) x : Quote v x (singlevar x) | 9 :=
    {
      quote := Var (inr tt)
    }.
End Quote.

(* Note : Explicitly using dynamically configured variable index sets
 instead of plain lists not only removes the need for an awkward dummy
 value to cope with out-of-bounds accesses, but also means that we can
 prove the correctness class fields in Lookup/Quote without having to
 take the potential for out-of-bounds indexing into account (which
 would be a nightmare). *)

(* When quoting something from scratch we will want to start with an
 empty heap.  To avoid having to mention this, we define quote' and
 eval_quote' : *)

Definition quote' : ∀ x {V'} {v : Vars V'} {d : Quote novars x v}, Expr _ := @quote _ _.

Definition eval_quote' : ∀ x {V'} {v : Vars V'} {d : Quote novars x v},
    (eval (merge novars v) quote) = x := @eval_quote _ _ .

Implicit Arguments quote' [[V'] [v] [d]].
Implicit Arguments eval_quote' [[V'] [v] [d]].

(* Time for some tests! *)

Goal ∀ x y (P : Value → Prop), P ((x * y) * (x * 0)).
  intros.
  rewrite <- (eval_quote' _).
    (* turns the goal into
         P (eval some_variable_pack_composed_from_combinators quote)
    *)
  simpl quote.
Admitted.

(* We can also inspect quotations more directly : *)

(* 追加 *)
Section Test2.
  Check eval.

  (* 
     eval vars expr = value のとき、 quote' value vars = expr
   *)
  Variables x y : Value.
  
  Check eval
        (merge novars (singlevar x))
        (Mult (Var (inr ())) Zero).
  Goal eval
       (merge novars (singlevar x))
       (Mult (Var (inr ())) Zero)
  = x * 0.
  Proof.
    simpl.
    unfold singlevar.
    easy.
  Qed.
  
  Set Printing Implicit.
  Check @quote' (x * 0)
        (unit + False)
        (merge (singlevar x) novars)
        (@quote_mult False novars x unit (singlevar x) 0 False novars
                     (quote_new_var False novars x)
                     (quote_zero (False + unit)
                                 (@merge False unit novars (singlevar x)))).
   Compute @quote' (x * 0)
          (unit + False)
          (merge (singlevar x) novars)
          _.

  Check @quote
        False novars
        (x * 0)
        (unit + False) (merge (singlevar x) novars)
        _.
  Compute @quote
          False novars
          (x * 0)
          (unit + False) (merge (singlevar x) novars)
          _.
  (* 
     = Mult (Var (inr (inl ()))) Zero
     : Expr (False + (() + False))
   *)
  
  
  (* ********** *)
  
  Check eval
        (merge novars
               (merge
                  (merge (singlevar x) (singlevar y))
                  (merge (singlevar x) novars)))
        (Mult (Mult (Var (inr (inl (inl ())))) (Var (inr (inl (inr ())))))
              (Mult (Var (inr (inl (inl ())))) Zero)).
  Goal eval
       (merge novars
              (merge
                 (merge (singlevar x) (singlevar y))
                 (merge (singlevar x) novars)))
       (Mult (Mult (Var (inr (inl (inl ())))) (Var (inr (inl (inr ())))))
             (Mult (Var (inr (inl (inl ())))) Zero))
  = ((x * y) * (x * 0)).
  Proof.
    simpl.
    unfold singlevar.
    easy.
  Qed.
  
  Check @quote' ((x * y) * (x * 0))
        ((unit + unit) + (unit + False))
        (merge
           (merge (singlevar x) (singlevar y))
           (merge (singlevar x) novars))
        (@quote_mult False novars (x * y) (() + ())
                     (@merge () () (singlevar x) (singlevar y)) (x * 0) (() + False)
                     (@merge () False (singlevar x) novars)
                     (@quote_mult False novars x () (singlevar x) y () (singlevar y)
                                  (quote_new_var False novars x)
                                  (quote_new_var (False + ())
                                                 (@merge False () novars (singlevar x)) y))
                     (@quote_mult (False + (() + ()))
                                  (@merge False (() + ()) novars
                                          (@merge () () (singlevar x) (singlevar y))) x 
                                  () (singlevar x) 0 False novars
                                  (quote_new_var (False + (() + ()))
                                                 (@merge False (() + ()) novars
                                                         (@merge () () (singlevar x) (singlevar y))) x)
                                  (quote_zero (False + (() + ()) + ())
                                              (@merge (False + (() + ())) ()
                                                      (@merge False (() + ()) novars
                                                              (@merge () () (singlevar x) (singlevar y)))
                                                      (singlevar x))))).
  Compute @quote' ((x * y) * (x * 0))
          ((unit + unit) + (unit + False))
          (merge
             (merge (singlevar x) (singlevar y))
             (merge (singlevar x) novars))
          _.
  
  Check @quote False novars ((x * y) * (x * 0))
        ((unit + unit) + (unit + False))
        (merge
           (merge (singlevar x) (singlevar y))
           (merge (singlevar x) novars))
        _.
  Compute @quote False novars ((x * y) * (x * 0))
          ((unit + unit) + (unit + False))
          (merge
             (merge (singlevar x) (singlevar y))
             (merge (singlevar x) novars))
          _.
  (* 
     = Mult (Mult (Var (inr (inl (inl ())))) (Var (inr (inl (inr ())))))
            (Mult (Var (inr (inl (inl ())))) Zero)
            
       : Expr (False + (() + () + (False + False)))
   *)
End Test2.

Section inspect.
  Variables x y : Value.
  Eval compute in quote' ((x * y) * (x * 0)).
    (* = Mult (Mult (Var (inr (inl (inl ())))) (Var (inr (inl (inr ())))))
           (Mult (Var (inr (inl (inl ())))) Zero)
       : Expr (False + (() + () + (False + False))) *)

  (* The second occurrence of (Var (inr (inl (inl ())))) means
   the quoting has successfully noticed that it's the same
   expression. *)

  (* The two units in the generated variable index type reflect the
   fact that the expression contains two variables. *)

  (* I think adding some additional Quote instances might let us
   get rid of the False's, but at the moment I see little reason to. *)
End inspect.

(* If we want to quote an equation between two expressions we should make
 sure that the both sides refer to the same variable pack, and for that we write a
 little utility function. It does the same kind of shuffling that the mult
 Quote instance did. *)

Lemma quote_equality {V} {v : Vars V}
      {V'} {v' : Vars V'}
      (l r : Value)
      `{!Quote novars l v}
      `{!Quote v r v'} :
  let heap := (merge v v') in
  eval heap (map_var monkey quote) = eval heap quote → l = r.
Proof with intuition.
  destruct Quote0 as [lq []].
  destruct Quote1 as [rq []].
  intros heap H.
  subst heap. simpl in H.
  rewrite <- H, eval_map_var.
  apply eval_proper... intro...
Qed.

Goal ∀ x y, x * y = y * x.
  intros.
  apply (quote_equality _ _).
  simpl quote.
  unfold map_var, monkey, sum_rect.
Admitted.

End with_vars.

(* END *)
