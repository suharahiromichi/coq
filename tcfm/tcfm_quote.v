(* GITCRC *)

Require Import ZArith.

Section binop.
(**
A Gentle Introduction to Type Classes and Relations in Coq
の
Chapter 3.9.2 Operational Type Classes の前半から
*)

  Set Implicit Arguments.
  Open Scope Z_scope.
  
  (* Operational Type Classes:  *)
  Class monoid_binop (A : Type) := monoid_op : A -> A -> A.
  Notation "x \* y" := (monoid_op x y) (at level 40, left associativity).
  
  Instance Z_mult_op : monoid_binop Z | 1 := Zmult. (* monoid_binop の優先順位 1 *)
  Instance Z_plus_op : monoid_binop Z | 2 := Zplus. (* monoid_binop の優先順位 2 *)
  
  (* monoid_binop の優先度の高い、数字が若い、ほうが使われる。 *)
  Compute 2 \* 5.                              (* 7 or 10 *)
End binop.

(* TCfM *)

Require Import Morphisms Program Unicode.Utf8.

Definition Value := nat.
Definition Vars V := V → Value.

Lemma sum_assoc {A B C} : (A + B) + C → A + (B + C).
  intuition.
Defined.

Lemma bla {A B C} : (A + B) → A + (B + C).
  intuition.
Defined.

Lemma monkey {A B} : False  +  A → A  +  B.
  intuition.
Defined.

Inductive Expr (V : Type) :=
| Mult (a b : Expr V)
| Zero
| Var (v : V).

Implicit Arguments Var [[V]].
Implicit Arguments Zero [[V]].
Implicit Arguments Mult [[V]].

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
 - congruence.
 - reflexivity.
 - now apply H.
Qed.

(* Some simple combinators for variable packs : *)

Definition novars : Vars False := False_rect _.
Definition singlevar (x : Value) : Vars unit := fun _ => x.
Definition merge {A B} (a : Vars A) (b : Vars B) : Vars (A + B) :=
  fun i => match i with
           | inl j => a j
           | inr j => b j
           end.

Section Lookup.

  Class Lookup {A} (x : Value) (f : Vars A) :=
    {
      lookup : A;
      lookup_correct : f lookup = x
    }.

  Global Implicit Arguments lookup [[A] [Lookup]].

  Context (x : Value) {A B} (va : Vars A) (vb : Vars B).

  Global Instance lookup_left `{!Lookup x va} : Lookup x (merge va vb) :=
    {
      lookup := inl (lookup x va)
    }.
  Proof.
    apply lookup_correct.
  Defined.
  
  Global Instance lookup_right `{!Lookup x vb} : Lookup x (merge va vb) :=
    {
      lookup := inr (lookup x vb)
    }.
  Proof.
    apply lookup_correct.
  Defined.

  (* If the heap is just a singlevar, we can easily index it. *)
  
  Global Program Instance : Lookup x (singlevar x) :=
    {
      lookup := tt
    }.

End Lookup.


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
  
  Class Quote {V} (l : Vars V) (n : Value) {V'} (r : Vars V') :=
    {
      quote : Expr (V + V');
      eval_quote : @eval (V+V') (merge l r) quote = n
    }.
  
  Implicit Arguments quote [[V] [l] [V'] [r] [Quote]].

  Global Program Instance quote_zero V (v : Vars V) : Quote v 0 novars :=
    {
      quote := Zero
    }.
  
  Global Program Instance quote_mult V (v : Vars V) n
         V' (v' : Vars V') m V'' (v'' : Vars V'')
         `{!Quote v n v'}
         `{!Quote (merge v v') m v''} : Quote v (n * m) (merge v' v'') :=
    {
      quote := Mult (map_var bla (quote n)) (map_var sum_assoc (quote m))
    }.
  Next Obligation.
  Proof.
    destruct Quote0, Quote1.
    subst. simpl.
    do 2 rewrite eval_map_var.
    f_equal; apply eval_proper; auto; intro; intuition.
  Qed.
  
  Global Program Instance quote_old_var V (v : Vars V) x {i : Lookup x v} :
    Quote v x novars | 8 :=
    {
      quote := Var (inl (lookup x v))
    }.
  Next Obligation.
  Proof.
    apply lookup_correct.
  Qed.
  
  Global Program Instance quote_new_var V (v : Vars V) x :
    Quote v x (singlevar x) | 9 :=
    {
      quote := Var (inr tt)
    }.
  
End Quote.

Check @quote : ∀ (V : Type) (l : Vars V) (n : Value) (V' : Type) (r : Vars V'), 
    Quote l n r → Expr (V + V').

Check @eval_quote : ∀ (V : Type) (l : Vars V) (n : Value) (V' : Type) (r : Vars V') 
                       (Quote : Quote l n r), eval (merge l r) quote = n.


(* When quoting something from scratch we will want to start with an empty heap.
   To avoid having to mention this, we define quote' and eval_quote': *)

(* 
Definition quote': ∀ x {V'} {v: Vars V'} {d: Quote novars x v}, Expr _ := @quote _ _.
 *)
Definition quote' x {V'} {v : Vars V'} {d : Quote novars x v} :
  Expr (False + V').
Proof.
  destruct d.
  easy.
Defined.

(*
Definition eval_quote': ∀ x {V'} {v: Vars V'} {d: Quote novars x v},
  eval (merge novars v) quote = x
    := @eval_quote _ _ .
*)
Definition eval_quote' x {V'} {v : Vars V'} {d : Quote novars x v} :
    eval (merge novars v) quote = x.
Proof.
  intros.
  destruct d.
  unfold quote.
  easy.
Defined.

Implicit Arguments quote' [[V'] [v] [d]].
Implicit Arguments eval_quote' [[V'] [v] [d]].

(* Time for some tests! *)

Goal ∀ x y (P : Value → Prop), P ((x * y) * (x * 0)).
  intros.
  Check eval_quote.
  Check eval_quote'.
  rewrite <- eval_quote.
  rewrite <- (eval_quote' _).
    (* turns the goal into
         P (eval some_variable_pack_composed_from_combinators quote)
    *)
  simpl quote.
Admitted.

(* We can also inspect quotations more directly : *)

Section inspect.
  Variables x y : Value.
  
  Eval compute in quote.                    (* Zero *)
  
  Check @quote _     _      x _ _ _ : Expr (() + False). (* これはだめとする。 *)
  Check @quote False novars x _ _ _ : Expr (False + ()).
  Check quote' x                    : Expr (False + ()).

  Compute @quote _     _      x _ _ _.      (* = Var (inl ()) *)
  Compute @quote False novars x _ _ _.      (* = Var (inr ()) *)
  Compute quote' x.                         (* = Var (inr ()) *)
  
  Check quote' 0 : Expr (False + False).
  Check quote' x : Expr (False + ()).
  Check quote' y : Expr (False + ()).
  Check quote' (x * 0) : Expr (False + (() + False)).
  Check quote' (x * y) : Expr (False + (() + ())).
  Check quote' ((x * y) * (x * 0)) : Expr (False + (() + () + (False + False))).

  Check @quote False novars ((x * y) * (x * 0)) _ _ _ : Expr (False + (() + () + (False + False))).

  Eval compute in quote' 0.       (* = Zero *)
  Eval compute in quote' x.       (* = Var (inr tt) *)
  Eval compute in quote' y.       (* = Var (inr tt) *)
  Eval compute in quote' (x * 0). (* = Mult (Var (inr (inl tt))) Zero *)
  Eval compute in quote' (x * y). (* = Mult (Var (inr (inl tt))) (Var (inr (inr tt))) *)
  Eval compute in quote' ((x * y) * (x * 0)).
  (* = Mult (Mult (Var (inr (inl (inl ())))) (Var (inr (inl (inr ())))))
     (Mult (Var (inr (inl (inl ())))) Zero) *)
  
  Check @eval_quote False novars 0 _ _ _ : eval (merge novars novars) quote = 0.
  Check eval_quote' 0 : eval (merge novars novars) quote = 0.
  
  Check @eval_quote _     _      x _ _ _ : eval (merge (singlevar x) novars) quote = x.
  (* ↑×とする。 *)
  Check @eval_quote False novars x _ _ _ : eval (merge novars (singlevar x)) quote = x.
  Check eval_quote' x : eval (merge novars (singlevar x)) quote = x.

  Compute @eval_quote _     _      x _ _ _.
  (* ↑×とする。 *)
  Compute @eval_quote False novars x _ _ _.
  Compute eval_quote' x.

  
  
  Check eval_quote' y : eval (merge novars (singlevar y)) quote = y.
  Check eval_quote' (x * 0) :
    eval (merge novars (merge (singlevar x) novars)) quote = x * 0.
  Check eval_quote' (x * y) :
    eval (merge novars (merge (singlevar x) (singlevar y))) quote = x * y.
  Check eval_quote' ((x * y) * (x * 0)) :
    eval
      (merge novars
             (merge (merge (singlevar x) (singlevar y)) (merge novars novars))) quote =
    x * y * (x * 0).
  
  
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

Lemma quote_equality {V} {v : Vars V} {V'} {v' : Vars V'} (l r : Value) `{!Quote novars l v} `{!Quote v r v'} :
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
