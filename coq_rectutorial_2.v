(** 帰納型のチュートリアル **)
(** A Tutorial on [Co-]Inductive Types in Coq **)


(* 4 Some Proof Techniques Based on Case Analysis *)


(* 4.1 Discrimination of introduction rules *)


Definition Is_zero ( x : nat) :=
  match x with
    | 0 => True
    | _ => False
  end.
Check Is_zero.


Lemma O_is_zero : forall m, m = 0 -> Is_zero m.
  intros m H.
  subst m.                                  (* rewrite H. *)


  (* subst m は、ゴールのmを仮定中の等式を使って置き換える。
  この場合は、rewrite H と同じである。H : m = 0 *)


  simpl.
  
  (* trivial は、applyを自動適用する autoと同じだが、コストに制限がある。
     X = X にだけしか適用できないと考えてよい。 *)
  trivial.
Qed.
Check O_is_zero.
Print O_is_zero.


Theorem S_is_not_O : forall n, S n <> 0.
  red.
  (* red は、ゴールの forall x : c x の c に対してβιζ簡約をおこなう *)
  (* Goal : forall n : nat, S n = 0 -> False *)
  
  intros n Hn.
  apply O_is_zero with (m := S n).
  apply Hn.
Qed.
Print S_is_not_O.


Theorem S_is_not_O' : forall n, S n <> 0.
  intros n.
  (* Goal : S n <> 0 *)
  discriminate.
  (* The tactic discriminate is a special-purpose tactic for proving disequalities
    between two elements of a recursive type introduced by different constructors. *)
Qed.


Theorem disc2 : forall n, S (S n) <> 1. 
  intros n.
  discriminate.
Qed.


Theorem disc3 : forall n, S (S n) = 0 -> forall Q : Prop, Q.
  intros n Hn Q.
  discriminate.
Qed.
Print disc3.




(* 4.2 Injectiveness of introduction rules *)


Lemma inj_pred : forall n m, n = m -> pred n = pred m.
  intros n m eq_n_m.
  (* Goal : pred n = pred m *)
  subst n.                                  (* rewrite eq_n_m. *)
  (* Goal : pred m = pred m *)
  trivial.
Qed.
Print inj_pred.


Eval compute in fun n : nat => pred (S n).  (* n *)
Eval compute in fun n : nat => S (pred n).  (* nにはならない。 *)
Theorem inj : forall n m, S n = S m -> n = m.
  intros n m eq_n_m.


  (* Goal :: n = m *)
  apply inj_pred with (n := S n) (m := S m).
  (* pred (S n) が n になるので、
     S n = S m -> pred (S n) = pred (S m)
     が満たされる。*)


  (* Goal :: S n = S m *)
  trivial.
Qed.
Print inj.


Theorem inj' : forall n m, S n = S m -> n = m.
  intros n m eq_n_m.
  injection eq_n_m.                         (* injection タクティクを使ってみた *)
  intros.
  apply H.
Qed.


Require Import List.
Lemma list_inject : forall (A : Set) (a b : A) (l l' :list A),
  a :: b :: l = b :: a :: l' -> a = b /\ l = l'.


  intros A a b l l' Heq.
  injection Heq.
  intros.                                   (* 以下 auto でもよい。 *)
  split.
  apply H1.
  apply H.
Qed.




(* 4.3 Inversion Techniques *)


Theorem not_le_Sn_0_with_constraints :
  forall n p : nat, S n <= p -> p = 0 -> False.
  intros n p H.
  case H.
  intros.
  discriminate.                             (* S_in_not_O' を参照のこと。 *)
  intros.
  discriminate.
Qed.


Theorem not_le_Sn_0 : forall n : nat, ~ (S n <= 0).
  intros n H.
  eapply not_le_Sn_0_with_constraints; eauto.
Qed.


(* eapply を使わない場合 *)
Theorem not_le_Sn_0''' : forall n : nat, ~ (S n <= 0).
  intros n H.
  apply not_le_Sn_0_with_constraints with (n := n) (p := 0).
  apply H.
  trivial.
Qed.




(* 4.3.1 Interactive mode *)


Theorem not_le_Sn_0' : forall n : nat, ~ (S n <= 0).
  red.
  intros n H.
  inversion H.
Qed.




(* 4.3.2 Static mode *)


Derive Inversion le_Sn_0_inv with (forall n :nat, S n <= 0).


Theorem le_Sn_0'' : forall n p : nat, ~ S n <= 0 .
  intros n p H.
  inversion H using le_Sn_0_inv.
Qed.


Theorem le_reverse_rules :
forall n m : nat, n <= m ->
  n = m \/ exists p, n <= p /\ m = S p.
  intros n m H.
  inversion H.
  left.
  trivial.
  right.
  exists m0.
  split.
  apply H0.
  reflexivity.
Qed.


(* Exercise 4.1 *)


Inductive ArithExp : Set :=
  | Zero : ArithExp
  | Succ : ArithExp -> ArithExp
  | Plus : ArithExp -> ArithExp -> ArithExp.


Inductive RewriteRel : ArithExp -> ArithExp -> Prop :=
  | RewSucc : forall e1 e2 : ArithExp,
      RewriteRel e1 e2 -> RewriteRel (Succ e1) (Succ e2)
  | RewPlus0 : forall e : ArithExp,
      RewriteRel (Plus Zero e) e
  | RewPlusS : forall e1 e2 : ArithExp,
      RewriteRel e1 e2 -> RewriteRel (Plus (Succ e1) e2) (Succ (Plus e1 e2)).


(*
  1. Prove that Zero cannot be rewritten any further.
  2. Prove that an expression of the form “ Succ e ” is always rewritten 
      into an expression of the same form.
*)




(* 5 Inductive Types and Structural Induction *)


Fixpoint plus (n p:nat) {struct n} : nat :=
  match n with
  | 0 => p
  | S m => S (plus m p)
  end.


Fixpoint plus' (n p:nat) {struct p} : nat :=
  match p with
  | 0 => n
  | S q => S (plus' n q)
  end.


Fixpoint plus'' (n p:nat) {struct n} : nat :=
  match n with
  | 0 => p
  | S m => plus'' m (S p)
  end.


Fixpoint even_test' (n:nat) : bool :=
  match n with
  | 0 => true
  | 1 => false
  | S (S p) => even_test' p
  end.


Inductive
  even : nat -> Prop :=
  | evenO : even O
  | evenS : forall n, odd n -> even (S n)
  with
  odd : nat -> Prop :=
    oddS : forall n, even n -> odd (S n).
Eval compute in even 2.                     (* Prop *)


Fixpoint even_test (n:nat) : bool :=
  match n with
  | 0 => true
  | S p => odd_test p
  end
  with odd_test (n:nat) : bool :=
  match n with
  | 0 => false
  | S p => even_test p
  end.
Print even_test.
Eval compute in even_test 2.                (* bool *)


Eval simpl in even_test.                    (* nat -> bool *)
Eval simpl in (fun x:nat => even x).        (* nat -> Prop *)
Eval simpl in (fun x:nat => plus 5 x).      (* nat -> nat *)
Eval simpl in (fun x:nat => even_test (plus 5 x)). (* nat -> bool *)
Eval simpl in (fun x:nat => even_test (plus x 5)). (* nat -> bool *)




(* 5.1 Proofs by Structural Induction *)


(*******)
(* nat *)
(*******)
Print nat_ind.
Print nat_rec.


(* nat_indとnat_recを再定義する。nat_rectを使わないで。 *)
Section Principle_of_Induction.
Variable P : nat -> Prop.
Hypothesis base_case : P 0.
Hypothesis inductive_step : forall n:nat, P n -> P (S n).


Fixpoint nat_ind (n:nat) : (P n) :=
  match n return P n with                   (* return P n は省略できる。 *)
  | 0 => base_case
  | S m => inductive_step m (nat_ind m)
  end.
End Principle_of_Induction.
Check nat_ind.


Section Principle_of_Induction'.
Variable P : nat -> Set.
Hypothesis base_case : P 0.
Hypothesis inductive_step : forall n:nat, P n -> P (S n).


Fixpoint nat_rec (n:nat) : (P n) :=
  match n return P n with
  | 0 => base_case
  | S m => inductive_step m (nat_rec m)
  end.
End Principle_of_Induction'.
Check nat_rec.


Scheme Even_induction := Minimality for even Sort Prop
  with Odd_induction := Minimality for odd Sort Prop.
Check Even_induction.
Print Even_induction.
Check Odd_induction.
Print Odd_induction.




Theorem even_plus_four : forall n:nat, even n -> even ( 4 + n ).
  intros n H.
  elim H using Even_induction with (P0 := fun n => odd ( 4 + n )).
  simpl.
  repeat constructor.
  
  simpl.
  repeat constructor.
  assumption.


  simpl.
  repeat constructor.
  assumption.
Qed.
Print even_plus_four.




Section Principle_of_Double_Induction.
Variable P : nat -> nat -> Prop.
Hypothesis base_case1 : forall m:nat, P 0 m.
Hypothesis base_case2 : forall n:nat, P (S n) 0.
Hypothesis inductive_step : forall n m : nat,
  P n m -> P (S n) (S m).


(**************)
(* nat_double *)
(**************)
Fixpoint nat_double_ind (n m : nat) {struct n} : P n m :=
  match n, m return P n m with
  |    0 ,     x => base_case1 x
  | (S x),     0 => base_case2 x
  | (S x), (S y) => inductive_step x y (nat_double_ind x y)
  end.
Check nat_double_ind.
End Principle_of_Double_Induction.


Section Principle_of_Double_Induction'.
Variable P : nat -> nat -> Set.
Hypothesis base_case1 : forall m : nat, P 0 m.
Hypothesis base_case2 : forall n : nat, P (S n) 0.
Hypothesis inductive_step : forall n m : nat,
  P n m -> P (S n) (S m).


Fixpoint nat_double_rec (n m : nat) {struct n} : P n m :=
  match n, m return P n m with
  |    0 ,     x => base_case1 x
  | (S x),     0 => base_case2 x
  | (S x), (S y) => inductive_step x y (nat_double_rec x y)
  end.
Check nat_double_rec.
End Principle_of_Double_Induction'.




Definition min : nat -> nat -> nat :=
  nat_double_rec
    (fun (x y:nat) => nat)
    (fun (x:nat) => 0)
    (fun (y:nat) => 0)
    (fun (x y r:nat) => S r).


Eval compute in (min 5 8).                  (* 5 : nat *)




(* 5.2 Using Elimination Combinators. *)


Lemma not_circular : forall n:nat, n <> S n.
  intro n.
  apply nat_ind with (P:= fun n => n <> S n).
  discriminate.
  
  red.
  intros n0 Hn0 eqn0sn0.
  injection eqn0sn0.
  trivial.
Qed.


Lemma eq_nat_dec : forall n p:nat, {n = p} + {n <> p}.
  intros n p.
  pattern p, n.
  elim n using nat_double_rec.
  destruct m; auto.
  destruct n0; auto.
  
  intros n0 m H.
  case H.
  intro eq.
  rewrite eq.
  auto.


  intro neq.
  right.
  red.
  injection 1.
  auto.
Qed.


Lemma eq_nat_dec' : forall n p:nat, {n = p}+{n <> p}.
  decide equality.
Qed.




(* Exercise 5.1 *)


(* Exercise 5.2 *)


(* 5.3 Well-founded Recursion *)


Print Acc.
Check Acc.


(* accessibility predicate *)
(* Accの定義が変更されているので、それを修正する *)
Inductive Acc (A : Set) (R : A -> A -> Prop) : A -> Prop :=
  Acc_intro : forall x:A, (forall y:A, R y x -> Acc A R y) -> Acc A R x.
(* Acc nat という指定がいらないようにする *)
Implicit Arguments Acc [A].                 (* 重要 *)
Implicit Arguments Acc_intro [A R].         (* 重要 *)
Print Acc.


(* 本節を通してdivを定義する *)


Lemma minus_smaller_S : forall x y:nat, x - y < S x.
  intros x y; pattern y, x;
  elim x using nat_double_ind.
  destruct m; auto with arith.
  simpl; auto with arith.
  simpl; auto with arith.
Qed.


Lemma minus_smaller_S' : forall x y:nat, x - y < S x.
  intros x y.
  pattern y, x.
  elim x using nat_double_ind.


  intros x0.
  elim x0.
  simpl.
  auto with arith.


  intros.
  simpl.
  auto with arith.


  intros.
  simpl.
  auto with arith.


  intros.
  simpl.
  auto with arith.
Qed.


Lemma minus_smaller_positive :
  forall x y:nat, x <> 0 -> y <> 0 -> x - y < x.
  destruct x; destruct y;
  ( simpl; intros; apply minus_smaller_S ||
  intros; absurd (0=0); auto).
Qed.


Definition minus_decrease :
  forall x y:nat, Acc lt x -> x <> 0 -> y <> 0 -> Acc lt (x - y).
Proof.
  intros x y H.
  case H.


  intros z Hz posy posz.
  apply Hz.
  apply minus_smaller_positive.
  assumption.
  assumption.
Defined.
Print minus_decrease.


Definition div_aux (x y:nat)(H: Acc lt x) : nat.
  fix 3.
  intros.
  refine (if eq_nat_dec x 0
          then 0
          else if eq_nat_dec y 0
               then y
               else S (div_aux (x-y) y _)).
  apply (minus_decrease x y H); auto.
Defined.
Print div_aux.
Check div_aux.


Require Import Wf_nat.
Print lt_wf.
Check lt_wf.


(*
Definition div x y := div_aux x y (lt_wf x).
*)


(* 6 A case study in dependent elimination *)


Require Import Bvector.
Require Import Logic.JMeq.


Lemma vector0_is_vnil_aux :
  forall (A:Set)(n:nat)(v:vector A n), n = 0 -> JMeq v (Vnil A).
Proof.
  destruct v.
  auto.
  intro; discriminate.
Qed.


Lemma vector0_is_vnil :
  forall (A:Set)(v:vector A 0), v = Vnil A.
Proof.
  intros a v; apply JMeq_eq.
  apply vector0_is_vnil_aux.
  trivial.
Qed.


Implicit Arguments Vcons [A n].
Implicit Arguments Vnil [A].
Implicit Arguments Vhead [A n].
Implicit Arguments Vtail [A n].


Definition Vid : forall (A : Set)(n:nat), vector A n -> vector A n.
  destruct n; intro v.
  exact Vnil.
  exact (Vcons (Vhead v) (Vtail v)).
Defined.


Lemma Vid_eq : forall (n:nat) (A:Set)(v:vector A n), v = (Vid _ n v).
  destruct v.
  reflexivity.
  reflexivity.
Qed.


Theorem zero_nil :
  forall (A : Set) (v:vector A 0), v = Vnil. (* A:Setを補う。 *)
Proof.
  intros.
  change (Vnil (A:=A)) with (Vid _ 0 v).
  (* Goal :: v = Vid A 0 v *)
  apply Vid_eq with (n := 0).
Qed.
  
Theorem decomp :
  forall (A : Set) (n : nat) (v : vector A (S n)), v = Vcons (Vhead v) (Vtail v).
Proof.
  intros.
  change (Vcons (Vhead v) (Vtail v)) with (Vid _ (S n) v).
  (* Goal :: Vid A (S n) v *)
  apply Vid_eq.
Defined.


Definition vector_double_rect :
  forall (A:Set) (P: forall (n:nat),(vector A n)->(vector A n) -> Type),
    P 0 Vnil Vnil ->
    (forall n (v1 v2 : vector A n) a b, P n v1 v2 ->
      P (S n) (Vcons a v1) (Vcons b v2)) ->
        forall n (v1 v2 : vector A n), P n v1 v2.
Proof.
  induction n.
  intros; rewrite (zero_nil _ v1); rewrite (zero_nil _ v2).
  auto.
  intros v1 v2; rewrite (decomp _ _ v1);rewrite (decomp _ _ v2).
  apply X0; auto.
Defined.


Definition bitwise_or n v1 v2 : vector bool n :=
  vector_double_rect
    bool
    (fun n v1 v2 => vector bool n)
    Vnil
    (fun n v1 v2 a b r => Vcons (orb a b) r) n v1 v2.


Fixpoint vector_nth (A:Set)(n:nat)(p:nat)(v:vector A p) {struct v} : option A :=
  match n,v with
  | _ , Vnil => None
  | 0 , Vcons b _ _ => Some b
  | S n', Vcons _ p' v' => vector_nth A n' p' v'
  end.


Implicit Arguments vector_nth [A p].


Lemma nth_bitwise :
  forall (n:nat) (v1 v2: vector bool n) i a b,
    vector_nth i v1 = Some a ->
    vector_nth i v2 = Some b ->
    vector_nth i (bitwise_or _ v1 v2) = Some (orb a b).
Proof.
Abort.


(* 続く *)