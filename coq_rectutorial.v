(** 帰納型のチュートリアル **)
(** A Tutorial on [Co-]Inductive Types in Coq **)


(* 2 Introducing Inductive Types *)


Inductive nat : Set :=
  | O : nat
  | S : nat -> nat.


Print nat.
Check nat.
Check O.
Check S.
Check (S (S (S O))).                        (* S (S (S O)) *)


Reset nat.
Print nat.
Check nat.
Check O.
Check S.
Check (S (S (S O))).                        (* 3 *)




(* 2.1 Lists *)
Require Import List.
Print list.                                 (* nil, cons *)


(*
Inductive list (A : Type) : Type :=
    nil : list A | cons : A -> list A -> list A
*)


Check list.                                 (* Type -> Type *)
Check (list nat).                           (* Set *)
Check (nil (A:= nat)).                      (* list nat *)
Check (nil (A:= nat -> nat)).               (* list (nat -> nat) *)
Check (fun A: Set => (cons (A:=A))).
Check (cons 3 (cons 2 nil)).




(* 2.2 Vectors. *)


Require Import Bvector.
Print vector.                               (* Vnil, Vcons *)


Check (Vnil nat).                           (* vector nat 0 *)
Check (fun (A:Set)(a:A) => Vcons _ a _ (Vnil _)).
Check (Vcons _ 5 _ (Vcons _ 3 _ (Vnil _))).


Check (Vcons _ 3 _ (Vnil _)).


Check (Vcons _   1  _ (Vcons _   2  _ (Vcons _   3 _ (Vnil _  )))). (* vector nat 3 *)
Check (Vcons nat 1  2 (Vcons nat 2  1 (Vcons nat 3 0 (Vnil nat)))). (* vector nat 3 *)
Check (vector nat 3).                       (* natの3個の要素からなるベクター *)




(* 2.3 The contradictory proposition. *)


Print False.                                (* Inductive False : Prop := *)
(* Notice that no constructor is given in this definition. *)




(* 2.4 The tautological proposition. *)


Print True.                                 (* Inductive True : Prop := I : True *)
(* only one element I. *)




(* 2.5 Relations as inductive types. *)


Print le.                                   (* le_n, le_S *)
(*
  Inductive le (n : nat) : nat -> Prop :=   (* (le n) : (nat -> Prop) *)
  | le_n : n <= n
  | le_S : forall m : nat, n <= m -> n <= S m.
*)


Theorem zero_leq_three: 0 <= 3.
  apply le_S.
  apply le_S.
  apply le_S.
  apply le_n.
  Restart.


  constructor 2.                            (* constructor だけでもよい *)
  constructor 2.                            (* constructor だけでもよい *)
  constructor 2.                            (* constructor だけでもよい *)
  constructor 1.                            (* constructor だけでもよい *)
  Restart.


  repeat constructor.
Qed.


Print zero_leq_three.
(*
  zero_leq_three = le_S 0 2 (le_S 0 1 (le_S 0 0 (le_n 0)))
*)


Print lt.


Lemma zero_lt_three : 0 < 3.


  (* Goal : 0 < 3 *)
  unfold lt.
  (* Goal : 1 <= 3 *)


  repeat constructor.
Qed.




(* 2.6 The propositional equality type. *)


Print eq.                                   (* refl_equal *)


(* The type system of Coq allows us to consider equality
  between various kinds of terms:
  elements of a set, proofs, propositions, types, and so on.
*)


Lemma eq_3_3 : 2 + 1 = 3.
  apply refl_equal.
  Restart.


  reflexivity.
Qed.


Lemma eq_3_3' : 1 + 2 = 3.
  apply eq_3_3.
Qed.


Lemma eq_3x4_3x4 : (2*6) = (3*4).
  reflexivity.
Qed.
Print eq_3x4_3x4.                           (* refl_equal (3 * 4) *)


Lemma eq_proof_proof : refl_equal (2*6) = refl_equal (3*4).
  reflexivity.
Qed.
Print eq_proof_proof.                       (* refl_equal (refl_equal (3 * 4)) *)


Lemma eq_lt_le : (2 < 4) = (3 <= 4).
  reflexivity.
Qed.
Print eq_lt_le.


Lemma eq_nat_nat : nat = nat.
  reflexivity.
Qed.
Print eq_nat_nat.                           (* refl_equal nat *)


Lemma eq_Set_Set : Set = Set.
  reflexivity.
Qed.
Print eq_Set_Set.                           (* refl_equal Set *)


(* 2.7 Logical connectives. *)


(* conjunction、論理積 *)
Print and.
(*
  Inductive and (A B : Prop) : Prop :=
  | conj : A -> B -> A /\ B.
*)


(* disjunction、論理和 *)
Print or.
(*
  Inductive or (A B : Prop) : Prop :=
  | or_introl : A -> A \/ B
  | or_intror : B -> A \/ B.
*)


(* the type sumbool is a disjunction but with computational contents. *)
Print sumbool.
(*
  Inductive sumbool (A B : Prop) : Set :=
  | left : A -> {A} + {B}
  | right : B -> {A} + {B}.
*)


Require Import Compare_dec.
Check le_lt_dec.                            (* forall n m : nat, {n <= m} + {m < n} *)


Definition max (n p :nat) :=
  match le_lt_dec n p with
  | left _ => p
  | right _ => n
  end.




Theorem le_max : forall n p, n <= p -> max n p = p.
  intros.
  unfold max.
  case (le_lt_dec n p).
  
  (* Goal : n <= p -> p = p *)
  reflexivity.                              (* 「->」が前についていても、問題ない *)


  (* Goal : p < n -> n = p *)
  intros.
  absurd (p < p).
  eauto with arith.
  eauto with arith.
Qed.
Extraction max.




(* 2.8 The existential quantifier. *)


Print ex.
(*
  Inductive ex (A : Type) (P : A -> Prop) : Prop :=
    ex_intro : forall x : A, P x -> ex P.
*)


(* 2.9 Mutually Dependent Definitions *)


Inductive tree(A:Set) : Set :=
  node : A -> forest A -> tree A
    with forest (A: Set) : Set :=
    | nochild : forest A
    | addchild : tree A -> forest A -> forest A.


Inductive
  even : nat -> Prop :=
  | evenO : even O
  | evenS : forall n, odd n -> even (S n)
with
  odd : nat -> Prop :=
    oddS : forall n, even n -> odd (S n).


Lemma odd_3 : odd 3.
  simpl.
  apply oddS.
  apply evenS.
  apply oddS.
  apply evenO.
Qed.
Print odd_3.


Lemma odd_49 : odd (7 * 7).
  simpl; repeat constructor.
Qed.
Print odd_49.




(* 3 Case Analysis and Pattern-matching *)


(* 3.1 Non-dependent Case Analysis *)


(* In most of the cases, Coq is able to infer the type B of the object defined,
  so the “return B” part can be omitted. *)


Definition Is_Zero (n:nat) :=
  match n return Prop with                  (* return Prop は省略できる。 *)
  | O => True
  | S p => False
  end.


(* 3.1.1 Example: the predecessor function. *)


Definition pred (n:nat) :=
  match n return nat with                   (* return nat は省略できる。 *)
  | O => O
  | S m => m
  end.


Eval simpl in pred 56.                      (* 55 *)
Eval simpl in pred 0.                       (* 0 *)
Eval simpl in fun p => pred (S p).          (* fun p : nat => p *)


Definition xorb (b1 b2:bool) :=
  match b1, b2 with
  | false, true => true
  | true, false => true
  | _ , _ => false
end.
Print xorb.




(* 3.2 Dependent Case Analysis *)


(* 3.2.1 Example: strong specification of the predecessor function. *)


Definition pred_spec (n:nat) :=
  {m:nat | n = 0 /\ m = 0 \/ n = S m}.


Definition predecessor : forall n:nat, pred_spec n.
  intros.
  case n.


  (* Goal : pred_spec 0 *)
  unfold pred_spec.
  exists 0.
  auto.


  (* Gaol : pred_spec (S n0) *)
  intros.
  unfold pred_spec.
  exists n0.
  auto.
Qed.
Print predecessor.
Extraction predecessor.


(* Exercise 3.1 *)
Theorem nat_expand :
  forall n:nat,
  n = match n return nat with                   (* return nat は省略できる。 *)
      | 0 => 0
      | S p => S p
      end.


  intros.
  case n.


  (* Goal : 0 = 0 *)
  reflexivity.


  (* forall n0 : nat, S n0 = S n0 *)    
  intros.
  reflexivity.
Qed.
Print nat_expand.
Extraction nat_expand.




(* 3.3 Some Examples of Case Analysis *)


(* 3.3.1 The Empty Type *)


Theorem fromFalse : False -> 0=1.
  intros.
  contradiction.
Qed.
Print fromFalse.
Extraction fromFalse.


Print not.                                  (* fun A : Prop => A -> False *)
Locate "~ _".                               (* ~ x := not x *)


Fact Nosense : 0 <> 0 -> 2 = 3.
  intro H.
  case H.
  reflexivity.
Qed.




(* 3.3.2 The Equality Type *)


Theorem trans : forall n m p : nat, n = m -> m = p -> n = p.
  intros n m p H H0.
  case H0.
  apply H.
Qed.


(* Exercise 3.2 Prove the symmetry property of equality. *)


Theorem trans' : forall n m p : nat, n = m -> m = p -> n = p.
  intros n m p H H0.
  (* H : n = m *)
  rewrite -> H.                             (* 左辺を -> 右辺で置き換える。->は省ける。*)
  apply H0.
Qed.


Print trans.
Print trans'.


Lemma Rw : forall x y: nat, y = y * x -> y * x * x = y.
  intros x y e.
  rewrite <- e. rewrite <- e.               (* do 2 rewrite <- e. としてもよい。 *)
  reflexivity.
Qed.


Require Import Arith.
Print mult_1_l.                             (* _１_L *) (* forall n : nat, 1 * n = n *)
Print mult_plus_distr_r.
                                  (* forall n m p : nat, (n + m) * p = n * p + m * p *)


Lemma mult_distr_S : forall n p : nat, n * p + p = (S n) * p.
  intros n p.
  simpl.
  apply plus_comm.                          (* Library Coq.Arith.Plus *)
Qed.


Lemma four_n : forall n : nat, n + n + n + n = 4 * n.
  intro n.
  rewrite <- (mult_1_l n).
  Restart.


  intro n.
  pattern n at 1.
  rewrite <- mult_1_l.
  rewrite mult_distr_S.
  rewrite mult_distr_S.
  rewrite mult_distr_S.
  reflexivity.
Qed.




(* 3.3.3 The Predicate n <= m *)


Lemma predecessor_of_positive :
  forall n, 1 <= n -> exists p : nat, n = S p.
  intros n H.
  case H.                           (* apply nat_ind with (n := n) in H. *)
  
  (* exists p : nat, 1 = S p *)
  exists 0.
  reflexivity.


  (* forall m : nat, 1 <= m -> exists p : nat, S m = S p *)
  intros m H0.
  exists m.
  reflexivity.
Qed.




(* 3.3.4 Vectors *)


(* For instance, let us define a function for computing the tail of any vector. *)


Definition Vtail_total (A : Set) (n : nat) (v : vector A n) : vector A (pred n) :=
  match v in (vector _ n0) return (vector A (pred n0)) with
  | Vnil => Vnil A
  | Vcons _ n0 v0 => v0
  end.




(* 3.4 Case Analysis and Logical Paradoxes *)


(* 3.4.1 The Positivity Condition *)


Section Paradox.
Variable Lambda : Set.
Variable lambda : (Lambda -> False) -> Lambda.


Variable matchL : Lambda ->
  forall Q : Prop, ((Lambda -> False) -> Q) -> Q.


Definition application (f x : Lambda) : False :=
  matchL f False (fun h => h x).


Definition Delta : Lambda :=
  lambda (fun x : Lambda => application x x).


Definition loop : False := application Delta Delta.


Theorem two_is_three : 2 = 3.
  elim loop.
Qed.
End Paradox.


Require Import ZArith.
Inductive itree : Set :=
  | ileaf : itree
  | inode : Z -> (nat -> itree) -> itree.


Definition isingle l := inode l (fun i => ileaf).


Definition t1 := inode 0 (fun n => isingle (Z_of_nat n)).


Definition t2 :=
  inode 0
    (fun n : nat =>
      inode (Z_of_nat n)
        (fun p => isingle (Z_of_nat (n*p)))).


Inductive itree_le : itree -> itree -> Prop :=
  | le_leaf : forall t, itree_le ileaf t
  | le_node : forall l l' s s',
                Zle l l' ->
                  (forall i, exists j:nat, itree_le (s i) (s' j)) ->
                    itree_le (inode l s) (inode l' s').


Inductive itree_le' : itree -> itree -> Prop :=
  | le_leaf' : forall t, itree_le' ileaf t
  | le_node' : forall l l' s s' g,
              Zle l l' ->
                (forall i, itree_le' (s i) (s' (g i))) ->
                  itree_le' (inode l s) (inode l' s').


Require Import List.
Inductive ltree (A:Set) : Set :=
  lnode : A -> list (ltree A) -> ltree A.




(* 3.4.2 Impredicative Inductive Types *)


Inductive prop : Prop :=
  prop_intro : Prop -> prop.


Lemma prop_inject: prop.
  Proof prop_intro prop.


Inductive ex_Prop (P : Prop -> Prop) : Prop :=
  exP_intro : forall X : Prop, P X -> ex_Prop P.


Inductive ex_Set (P : Set -> Prop) : Type :=
  exS_intro : forall X : Set, P X -> ex_Set P.


Inductive typ : Type :=
  typ_intro : Type -> typ.


Definition typ_inject: typ.
  split; exact typ.                         (* Proof completed. *)
(* Defined.                                    Error: Universe inconsistency. *)
Abort.


(*
Check (fun (P:Prop ->Prop)(p: ex_Prop P) =>
  match p with exP_intro X HX => X end).
*)


(* 3.4.3 Extraction Constraints *)


(* 3.4.4 Strong Case Analysis on Proofs *)


Definition comes_from_the_left_sumbool (P Q:Prop) (x:{P} + {Q}) : Prop :=
  match x with
    | left p => True
    | right q => False
  end.


(* 続く *)