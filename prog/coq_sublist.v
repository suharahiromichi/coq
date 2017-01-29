Require Import List.
Require Import Omega.
Require Import Sorting.Permutation.
Require Import Sorting.Sorted.
Require Import Program.Wf.
Require Import Arith.Bool_nat.

(*
Reserved Notation "` x" (at level 99).
Notation "` x" := (proj1_sig x).
 *)

Section Swap.
  Program Definition swap {T : Type} (x : T * T) :
    {y | fst x = snd y /\ snd x = fst y} :=
    let '(x1, x2) := x in (x2, x1).
  (* Obligation なし *)
  
  Compute proj1_sig (swap (1, 2)).          (* (2, 1) *)
End Swap.

Section Sublist.
  Variable A : Type.
  Variable f : A -> bool.

  (* Sublist l' l <==> l' ⊆ l *)
  Inductive Sublist : list A -> list A -> Prop :=
  | SL_nil : Sublist nil nil
  | SL_skip x l' l : Sublist l' l -> Sublist l' (x :: l)
  | SL_cons x l' l : Sublist l' l -> Sublist (x :: l') (x :: l).
  
  Hint Constructors Sublist.
  
  (* Sublist なら長さが減る。 *)
  Lemma sublist__length (l l' : list A) :
    Sublist l' l -> length l' <= length l.
  Proof.
    intro H.
    induction H; subst; simpl in *; try auto.
    omega.
  Qed.
  
  Program Fixpoint filter (l : list A) : {l' | Sublist l' l} :=
    match l with
    | nil => nil
    | x :: l => if f x then x :: (filter l) else filter l
    end.
  (* Obligation なし *)
  
  (* filter の結果は Sublist である。 *)
  Lemma filter__sublist (l : list A) :
    Sublist (proj1_sig (filter l)) l.
  Proof.
    induction l; subst; simpl in *.
    - now auto.
    - destruct (f a); simpl; now auto.
  Qed.
  
End Sublist.

(* Arith.Bool_nat で定義されている。 *)
Check nat_eq_bool : forall x y : nat, {b : bool | if b then x = y else x <> y}.
Check nat_noteq_bool : forall x y : nat, {b : bool | if b then x <> y else x = y}.

Compute proj1_sig (filter nat
                          (fun x => (proj1_sig (nat_noteq_bool x 2)))
                          (1 :: 2 :: 3 :: nil)).
  
Extraction filter.

(* END *)
