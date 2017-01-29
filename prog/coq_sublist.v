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
  | SL_nil l : Sublist nil l
  | SL_skip x l' l : Sublist l' l -> Sublist l' (x :: l)
  | SL_cons x l' l : Sublist l' l -> Sublist (x :: l') (x :: l).
  
  Hint Constructors Sublist.
  
  (* Sublist なら長さが減る。 *)
  Lemma sublist__length (l l' : list A) :
    Sublist l' l -> length l' <= length l.
  Proof.
    intro H.
    induction H; subst; simpl in *; try auto; omega.
  Qed.
  
  (* *** *)
  Lemma sublist_ref (l : list A) :
    Sublist l l.
  Proof.
    induction l as [|x l' IHl]; now auto.
  Qed.
  
  Lemma sublist_trans (l l' l'' : list A) :
    Sublist l'' l' -> Sublist l' l -> Sublist l'' l.
  Proof.
  Admitted.                               (* mathcomp seq.v *)
  

  Program Fixpoint filter (l : list A) :
    {l' | Sublist l' l /\ Forall (fun x => f x = true) l'} :=
    (* さらに、l' が最大の長さのものであることを示す必要がある。 *)
    match l with
    | nil => nil
    | x :: l => if f x then x :: (filter l) else filter l
    end.
  Obligation 2.
  Proof.
    split.
    - now auto.
    - apply Forall_cons.
      + admit.                              (*  f x = true *)
      + now auto.
  Defined.
  
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
