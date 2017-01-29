Require Import List.
Require Import Omega.
Require Import Sorting.Permutation.
Require Import Sorting.Sorted.
Require Import Program.Wf.
Require Import Arith.Bool_nat.

(* http://ccvanishing.hateblo.jp/entry/2012/12/30/205251 *)
Section Marger.
  Variable A : Type.
  Variable f : A -> bool.

  Inductive merger : list A -> list A -> list A -> Prop :=
  | Merger_nil_l  : forall l : list A,
      merger l nil l
  | Merger_nil_r  : forall l : list A,
      merger l l nil
  | Merger_cons_l : forall (x : A) (l l1 l2 : list A),
      merger l l1 l2 -> merger (x :: l) (x :: l1) l2
  | Merger_cons_r : forall (x : A) (l l1 l2 : list A),
      merger l l1 l2 -> merger (x :: l) l1 (x :: l2).

  Hint Constructors merger.
  
  Lemma merger_cons_l_inv x l l1 l2 :
    merger (x :: l) (x :: l1) l2 -> merger l l1 l2.
  Proof.
    intro H.
    inversion H; subst.
    - now auto.
    - now auto.
    - inversion H.
    inversion H; subst; simpl in *; try auto.
    - auto.
  Admitted.
  
  Lemma merger_cons_r_inv x l l1 l2 :
    merger (x :: l) l1 (x :: l2) -> merger l l1 l2.
  Proof.
  Admitted.

  Lemma Forall_inv' (P : A -> Prop) (x : A) (l : list A) :
    Forall P (x :: l) -> Forall P l.
  Proof.
    intro H.
    now inversion H.
  Qed.
  
  Hint Resolve merger_cons_l_inv merger_cons_r_inv.
  
  Program Fixpoint filter (l : list A) :
    {l' | forall lf,
        merger l l' lf ->
        Forall (fun x => f x = true) l' ->
        Forall (fun x => f x = false) lf} :=
    match l with
    | nil => nil
    | x :: l => if f x then x :: (filter l) else filter l
    end.
  Obligations.
  Obligation 1.
  Proof.
    inversion H; subst; simpl in *.
    - now auto.
    - now auto.
  Defined.
  Obligation 2.
  Proof.
    apply f0.
    - eapply merger_cons_l_inv.
      now eauto.
    - now apply Forall_inv' with (x := x).
  Defined.
  Obligation 3.
  Proof.
    apply f0 with (lf := lf).
    - admit.
    - now auto.

    Restart.
    Check (f0 (x :: lf)).
    apply Forall_inv' with (x := x).
    apply f0 with (lf := x :: lf).
    - admit.
    - now auto.
  Defined.

End Marger.

(* Arith.Bool_nat で定義されている。 *)
Check nat_eq_bool : forall x y : nat, {b : bool | if b then x = y else x <> y}.
Check nat_noteq_bool : forall x y : nat, {b : bool | if b then x <> y else x = y}.

Compute proj1_sig (filter nat
                          (fun x => (proj1_sig (nat_noteq_bool x 2)))
                          (1 :: 2 :: 3 :: nil)).
  
Extraction filter.

(* END *)
