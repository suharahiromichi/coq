Require Import Omega.
Require Import List.
Require Import Arith.
Require Import Sorting.Permutation.
Require Import Sorting.Sorted.

(* 不等号 *)
(* n m : n < m -> (n <= m) *)
Hint Resolve lt_le_weak : lt_le.

(* PERM *)
Check Permutation : forall (A : Type), list A -> list A -> Prop.
Check perm_nil : forall (A : Type),  Permutation nil nil.
Check perm_skip : forall (A : Type) (x : A) (l l' : list A),
    Permutation l l' -> Permutation (x :: l) (x :: l').
Check perm_swap : forall (A : Type) (x y : A) (l : list A),
    Permutation (y :: x :: l) (x :: y :: l).
Check perm_trans : forall (A : Type) (l l' l'' : list A),
    Permutation l l' -> Permutation l' l'' -> Permutation l l''.

(*
Permutatuin の左から右へrewriteできる。
see. Instance Permutation_Equivalence A, in Sorting.Permutation.v

Goal forall (l l' l'' : list nat), Permutation l' l'' -> Permutation l l'.
Proof.
  intros.
  rewrite H.
Admitted.
 *)

(*
(* Permutation_cons とおなじ。 *)
Lemma perm_cons : forall (n : nat) (l l' : list nat), 
    Permutation l l' -> Permutation (n :: l) (n :: l').
Proof.
  intros n l l' H.
  inversion H; try auto.
  now apply perm_skip, perm_swap.
Qed.
 *)

Hint Resolve perm_nil perm_skip perm_swap perm_trans Permutation_cons : perm.


(* SORT *)
Check LocallySorted : forall A : Type, (A -> A -> Prop) -> list A -> Prop.
Check LSorted_nil : forall (A : Type) (R : A -> A -> Prop), LocallySorted R nil.
Check LSorted_cons1 : forall (A : Type) (R : A -> A -> Prop) (a : A),
    LocallySorted R (a :: nil).
Check LSorted_consn : forall (A : Type) (R : A -> A -> Prop) (a b : A) (l : list A),
    LocallySorted R (b :: l) -> R a b -> LocallySorted R (a :: b :: l).

Hint Resolve LSorted_nil LSorted_cons1 LSorted_consn : sort.

(* **** *)
(* 証明 *)
(* **** *)

Lemma perm__sorted a x x0 l' :
  a > x ->
  (hd a x0 = a \/ hd a x0 = hd a l') ->
  Permutation (a :: l') x0 ->
  (LocallySorted le l' -> LocallySorted le x0) ->
  LocallySorted le (x :: l') ->
  LocallySorted le (x :: x0).
Proof.
  intros H o l0 p Hxl'.
  assert (LocallySorted le l') as H1 by (inversion Hxl'; auto with sort).
  assert (LocallySorted le x0) as H2 by auto.
  destruct x0.
  - now auto with sort.
  - inversion Hxl'; simpl in o; destruct o; subst;
      now auto with sort lt_le.             (* apply LSorted_consn. *)
(*    
  Restart.
  intros H o l0 p Hxl'.
  assert (LocallySorted le l') as H1 by (inversion Hxl'; auto with sort).
  assert (LocallySorted le x0) as H2 by auto.
  destruct x0.
  - now auto with sort.
  - inversion Hxl'; simpl in o; subst.
    + destruct o; subst.
      * apply LSorted_consn.
        ** now apply H2.
        ** now apply lt_le_weak.
      * apply LSorted_consn.
        ** now auto.
        ** now apply lt_le_weak.
    + destruct o; subst.
      * apply LSorted_consn.
        ** now apply H2.
        ** now apply lt_le_weak.
      * apply LSorted_consn.
        ** now auto.
        ** now apply H5.
*)
Qed.

Program Fixpoint insert (a : nat) (l : list nat) {struct l} : 
  {l' : list nat | Permutation (a::l) l' /\
                   (LocallySorted le l -> LocallySorted le l') /\
                   (hd a l' = a \/ hd a l' = hd a l)} := 
match l with
| nil => a :: nil
| x :: l' => 
  if le_gt_dec a x then
    a :: x :: l'
  else
    x :: (insert a l')
end.
Obligation 1.
Proof.
  now auto with sort.
Defined.
Obligation 2.
  now auto with sort.
Defined.
Obligation 3.
  split.
  - rewrite perm_swap.                      (* Permutation で rewrite する。 *)
    now auto with perm.
  - split.
    + now apply (perm__sorted a x x0 l' H o p l0).
    + now auto.
Defined.
    
Program Fixpoint isort l {struct l} :  
  {l' : list nat | Permutation l l' /\ LocallySorted le l'} := 
  match l with 
  | nil => nil
  | a :: l' => insert a (isort l')
  end.
Obligations.
Obligation 1.
Proof.
  now auto with sort perm.
Defined.
Obligation 2.
  remember (insert a x).
  destruct s; subst.
  destruct a0; subst.
  simpl.
  split.
  - eauto with perm.
  - destruct a0; now auto.
(*
    Undo 3.
    Check @perm_trans nat (a :: l') (a :: x).
    apply (@perm_trans nat (a :: l') (a :: x)).
    * now apply perm_cons.
    * now apply p0.
  - destruct a0.
    now auto.
*)
Defined.


Lemma sorted_ind_inv h ls : LocallySorted le (h :: ls) -> LocallySorted le ls.
Proof.
  intro H.
  inversion H.
  - now auto with sort.
  - now auto.
Qed.

Hint Resolve sorted_ind_inv : sort.

Program Fixpoint merge (ls1 ls2 : list nat) :
  {l' : list nat | Permutation (ls1 ++ ls2) l' /\
                  (LocallySorted le ls1 /\ LocallySorted le ls2 ->
                   LocallySorted le l')} :=
  match ls1 with
  | nil => ls2
  | h :: ls' => insert h (merge ls' ls2)
  end.
Obligations.
Next Obligation.
  split.
  - now auto.
  - intro H.
    now destruct H.
Defined.
Next Obligation.
  remember (insert h x) as s.
  destruct s as [x0 [p0 [l0 o]]].
  subst; simpl.
  intuition.                          (* ゴールの /\ をsplit する。 *)
  - now eauto with sort perm.
  - now eauto with sort.
Defined.

Lemma sorted_cons_inv h ls :
  LocallySorted le (h :: ls) -> LocallySorted le ls.
Proof.
  intro H.
  inversion H.
  subst.
  - now auto with sort.
  - now auto.
Qed.

Lemma sorted_cons_inv2 h1 h2 ls :
  LocallySorted le (h1 :: h2 :: ls) -> LocallySorted le (h1 :: ls).
Proof.
  intro H.
  inversion H.
  inversion H2.
  subst.
  + now auto with sort.
  + apply LSorted_consn.
    * now auto.
    * omega.
Qed.

Variable subseq : forall (ls' ls : list nat), Prop. (* XXX *)

Search _ Permutation.
Lemma perm__subseq ls ls' ls'' :
  Permutation ls (ls' ++ ls'') ->
  (LocallySorted le ls -> LocallySorted le ls') ->
  subseq ls' ls.
Proof.
Admitted.                                   (* XXXX *)

Lemma subseq__sorted ls ls' :               (* path.v *)
  subseq ls' ls ->
  LocallySorted le ls ->
  LocallySorted le ls'.
Proof.
Admitted.                                   (* XXXX *)

Lemma subseq__cons h ls ls' :
  subseq ls ls' -> subseq (h :: ls) (h :: ls').
Proof.
Admitted.                                   (* XXXXX *)

Lemma sorted__sorted3 h ls ls' ls'' :
  Permutation ls (ls' ++ ls'') ->
  (LocallySorted le ls -> LocallySorted le ls') ->
  LocallySorted le (h :: ls) ->
  LocallySorted le (h :: ls').
Proof.
  intros Hp Hs.
  apply subseq__sorted.
  apply subseq__cons.
  now apply (@perm__subseq ls ls' ls'').
Qed.

Hint Resolve sorted_cons_inv : sort.

Program Fixpoint splits (ls : list nat) :
  {l' : list nat * list nat |
   let (ls1, ls2) := l' in
   Permutation ls (ls1 ++ ls2) /\
   (LocallySorted le ls -> LocallySorted le ls1) /\
   (LocallySorted le ls -> LocallySorted le ls2) } :=
  match ls with
  | nil => (nil, nil)
  | h :: nil => (h :: nil, nil)
  | h1 :: h2 :: ls' =>
    let '(ls1, ls2) := splits ls' in (* let の左辺に"'"をつける。バニラCoq *)
    (h1 :: ls1, h2 :: ls2)
  end.
Obligations.
Next Obligation.
  split.
  - now auto.
  - now auto with sort.
Defined.
Next Obligation.
  intuition.
  - rewrite p.
    apply Permutation_cons.
    + reflexivity.
    + Search _ Permutation (_ :: _ ++ _) (_ ++ _ :: _).
      now apply Permutation_middle.
  - apply sorted_cons_inv2 in H.
    eapply sorted__sorted3; now eauto.
  - apply sorted_cons_inv in H.
    rewrite Permutation_app_comm in p.
    eapply sorted__sorted3; now eauto.
Defined.

(* END *)
