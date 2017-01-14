(**
プログラミング Coq 証明駆動開発入門(1)
http://www.iij-ii.co.jp/lab/techdoc/coqt/coqt8.html

をSSReflectに書き直した。
その上で、「Program Fixpoint」を使って定義をした。
*)

From mathcomp Require Import all_ssreflect.
Require Import Program.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Set Print All.


(* ************ *)
(* 不等号の証明 *)
(* ************ *)
(*
(* lt なら le *)
(* ltnW でよかった。 *)
Lemma lt__le n n' : n > n' -> n' <= n.
Proof.
  move=> H.
  rewrite leq_eqVlt.
  by apply/orP; right.
Qed.

Lemma b_false__not_b b : b = false -> ~ b.
Proof.
  Search _ (_ = false).
  by apply/elimF/idP.
Qed.  

(* le の否定が lt になる。 *)
Lemma not_le__lt n n' : ~ n <= n' <-> n' < n.
Proof.
  rewrite /not ltnNge /negb.
  split => H.
  - case: (n <= n') H => H.
    + exfalso.
        by apply H.
    + by [].
  - case: (n <= n') H => H H'.
    + by inversion H.
    + by inversion H'.
Qed.

(* 証明途中に出現するもの。 *)
Lemma test n n' : (n <= n') = false -> n' <= n.
Proof.
  move=> H.
  apply lt__le.
  apply not_le__lt.
  by apply b_false__not_b.
Qed.
 *)

Lemma le_false_lt n n' : (n <= n') = false -> n' < n.
Proof.
  move=> H.
  apply/ltP.
  apply PeanoNat.Nat.nle_gt.
  apply/leP.
  by apply negbT.
Qed.

(* Hint Resolve not_le__lt b_false__not_b : myleq. *)
Hint Resolve le_false_lt : myleq.

(* **** *)
(* 証明 *)
(* **** *)
Lemma perm_refl' : forall l : seq nat, perm_eq l l.
Proof.
  by [].
Qed.

Lemma perm_sym' : forall l l' : seq nat, perm_eq l l' -> perm_eq l' l.
Proof.
  move=> l l'.
  have H := @perm_eq_sym nat_eqType.
  rewrite /symmetric in H.
  by rewrite H.
Qed.

Lemma perm_trans' : forall l l' l'' : seq nat, 
    perm_eq l l' -> perm_eq l' l'' -> perm_eq l l''.
Proof.
  move=> l l' l''.
  have H := @perm_eq_trans nat_eqType.
  rewrite /transitive in H.
    by eapply H.
Qed.

Lemma perm_cons' : forall (n : nat) (l l' : seq nat), 
    perm_eq l l' -> perm_eq (n :: l) (n :: l').
Proof.
  move=> n l l'.
  have H := @perm_cons nat_eqType.
    by rewrite H.
Qed.
  
Lemma perm_iff : forall (m n : seq nat),
                   (forall l, perm_eq m l = perm_eq n l) <-> perm_eq m n.
Proof.
  move=> m n.
  split=> H.
  - by rewrite H.
  - by apply/perm_eqlP.
Qed.

Lemma perm_swap : forall (l l' : seq nat) (x a : nat),
                    perm_eq [:: x, a & l] l' = perm_eq [:: a, x & l] l'.
Proof.
  move=> l l' x a.
  apply perm_iff.
  Check cat1s.
  rewrite -[[:: x, a & l]]cat1s.
  rewrite -[[:: a & l]]cat1s.
  rewrite -[[:: a, x & l]]cat1s.
  rewrite -[[:: x & l]]cat1s.
  apply/perm_eqlP.
  by apply (perm_catCA [:: x] [:: a] l).
Qed.

Hint Resolve perm_cons' perm_refl' perm_swap perm_trans' : sort.

(* **** *)
(* 証明 *)
(* **** *)
Inductive LocallySorted (T : eqType) (R : rel T) : seq T -> Prop :=
| LSorted_nil : LocallySorted R nil
| LSorted_cons1 : forall a : T, LocallySorted R (a :: nil)
| LSorted_consn : forall (a b : T) (l : seq T),
                    LocallySorted R (b :: l) ->
                    R a b -> LocallySorted R (a :: b :: l).


Hint Constructors LocallySorted : sort.
Hint Resolve LSorted_nil LSorted_cons1 LSorted_consn : sort.

(* Permutation, seq.v *)
Check perm_eq (1::2::3::nil) (2::1::3::nil).
Eval compute in perm_eq (1::2::3::nil) (2::1::3::nil). (* true *)
Eval compute in perm_eq nil nil.                       (* true *)


(* ソート処理の定義 *)

(*
うまくいかなかった定義：
引数に事前条件を書くとうまくいかないようである。

Program Fixpoint insert' (a : nat) (l : {l : seq nat | LocallySorted leq l})
        {measure (size l)}
  : {s : seq nat | LocallySorted leq s /\ perm_eq (a :: l) s} :=
  match l with
  | nil => a :: nil
  | x :: xs => if a <= x then
                 a :: l
               else
                 x :: insert' a xs
  end.
 *)

Program Fixpoint insert n l {struct l} : 
  {l' : seq nat | perm_eq (n ::l) l' /\
                  (LocallySorted leq l -> LocallySorted leq l') /\ 
                  (head n l' = n \/ head n l' = head n l)} := 
  match l with
  | nil => n :: nil
  | n' :: l' => 
    if n <= n' then
      n :: n' :: l'
    else
      n' :: insert n l'
  end.
Obligations.

Next Obligation.
    by auto with sort.
Defined.

Next Obligation.
  case Hnn' : (n <= n').
  - by auto with sort.
  - split.
    + erewrite perm_swap.
      by apply perm_cons'.
      (* by eauto with sort. *)
    + split.
      * move=> H0.
        assert (LocallySorted leq l') as H1 by (inversion H0; auto with sort).
        assert (LocallySorted leq x)  as H2 by auto.
        elim: x i l0 o H2.
        ** by auto with sort.
        ** inversion H0; subst.
           *** move=> a l _ _ _ Ho H2; rewrite /= in Ho.
               case: Ho => Ho; subst;
                             by auto with sort myleq.
               (*
               **** apply sorted2; by [apply ltnW, not_le__lt, b_false__not_b |].
               **** apply sorted2; by [apply ltnW, not_le__lt, b_false__not_b |].
               *)
           *** move=> a l' _ _ _ Ho H2; rewrite /= in Ho.
               case: Ho => Ho; subst;
                             by auto with sort myleq.
               (*
               **** apply sorted2; by [apply ltnW, not_le__lt, b_false__not_b |].
               **** apply sorted2; by [].
               *)
      * by auto.
Defined.

Program Fixpoint isort l {struct l} :  
  {l' : seq nat | perm_eq l l' /\ LocallySorted leq l'} := 
match l with 
| nil => nil
| a::l' => insert a (isort l')
end.

Next Obligation.
  by auto with sort.
Defined.

Next Obligation.
  remember (insert a x).
  case H : s => /= {Heqs}; subst.
    by intuition; eauto with sort.
    
    Undo 1.
  intuition.
  Check @perm_trans' (a :: l') (a :: x).
  - apply (@perm_trans' (a :: l') (a :: x)).
    + by apply perm_cons'.
    + by apply H.
  - apply (@perm_trans' (a :: l') (a :: x)).
    + by apply perm_cons'.
    + by apply H.
Defined.

Print sort.

Eval compute in proj1_sig (insert 1 nil).                (* [:: 1] *)
Eval compute in proj1_sig (insert 5 [:: 1; 4; 2; 9; 3]). (* [:: 1; 4; 2; 5; 9; 3] *)
Eval compute in proj1_sig (isort [:: 2; 4; 1; 5; 3]).    (* [:: 1; 2; 3; 4; 5] *)

Extraction insert.
Extraction isort.

(* おまけ *)
Lemma sorted_ind_inv h ls : LocallySorted leq (h :: ls) -> LocallySorted leq ls.
Proof.
  move=> H.
  inversion H.
  - by auto with sort.
  - by [].
Qed.

Hint Resolve sorted_ind_inv : sort.

Program Fixpoint merge (ls1 ls2 : seq nat) :
  {l' : seq nat | perm_eq (ls1 ++ ls2) l' /\
                  (LocallySorted leq ls1 /\ LocallySorted leq ls2 ->
                   LocallySorted leq l')} :=
  match ls1 with
  | nil => ls2
  | h :: ls' => insert h (merge ls' ls2)
  end.
Obligations.
Next Obligation.
  split.
  - by [].
  - by case.
Defined.
Next Obligation.
  remember (insert h x) as s.
  case H : s => /= {Heqs}; subst.
  intuition;                          (* ゴールの /\ をsplit する。 *)
    by eauto with sort.
Defined.

Print merge.

(* END *)
