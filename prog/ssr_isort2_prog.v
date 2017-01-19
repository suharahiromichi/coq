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
Inductive Permutation (T : eqType) : seq T -> seq T -> Prop :=
| perm_nil : Permutation nil nil
| perm_skip : forall (x : T) (l l' : seq T),
    Permutation l l' -> Permutation (x :: l) (x :: l')
| perm_swap : forall (x y : T) (l : seq T), Permutation [:: y, x & l] [:: x, y & l]
| perm_trans : forall l l' l'' : seq T,
    Permutation l l' -> Permutation l' l'' -> Permutation l l''.

Hint Resolve perm_nil perm_skip perm_swap perm_trans : perm.

Lemma perm_refl : forall (T : eqType) (l : seq T), Permutation l l.
Proof.
  move=> T l.
  elim: l; by auto with perm.
Qed.

Lemma perm_cons : forall (T : eqType) (n : T) (l l' : seq T), 
    Permutation l l' -> Permutation (n :: l) (n :: l').
Proof.
  move=> T n l l' H.
  now inversion H; auto with perm.
Qed.

Hint Resolve perm_refl perm_cons : perm.

Lemma perm_iff : forall (T : eqType) (m n : seq T),
    (forall l, Permutation m l = Permutation n l) <-> Permutation m n.
Proof.
  move=> T m n.
  split=> H.
  - rewrite H; by auto with perm.
  - inversion H; subst.
    + by auto with perm.
    + 
admit.
Admitted.
(* Permutation をつかって rewrite したい。 *)

Lemma perm_cat_swap : forall (T : eqType) (s1 s2 s3 : seq T),
    Permutation (s1 ++ s2 ++ s3) (s2 ++ s1 ++ s3).
Proof.
Admitted.

Lemma perm_cons_swap : forall (T : eqType) (l l' : seq T) (x a : T),
      Permutation [:: x, a & l] l' = Permutation [:: a, x & l] l'.
Proof.
  move=> T l l' x a.
  apply perm_iff.
  rewrite -[[:: x, a & l]]cat1s.
  rewrite -[[:: a & l]]cat1s.
  rewrite -[[:: a, x & l]]cat1s.
  rewrite -[[:: x & l]]cat1s.
  by apply perm_cat_swap.
Qed.

(* **** *)
(* 証明 *)
(* **** *)
Inductive LocallySorted (T : eqType) (R : rel T) : seq T -> Prop :=
| LSorted_nil : LocallySorted R nil
| LSorted_cons1 : forall a : T, LocallySorted R (a :: nil)
| LSorted_consn : forall (a b : T) (l : seq T),
                    LocallySorted R (b :: l) ->
                    R a b -> LocallySorted R (a :: b :: l).


Hint Resolve LSorted_nil LSorted_cons1 LSorted_consn : sort.

(* ソート処理の定義 *)

Program Fixpoint insert n l {struct l} : 
  {l' : seq nat | Permutation (n :: l) l' /\
                  (LocallySorted leq l -> LocallySorted leq l') /\ 
                  (head n l' = n \/ head n l' = head n l)} := 
  match l with
  | [::] => n :: nil
  | n' :: l' => 
    if n <= n' then
      [:: n, n' &  l']
    else
      n' :: insert n l'
  end.
Obligations.
Next Obligation.
    by auto with perm sort.
Defined.
Next Obligation.
  case Hnn' : (n <= n').
  - split; by auto with perm sort.
  - split.
    + rewrite perm_cons_swap.
      by auto with perm.
    + split.
      * move=> H0.
        have H1 : LocallySorted leq l' by inversion H0; auto with sort.
        have H2 : LocallySorted leq x by auto.
        elim: x p l0 o H2.
        ** by auto with sort.
        ** inversion H0; subst.
           *** move=> a l' _ _ _ Ho H2; rewrite /= in Ho.
               case: Ho => Ho; subst;
                             by auto with sort myleq.
           *** move=> a l' _ _ _ Ho H2; rewrite /= in Ho.
               case: Ho => Ho; subst;
                             by auto with sort myleq.
      * by auto.
Defined.

Program Fixpoint isort l {struct l} :  
  {l' : seq nat | Permutation l l' /\ LocallySorted leq l'} := 
  match l with 
  | nil => nil
  | a::l' => insert a (isort l')
  end.
Next Obligation.
  by auto with sort perm.
Defined.
Next Obligation.
  remember (insert a x).
  case H : s => /= {Heqs}; subst.
    by intuition; eauto with perm.
Defined.

Eval compute in proj1_sig (insert 1 nil).                (* [:: 1] *)
Eval compute in proj1_sig (insert 5 [:: 1; 4; 2; 9; 3]). (* [:: 1; 4; 2; 5; 9; 3] *)
Eval compute in proj1_sig (isort [:: 2; 4; 1; 5; 3]).    (* [:: 1; 2; 3; 4; 5] *)

Extraction insert.
Extraction isort.

(* END *)
