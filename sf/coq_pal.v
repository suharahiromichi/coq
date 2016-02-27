(* 回文 palindromes *)
Require Export Poly_J.

(* 全てlist nat で定義している。
   Poly_J で定義された関数や定理も、ここで定義しなおしている。
 *)
Inductive pal : list nat -> Prop :=
| pal0 : pal []
| pal1 : forall (x : nat), pal [x]
| pal2 : forall (x : nat) (l : list nat),
  pal l -> pal (x :: (snoc l x)).

Fixpoint rev (l : list nat) : list nat :=   (* Poly_J で定義済み *)
  match l with
    | [] => []
    | h :: t => snoc (rev t) h
  end.

Lemma rev_snoc : forall (x : nat) (l : list nat), (* Poly_J で定義済み *)
                   rev (snoc l x) = x :: rev l.
Proof.
  intros x l.
  induction l.
  - simpl.  
    reflexivity.
  - simpl.
    rewrite IHl.
    simpl.
    reflexivity.
Qed.

Lemma snoc_rev : forall (x : nat) (l : list nat), (* Poly_J で定義済み *)
                   snoc (rev l) x = rev (x :: l).
Proof.
  intros x l.
  induction l.
  - simpl.
    reflexivity.
  - simpl.
    reflexivity.
Qed.

Require Import Omega.
Require Import Recdef.

(* pal の関数版（清楚帰納法）を定義する。 *)
Function palb (n : nat) (l : list nat) {wf lt n} : Prop :=
  match n with
    | 0 => True                             (* [] *)
    | 1 => True                             (* [x] *)
    | S (S n) =>
      match l with
        | [] => True                        (* [] *)
        | x1 :: l1 => match rev l1 with
                        | [] => True        (* [x] *)
                        | x2 :: l2 => x1 = x2 /\ palb n l2
                      end
      end
  end.
Proof.
  - intros.
    omega.
  - exact lt_wf.
Qed.

(* 補題の証明 *)
Functional Scheme rev_ind := Induction for rev Sort Prop.
Lemma rev_rev (l : list nat) : rev (rev l) = l.
Proof.
  functional induction rev l.
  - now simpl.
  - rewrite rev_snoc.
    now rewrite IHl0.
Qed.

Lemma eq_cons_hd (x1 x2 : nat) (l1 l2 : list nat) : x1 :: l1 = x2 :: l2 -> x1 = x2.
Proof.
  intros H.
  now inversion H.
Qed.

Lemma eq_cons_tl (x1 x2 : nat) (l1 l2 : list nat) : x1 :: l1 = x2 :: l2 -> l1 = l2.
Proof.
  intros H.
  now inversion H.
Qed.

Lemma eq_rev__eq_rev (l1 l2 : list nat) : rev l1 = l2 -> l1 = rev l2.
Proof.
  intros H.
  rewrite <- H.
  now rewrite rev_rev.
Qed.

(* 最後のひとつの要素以外を取り出す。 fujさん *)
Fixpoint liat (l : list nat) :=
match l with
  | [] => []
  | h :: t =>
    match t with
      | [] => []
      | _ :: _ => h :: (liat t)
    end
end.

(* liat と snoc の関係。 fuj さん *)
Theorem liat_snoc : forall (l : list nat) x, liat (snoc l x) = l.
Proof.
  intros l x.
  induction l.
  - reflexivity.
  - simpl.
    rewrite IHl.
    destruct l.
    + reflexivity.
    + reflexivity.
Qed.

Lemma eq_snoc (x1 x2 : nat) (l1 l2 : list nat) :
  snoc l1 x1 = snoc l2 x2 -> l1 = l2.
Proof.
  intros H.
  Check f_equal liat.
  apply (f_equal liat) in H.
  rewrite liat_snoc in H.
  rewrite liat_snoc in H.
  now apply H.
Qed.

Lemma eq_rev_x_rev_l__snoc_l_x (x : nat) (l : list nat) :
  rev (x :: rev l) = snoc l x.
Proof.
  simpl.
  rewrite snoc_rev.
  simpl.
  now rewrite rev_rev.
Qed.

Lemma eq_rev_pal' : forall l, l = rev l -> palb (length l) l.
Proof.
  intros l H.
  functional induction palb (length l) l; try auto.
  - split.
    (* l を [x1] ++ l2 ++ [x2] に分解できた。 *)
    + simpl in H.
      (* x1 = x2 *)
      rewrite e1 in H.
      simpl in H.
      apply eq_cons_hd in H.
      now apply H.
    + apply IHP.
      (* l2 = rev l2 *)
      apply eq_rev__eq_rev in e1.
      rewrite e1 in H.
      rewrite eq_rev_x_rev_l__snoc_l_x in H.
      simpl in H.
      apply eq_cons_tl in H.
      apply eq_snoc in H.
      now rewrite H.
Qed.

Lemma pal_pal : forall l, palb (length l) l -> pal l.
Proof.
  admit.                                    (* XXXXX *)
Admitted.

Lemma eq_rev_pal : forall l, l = rev l -> pal l.
Proof.
  admit.                                    (* XXXXX *)
Admitted.
  
(* END *)
