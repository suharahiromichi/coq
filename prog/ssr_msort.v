From mathcomp Require Import all_ssreflect.
Require Import Program.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Set Print All.

(* **** *)
(* perm *) (* seq.v *)
(* **** *)

Variable T : eqType.

Check perm_eq : seq T -> seq T -> bool.
Search _ perm_eq.
Compute perm_eq [:: 1; 2] [:: 1; 2].        (* true *)

Check perm_eq_refl : forall (T : eqType) (s : seq T), perm_eq s s.
Check perm_eq_sym : forall T : eqType, symmetric perm_eq.
Check perm_eq_trans : forall T : eqType, transitive perm_eq.
Check perm_cons : forall (T : eqType) (x : T) (s1 s2 : seq T),
    perm_eq (x :: s1) (x :: s2) = perm_eq s1 s2.

Lemma perm_cons' : forall (n : T) (l l' : seq T), 
    perm_eq l l' -> perm_eq (n :: l) (n :: l').
Proof.
  move=> n l l' H.
  by rewrite perm_cons.
Qed.

(*
Lemma perm_cons'2 :  forall (T : eqType) (n1 n2 : T) (s1 s2 : seq T),
    perm_eq [:: n1, n2 & s1] [:: n2, n1 & s2] = perm_eq (n1 :: s1) (n1 :: s2).
Proof.
Admitted.
 *)

Lemma perm_iff : forall (m n : seq T),
                   (forall l, perm_eq m l = perm_eq n l) <-> perm_eq m n.
Proof.
  move=> m n.
  split=> H.
  - by rewrite H.
  - by apply/perm_eqlP.
Qed.

Lemma perm_swap : forall (l l' : seq T) (x a : T),
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

Lemma perm_swap_cat : forall (l l' l'' : seq T),
    perm_eq (l ++ l') l'' = perm_eq (l' ++ l) l''.
Proof.
  move=> l l' l''.
  apply perm_iff.
  by rewrite perm_catC.
Qed.

(* :: と ++ は左結合で、同じ優先順位である。 *)
Lemma perm_swap_cons_cat : forall (x : T) (l l' l'' : seq T),
    perm_eq (x :: l ++ l') l'' = perm_eq (l ++ x :: l') l''.
Proof.
  move=> x l l' l''.
  apply perm_iff.
  rewrite -[x :: l ++ l']cat1s.
  rewrite -[x :: l']cat1s.
  by rewrite -perm_catCA.
Qed.

Hint Resolve perm_cons perm_eq_refl perm_eq_sym perm_eq_trans : perm.
Hint Rewrite perm_iff perm_swap perm_swap_cat : perm.

(* **** *)
(* sort *) (* path.v *)
(* **** *)

Variable leT : rel T.
Hypothesis leT_tr : transitive leT.
Hypothesis leT_false : forall x y, leT x y = false -> leT y x. (* ???? *)

Check sorted leT : seq T -> bool.
Search _ sorted.

Lemma sorted_nil : sorted leT [::].
Proof.
    by [].
Qed.

Lemma sorted_cons1 n : sorted leT [:: n].
Proof.
    by [].
Qed.

Lemma sorted_consn m n l :
  sorted leT (n :: l) -> leT m n -> sorted leT [:: m, n & l].
Proof.
  move=> /= H R.
    by apply/andP.                            (* path の定義のまま。 *)
Qed.

Hint Resolve sorted_nil sorted_cons1 sorted_consn : sort.

Lemma sorted_cons_inv h l : sorted leT (h :: l) -> sorted leT l.
Proof.
  apply: subseq_sorted.
  - by apply: leT_tr.
  - by apply: subseq_cons.
Qed.

Lemma sorted_inv m n l :
  sorted leT [:: m, n & l] -> (leT m n /\ sorted leT (n :: l)).
Proof.
  by move/andP.                             (* path の定義のまま。 *)
Qed.

Lemma cat__sorted l l' :
  sorted leT (l ++ l') -> (sorted leT l /\ sorted leT l').
Proof.
  elim: l.
  - by [].
  - move=> a l IHl H.
Admitted.                                   (* XXXX *)
  
(*
Lemma sorted_cons_inv2 m n l :
  sorted leT [:: m, n & l] -> sorted leT (m :: l).
Proof.
  apply: subseq_sorted.
  - by apply: leT_tr.
  - rewrite -[(m :: l)]cat1s.
    rewrite -[[:: m, _ & _]]cat1s.
    apply: cat_subseq.
    + by apply: subseq_refl.
    + by apply: subseq_cons.
Qed.

Lemma subseq_cons2 (n : T) (l l' : seq T) :
  subseq l l' -> subseq (n :: l) (n :: l').
Proof.
  rewrite -[(n :: l)]cat1s.
  rewrite -[(n :: l')]cat1s.
  by apply: cat_subseq.
Qed.

Lemma perm__subseq l l' :
  (exists l'', perm_eq (l' ++ l'') l) ->
  (sorted leT l -> sorted leT l') -> subseq l' l.
Proof.
Admitted.

Lemma perm__sorted n l l' :
  (exists l'', perm_eq (l' ++ l'') l) ->    (* perm__subseq *)
  (sorted leT l -> sorted leT l') ->        (* perm__subseq *)
  sorted leT (n :: l) -> sorted leT (n :: l').
Proof.
  move=> He Hs H.
  Check (@subseq_sorted T leT leT_tr (n :: l') (n :: l)).
  apply (@subseq_sorted T leT leT_tr (n :: l') (n :: l)).
  - apply subseq_cons2.
    apply perm__subseq; by [].
  - by [].
Admitted.

Lemma perm_app : forall (n : nat) (l'' l l' : seq nat),
    perm_eq l'' (l ++ l') -> perm_eq (n :: l'') (l ++ n :: l').
Admitted.
 *)

Lemma sorted__sorted' (x : T) (l : seq T) :
  (forall y, y \in l -> leT x y) -> sorted leT l -> sorted leT (x :: l).
Proof.
  move=> Hxy.
  Check @path_min_sorted T leT x l.
  rewrite -(@path_min_sorted T leT x l).
  - by [].
  - (* Goal : {in l, forall y0 : T, leT x y0}, ssrbool.v l.222, l.1571 *)
    (*             {in A, P1} <-> forall x, x \in A -> Qx.             *)
    move=> y Hyl.
      by apply: (Hxy y).
Qed.
(* 別証明 *)
(* (forall y0 : T, y0 \in x' -> leT x y0) <-> {in x', forall y : T, leT x y} *)
(* であることにも。 *)
Lemma sorted__sorted (x : T) (l : seq T) :
  {in l, forall y : T, leT x y} -> sorted leT l -> sorted leT (x :: l).
Proof.
  move=> H Hs.
  rewrite /sorted.
  by rewrite path_min_sorted.
Qed.

Lemma sorted__in (n n' : T) (l l' : seq T) :
  perm_eq (n :: l') l ->
  (sorted leT l' -> sorted leT l) ->
(*  head n l = n \/ head n l = head n l' *)
  leT n' n -> path leT n' l' ->
  {in l, forall y : T, leT n' y}.
Proof.
Admitted.                                   (* XXX *)

Check path_min_sorted : forall (T : eqType) (leT : rel T) (x : T) (s : seq_predType T),
    {in s, forall y : T, leT x y} -> path leT x s = sorted leT s.

Program Fixpoint merge (ls1 ls2 : seq T)
  {measure (size ls1 + size ls2)} :
  {l' : seq T | perm_eq (ls1 ++ ls2) l' /\
                (sorted leT ls1 -> sorted leT ls2 -> sorted leT l')} :=
  (* match (ls1, ls2) とすると、ペアどうしの代入の前提が解けない。 *)
  (* 「'」をつけてもだめのよう。 *)
  match ls1 with
  | [::] => ls2
  | x :: ls1' => match ls2 with
                 | [::] => ls1
                 | y :: ls2' => if (leT x y) then
                                  x :: (merge ls1' ls2)
                                else
                                  y :: (merge ls1 ls2')
                 end
  end.
Obligations.
Next Obligation.
  split.
  - by rewrite [ls1' ++ []%list]List.app_nil_r.
  - by [].
Defined.
Next Obligation.
  apply PeanoNat.Nat.add_le_lt_mono.
  - by [].
  - by [].
Defined.
Next Obligation.
  split.
  - remember (merge ls1' (y :: ls2') _).
    case Hx : s => /= [x' [Hxp Hxs]].
    remember (merge (x :: ls1') ls2' _).
    case Hy : s0 => /= [y' [Hyp Hys]].
    case H : (leT x y); subst.
    + by rewrite perm_cons.
    + rewrite -cat_cons.
      rewrite perm_swap_cat.
      rewrite cat_cons.
      rewrite perm_cons.
        by rewrite perm_swap_cat.
  - remember (merge ls1' (y :: ls2') _).
    case Hx : s => /= [x' [Hxp Hxs]].
    (* x' は ls1 ++ ls2 = x::ls1' ++ y::ls2' から x を抜いたもの。 *)
    
    remember (merge (x :: ls1') ls2' _).
    case Hy : s0 => /= [y' [Hyp Hys]].
    (* y' は ls1 ++ ls2 = x::ls1' ++ y::ls2' から y を抜いたもの。 *)

    case H : (leT x y); subst.
    + move=> H1 H2.
      apply sorted__sorted.
      * Check (@sorted__in y x x' (ls1' ++ ls2')).
        apply (@sorted__in y x x' (ls1' ++ ls2')).
        ** by rewrite perm_swap_cons_cat.
        ** move=> H'.
           apply cat__sorted in H'.
           case: H' => H'1 H'2.
           by apply Hxs.
        ** by [].
        ** admit.                           (* XXXX *)
      * apply Hxs.
        eapply path_sorted.
        apply H1.
        by apply H2.
    + move=> H1 H2.
      apply sorted__sorted.
      * Check (@sorted__in x y y' (ls1' ++ ls2')).
        apply (@sorted__in x y y' (ls1' ++ ls2')).
        ** by [].
        ** move=> H'.
           apply cat__sorted in H'.
           case: H' => H'1 H'2.
           by apply Hys.
        ** by apply leT_false.              (* ???? *)
        ** admit.                           (* XXXX *)
      * apply Hys.
        apply H1.
        eapply path_sorted.
        by apply H2.
Defined.

(* ******************* *)
(* insert を使う merge *)
(* ******************* *)
Program Fixpoint insert n l {struct l} : 
  {l' : seq T | perm_eq (n :: l) l' /\
                (sorted leT l -> sorted leT l') /\ 
                (head n l' = n \/ head n l' = head n l)} := 
  match l with
  | [::] => [:: n]
  | n' :: l' => 
    if leT n n' then
      n :: n' :: l'
    else
      n' :: insert n l'
  end.
Obligations.
Next Obligation.
  case Hnn' : (leT n n').
  - by auto with sort.
  - split.
    + erewrite perm_swap.
      by rewrite perm_cons.
    + split.
      * move=> H.
        apply sorted__sorted.
(*
        have H1 : sorted leT l' by apply: (@sorted_cons_inv n' l'). l', x : seq T
        have H2 : sorted leT x by auto.
*)
        ** apply (@sorted__in n n' x l').
           *** by apply i.
           *** by apply i0.
           *** by apply leT_false.          (* ????? *)
           *** by apply H.
        ** apply i0.
           eapply path_sorted.
             by apply H.
      * by auto.
Defined.

Hint Resolve sorted_cons_inv : sort.
Hint Resolve perm_cons' : perm.

Program Fixpoint merge' (ls1 ls2 : seq T) :
  {l' : seq T | perm_eq (ls1 ++ ls2) l' /\
                (sorted leT ls1 /\ sorted leT ls2 -> sorted leT l')} :=
  match ls1 with
  | nil => ls2
  | h :: ls' => insert h (merge' ls' ls2)
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
  intuition.                          (* ゴールの /\ をsplit する。 *)
  - Check @perm_eq_trans T (h :: x) (h :: ls' ++ ls2) _.
    eapply (@perm_eq_trans T (h :: x) (h :: ls' ++ ls2) _). (* _ は _x_ *)
    + by rewrite perm_cons.
    + by [].
  - apply H1, H2.
    + by apply path_sorted with (x := h).
    + by [].
  - eapply (@perm_eq_trans T (h :: x) (h :: ls' ++ ls2) _). (* _ は _x_ *)
    + by rewrite perm_cons.
    + by [].
  - apply H1, H2.
    + by apply path_sorted with (x := h).
    + by [].
Defined.

(* 証明のないinsertを呼ぶと、ゴールにinsertが残り、証明できない。 *)

(* END *)
