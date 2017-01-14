From mathcomp Require Import all_ssreflect.
Require Import Program.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Set Print All.


(* ************ *)
(* 不等号の証明 *)
(* ************ *)

Lemma b_false__not_b b : b = false -> ~ b.
Proof.
  Search _ (_ = false).
  move/negbT => H.
    by apply/idP.
    
  Restart.
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

(* auto で ltnW は見つかるので、それ以外のをまとめる *)
Lemma test' n n' : (n <= n') = false -> n' < n.
Proof.
  move=> H.
  apply not_le__lt.
  by apply b_false__not_b.
Qed.

(* Hint Resolve not_le__lt b_false__not_b : myleq. *)
Hint Resolve test' : myleq.


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

Lemma perm_swap2 : forall (l l' l'' : seq T),
                    perm_eq (l ++ l') l'' = perm_eq (l' ++ l) l''.
Proof.
  move=> l l' l''.
  apply perm_iff.
  Print perm_eql.
  Search _ perm_eq.
Admitted.                                   (* XXXX *)

Hint Resolve perm_cons perm_eq_refl perm_eq_sym perm_eq_trans perm_iff perm_swap : perm.

(* **** *)
(* sort *) (* path.v *)
(* **** *)

Variable leT : rel T.
Hypothesis leT_tr : transitive leT.

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

Check perm_to_subseq : forall (T : eqType) (s1 s2 : seq T),
       subseq s1 s2 -> {s3 : seq T | perm_eq s2 (s1 ++ s3)}.
(*
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

Hint Resolve sorted_nil sorted_cons1 sorted_consn sorted_cons_inv sorted_inv : sort.

Lemma TEST (x y : T) (x' : seq T) :
  leT x y -> y \in x' -> sorted leT x' -> sorted leT (x :: x').
Proof.
Admitted.

Lemma TEST1 (y : T) (x' l : seq T) :
  perm_eq (y :: l) x' -> y \in x'.
Proof.
  Admitted.

Lemma path_path_sorted_1 (x y : T) (ls1' ls2' x' : seq T) :
  leT x y ->
  perm_eq (ls1' ++ y :: ls2') x' ->
  sorted leT x' ->
  (* path leT x ls1' -> path leT y ls2' -> *)
  sorted leT (x :: x').
Proof.
  (* x' = merge ls1' (y :: ls2') *)
  move => Hxy Hp H1. (* H2 H3. *)
  apply (@TEST x y x').
  - by [].
  - rewrite perm_swap2 in Hp.
    Check cat_cons.
    rewrite cat_cons in Hp.
    by apply (@TEST1 y x' (ls2' ++ ls1')).
  - by [].
Qed.

Lemma path_path_sorted_2 (x y : T) (ls1' ls2' y' : seq T) :
  leT x y = false ->
  perm_eq (x :: ls1' ++ ls2') y' ->
  sorted leT y' ->
  (* path leT x ls1' -> path leT y ls2' -> *)
  sorted leT (y :: y').
Proof.
Admitted.

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
      rewrite perm_swap2.
      rewrite cat_cons.
      rewrite perm_cons.
        by rewrite perm_swap2.
  - remember (merge ls1' (y :: ls2') _).
    case Hx : s => /= [x' [Hxp Hxs]].
    (* x' は ls1 ++ ls2 = x::ls1' ++ y::ls2' から x を抜いたもの。 *)
    
    remember (merge (x :: ls1') ls2' _).
    case Hy : s0 => /= [y' [Hyp Hys]].
    (* y' は ls1 ++ ls2 = x::ls1' ++ y::ls2' から y を抜いたもの。 *)
    
    case H : (leT x y); subst.
    + move=> H1 H2.
      apply (@path_path_sorted_1 x y ls1' ls2' x').
      * by [].
      * by [].
      * apply Hxs.
        Check (@path_sorted T leT x ls1').
        ** by apply (@path_sorted T leT x ls1').
        ** by [].
(*      * by [].
      * by []. *)
    + move=> H1 H2.
      apply (@path_path_sorted_2 x y ls1' ls2' y').
      * by [].
      * by [].
      * apply Hys.
        ** by [].
        Check @path_sorted T leT y ls2'.
        ** by apply (@path_sorted T leT y ls2').
(*      * by [].
      * by []. *)
Defined.

(* Permutation, seq.v *)
Check perm_eq (1::2::3::nil) (2::1::3::nil).
Eval compute in perm_eq (1::2::3::nil) (2::1::3::nil). (* true *)
Eval compute in perm_eq nil nil.                       (* true *)


(* ソート処理の定義 *)

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
           *** move=> a l' _ _ _ Ho H2; rewrite /= in Ho.
               case: Ho => Ho; subst;
                             by auto with sort myleq.
      * by auto.
Defined.

(* ************** *)
(* insertion sort *)
(* ************** *)
Fixpoint isort l {struct l} :  
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

Print isort.

Eval compute in proj1_sig (insert 1 nil).                (* [:: 1] *)
Eval compute in proj1_sig (insert 5 [:: 1; 4; 2; 9; 3]). (* [:: 1; 4; 2; 5; 9; 3] *)
Eval compute in proj1_sig (isort [:: 2; 4; 1; 5; 3]).    (* [:: 1; 2; 3; 4; 5] *)

Extraction insert.
Extraction isort.

(* ********** *)
(* merge sort *)
(* ********** *)
Lemma sorted_inv h ls : LocallySorted leq (h :: ls) -> LocallySorted leq ls.
Proof.
  move=> H.
  inversion H.
  - by auto with sort.
  - by [].
Qed.

Lemma sorted_inv2 : forall a b l, LocallySorted leq [:: a, b & l] -> a <= b.
Proof.
  move=> a b l H.
  by inversion H; subst.
Qed.

Lemma sorted_inv3 : forall a b l, LocallySorted leq [:: a, b & l] ->
                                  (a <= b /\ LocallySorted leq (b :: l)).
Proof.
  move=> a b l H.
  split.
  - by inversion H; subst.
  - inversion H; subst.
    inversion H2; subst.
    + by apply LSorted_cons1.
    + by [].
Qed.

Lemma sorted__sorted2 h1 h2 ls :
  LocallySorted leq [:: h1, h2 & ls] -> LocallySorted leq (h1 :: ls).
Proof.
  elim: ls => [H | h3 ls' IHls H].
  - by apply LSorted_cons1.
  - elim: ls' IHls H => [H H' | h4 ls'' IHls' H H'].
    + apply sorted_inv3 in H'.
      case: H' => [H1 H2].
      apply sorted_inv3 in H2.
      case: H2 => [H2 H3].
      have H13 : h1 <= h3 by apply (leq_trans H1 H2).
      apply (@LSorted_consn _ leq h1 h3 [::]).
      * by [].
      * by [].
    + apply sorted_inv3 in H'.
      case: H' => [H1 H2].
      apply sorted_inv3 in H2.
      case: H2 => [H2 H3].
      have H13 : h1 <= h3 by apply (leq_trans H1 H2).
      apply (@LSorted_consn _ leq h1 h3 _).
      * by [].
      * by [].
Qed.

Lemma sorted__sorted3 h ls ls' ls'' :
  perm_eq ls (ls' ++ ls'') ->
  (LocallySorted leq ls -> LocallySorted leq ls') ->
  LocallySorted leq (h :: ls) ->
  LocallySorted leq (h :: ls').
Proof.
  
Admitted.

Lemma perm_app : forall (n : nat) (l'' l l' : seq nat),
    perm_eq l'' (l ++ l') -> perm_eq (n :: l'') (l ++ n :: l').
Admitted.

Hint Resolve sorted_inv sorted_inv2 sorted__sorted3 : sort.

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

Program Fixpoint splits (ls : seq nat) :
  { (ls1,ls2) : seq nat * seq nat |
    perm_eq ls (ls1 ++ ls2) /\
    (LocallySorted leq ls -> LocallySorted leq ls1) /\
    (LocallySorted leq ls -> LocallySorted leq ls2) } :=
  match ls with
  | [::] => ([::], [::])
  | [:: h] => ([:: h], [::])
  | [:: h1, h2 & ls'] =>
    let '(ls1, ls2) := splits ls' in (* let の左辺に"'"をつける。バニラCoq *)
    (h1 :: ls1, h2 :: ls2)
  end.
Obligations.
Next Obligation.
    by eauto with sort.
Defined.
Next Obligation.
  intuition.
  Search (_ :: _ ++ _).
  - apply perm_cons'.
      by apply perm_app.
  - by eauto with sort.
  - by eauto with sort.
Defined.
  
Program Fixpoint msort (ls : seq nat) {measure (size ls)} :
  {l' : seq nat | perm_eq ls l' /\ LocallySorted leq l'} :=
  if (size ls) <= 1 then
    ls
  else
    let '(ls1, ls2) := splits ls in (* let の左辺に"'"をつける。バニラCoq *)
    merge (msort ls1) (msort ls2).
Obligations.
Next Obligation.
  remember (splits ls) as s.
  case H : s => /= {Heqs}; subst.
  apply/ltP.
Admitted.

 *)

(* END *)
