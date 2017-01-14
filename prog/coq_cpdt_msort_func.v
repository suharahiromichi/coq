(*
  CPDTより：
  Some more recent Coq features provide more convenient syntax for
  defining recursive functions.  Interested readers can consult the
  Coq manual about the commands %\index{Function}%[Function] and
  %\index{Program Fixpoint}%[Program Fixpoint].
*)

(* オリジナルは、CPDTの  GeneralRec.v *)

Require Import Arith List Omega.
Require Import Cpdt.CpdtTactics Cpdt.Coinductive.
Require Import Permutation Sorted Program Recdef.

Set Implicit Arguments.
Set Asymmetric Patterns.


Section mergeSort.
  Variable A : Type.
  Variable le : A -> A -> bool.

  Fixpoint insert (x : A) (ls : list A) : list A :=
    match ls with
      | nil => x :: nil
      | h :: ls' =>
        if le x h
          then x :: ls
          else h :: insert x ls'
    end.
  
  Fixpoint merge (ls1 ls2 : list A) : list A :=
    match ls1 with
      | nil => ls2
      | h :: ls' => insert h (merge ls' ls2)
    end.

  Fixpoint split (ls : list A) : list A * list A :=
    match ls with
      | nil => (nil, nil)
      | h :: nil => (h :: nil, nil)
      | h1 :: h2 :: ls' =>
        let (ls1, ls2) := split ls' in
          (h1 :: ls1, h2 :: ls2)
    end.
  
  (* yoshihiro *)
  Lemma split_length : forall zs xs ys,
      split zs = (xs, ys) -> length zs = length xs + length ys.
  Proof.
  Admitted.
  
  (* yoshihiro *)
  Function mergesort (xs : list A) {measure length xs} : list A :=
    match xs with
    | nil => nil
    | x::nil => x::nil
    | x::y::zs =>
      match split (x::y::zs) with
      | (xs, ys) => merge (mergesort xs) (mergesort ys)
      end
    end.
  Proof.
    - intros xs x l ys zs teq0 teq xs0 ys0 teq1.
      Check (@split_length (x :: ys :: zs) xs0 ys0 teq1).
      Check (@split_length _ _ _ teq1).
      rewrite (@split_length _ _ _ teq1).
      simpl in teq1.
      generalize teq1.
      case (split zs).
      intros.
      inversion teq2.
      now crush.
    - intros xs x l ys zs teq0 teq xs0 ys0 teq1.
      rewrite (@split_length _ _ _ teq1).
      simpl in teq1.
      generalize teq1.
      case (split zs).
      intros.
      inversion teq2.
      now crush.
  Defined.
  
  (* CPDT オリジナル *)
  Definition lengthOrder (ls1 ls2 : list A) :=
    length ls1 < length ls2.
  
  Lemma split_wf1 : forall ls, 2 <= length ls
    -> lengthOrder (fst (split ls)) ls.
  Admitted.
  
  Lemma split_wf2 : forall ls, 2 <= length ls
    -> lengthOrder (snd (split ls)) ls.
  Admitted.
  
  Lemma split_wf1' : forall ls, 2 <= length ls
    -> length (fst (split ls)) < length ls.
  Proof.
    pose split_wf1 as H.
    unfold lengthOrder in H.
    crush.
  Qed.
  
  Lemma split_wf2' : forall ls, 2 <= length ls
    -> length (snd (split ls)) < length ls.
  Proof.
    pose split_wf2 as H.
    unfold lengthOrder in H.
    crush.
  Qed.
  
  (*  Hint Resolve split_wf1 split_wf2. *)
  Hint Resolve split_wf1' split_wf2'.
  
  Function mergeSort (ls : list A) {measure length ls} : list A :=
    if le_lt_dec 2 (length ls) then
      let lss := split ls in
      merge (mergeSort (fst lss)) (mergeSort (snd lss))
    else
      ls.
  Proof.
    - auto.
    - auto.
      
      (*
    - pose split_wf2 as H.
      unfold lengthOrder in H.
      crush.
    - pose split_wf1 as H.
      unfold lengthOrder in H.
      crush.
       *)
      
      (*
      rewrite (split_length' ls).
      case (le_lt_dec 2 (length ls)); intros H.
      + apply (split_len_1 ls) in H.
        crush.
      + crush.                              (* len ls < 2 で矛盾  *)
    - intros ls le2 teq2.
      rewrite (split_length' ls).
      case (le_lt_dec 2 (length ls)); intros H.
      + apply (split_len_2 ls) in H.
        crush.
      + crush.                              (* len ls < 2 で矛盾  *)
*)
  Defined.
(*
mergeSort_tcc is defined
mergeSort_terminate is defined
mergeSort_ind is defined
mergeSort_rec is defined
mergeSort_rect is defined
R_mergeSort_correct is defined
R_mergeSort_complete is defined
*)

  Check mergeSort_ind : forall P : list A -> list A -> Prop,
       (forall (ls : list A) (_x : 2 <= length ls),
        le_lt_dec 2 (length ls) = in_left ->
        let lss := split ls in
        P (fst lss) (mergeSort (fst lss)) ->
        P (snd lss) (mergeSort (snd lss)) ->
        P ls (merge (mergeSort (fst lss)) (mergeSort (snd lss)))) ->
       (forall (ls : list A) (_x : length ls < 2),
        le_lt_dec 2 (length ls) = in_right -> P ls ls) ->
       forall ls : list A, P ls (mergeSort ls)

End mergeSort.

Extraction merge.
Extraction split.
Extraction mergeSort.

(* END *)
