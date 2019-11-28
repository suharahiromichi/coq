(* https://danilafe.com/blog/coq_palindrome/ *)

From mathcomp Require Import all_ssreflect.
Set Implicit Arguments.
Unset Strict Implicit.

Section Pal.

  Inductive palindrome { X : Type } : seq X -> Prop :=
  | palindrome_nil : palindrome [::]
  | palindrome_x : forall (x : X), palindrome [:: x]
  | palindrome_xs : forall (x : X) (l : seq X),
      palindrome l -> palindrome (x :: l ++ [:: x]).
  Hint Constructors palindrome.
  
  Theorem pal_rev { X : Type } (l : seq X) : palindrome l -> l = rev l.
  Proof.
    elim=> //= x l' H IHpalindrome.
    rewrite -cat_cons -cat1s !rev_cat.
      by rewrite -IHpalindrome.
  Qed.
  
  Inductive seq_alt { X : Type } : seq X -> Prop :=
  | seq_alt_base : seq_alt [::]
  | seq_alt_x : forall (x : X), seq_alt [:: x]
  | seq_alt_xy : forall (x y : X)
                        (l : seq X), seq_alt l -> seq_alt (x :: l ++ [:: y]).
  Hint Constructors seq_alt.
  
  Lemma seq_alt_cons { X : Type } (x : X) (l : seq X) : seq_alt l -> seq_alt (x::l).
  Proof.
    elim=> //= [y |x' y l' H IHseq_alt].
    - have -> : [:: x ; y] = x :: [::] ++ [:: y] by [].
        by apply: seq_alt_xy.
    - inversion IHseq_alt; subst; clear IHseq_alt; move=> /=.
      + have -> : [:: x; x'; y] = [:: x] ++ [:: x'] ++ [:: y] by [].
          by apply: seq_alt_xy.
      + have -> :
          x' :: (l0 ++ [:: y0]) ++ [:: y] = (x' :: (l0 ++ [:: y0])) ++ [::y] by [].
        by do 2!apply: seq_alt_xy.
  Qed.

  Lemma seq_alt_correct { X : Type } : forall (l : seq X), seq_alt l.
  Proof.
    induction l.
    - apply seq_alt_base.
    - apply seq_alt_cons. apply IHl.
  Qed.
  
  Lemma alt_induction { X : Type } (P : seq X -> Prop) :
    P [::] ->
    (forall (x : X), P [:: x]) ->
    (forall (l : seq X), P l -> forall (x y : X), P (x :: l ++ [:: y])) ->
    forall (ln : seq X), P ln.
  Proof.
    move=> Hb1 Hb2 Hss ln.
    elim: (seq_alt_correct ln) => //= x y l IHl H.
      by apply: Hss.
  Qed.
  
  (* sf/Lists.v *)
  Lemma rev_injective { X : Type } (l1 l2 : seq X) : rev l1 = rev l2 -> l1 = l2.
  Proof.
  Admitted.
  
  Theorem rev_pal' { X : Type } (l : seq X) : l = rev l -> palindrome l.
  Proof.
    move=> H.
    elim/(@alt_induction X) : l H => //= l IH x y H.
    have H1 : x :: l ++ [:: y] = (x :: l) ++ [:: y] by [].
    rewrite H1 in H.
    rewrite rev_cat in H.
    injection H as Heq1.
    rewrite -Heq1.
    apply: palindrome_xs.
    apply: IH.
    rewrite -Heq1 in H.
    rewrite -[x :: l]cat1s in H.
    rewrite rev_cat in H.
    have H2 : rev [:: x] = [:: x] by [].
    rewrite H2 in H.
    symmetry in H.
    Admitted.

(*
  Theorem rev_pal' { X : Type } : forall (l : seq X), l = rev l -> palindrome l.
  Proof.
  intros l H. induction l using alt_induction.
  - (* Base case 1; empty seq is palindrome by definition. *)
    apply palindrome_nil.
  - (* Base case 2; singleton seq is palindrome by definition. *)
    apply palindrome_x.
  - (* Inductive step (and interesting case.) *)

    (* Milk the reverse property to show that we end and begin with the same thing. *)
    assert (Hi1 : x::l ++ [y] = (x::l) ++ [y]). reflexivity. rewrite Hi1 in H.
    rewrite rev_app_distr in H. simpl in H. injection H as Heq1.

    (* Do the same again; This time, we also find that rev l = l. *)
    apply rev_injective in H. repeat (rewrite rev_app_distr in H). simpl in H. injection H as Heq2.

    (* Use the induction hypothesis to deduce that l is a palindrome. *)
    rewrite rev_involutive in H. symmetry in H. apply IHl in H.

    (* We know we start and end with the same thing; Use the third way to construct a palindrome.
       Since l is a palindrome, we are done. *)
    rewrite Heq1. apply palindrome_xs. apply H.
Qed.
 *)

End Pal.

(* END *)