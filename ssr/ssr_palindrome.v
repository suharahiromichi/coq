(* https://danilafe.com/blog/coq_palindrome/ *)

From mathcomp Require Import all_ssreflect.
Set Implicit Arguments.
Unset Strict Implicit.

Section Pal.

  Variable X : Type.
  
  Inductive palindrome : seq X -> Prop :=
  | palindrome_nil : palindrome [::]
  | palindrome_x : forall (x : X), palindrome [:: x]
  | palindrome_xs : forall (x : X) (l : seq X),
      palindrome l -> palindrome (x :: l ++ [:: x]).
  Hint Constructors palindrome.
  
  Theorem pal_rev (l : seq X) : palindrome l -> l = rev l.
  Proof.
    elim=> //= x l' H IHpalindrome.
    rewrite -cat_cons -cat1s !rev_cat.
      by rewrite -IHpalindrome.
  Qed.
  
  Inductive seq_alt : seq X -> Prop :=
  | seq_alt_base : seq_alt [::]
  | seq_alt_x : forall (x : X), seq_alt [:: x]
  | seq_alt_xy : forall (x y : X)
                        (l : seq X), seq_alt l -> seq_alt (x :: l ++ [:: y]).
  Hint Constructors seq_alt.
  
  Lemma seq_alt_cons (x : X) (l : seq X) : seq_alt l -> seq_alt (x::l).
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

  Lemma seq_alt_correct : forall (l : seq X), seq_alt l.
  Proof.
    induction l.
    - apply seq_alt_base.
    - apply seq_alt_cons. apply IHl.
  Qed.
  
  Lemma alt_induction (P : seq X -> Prop) :
    P [::] ->
    (forall (x : X), P [:: x]) ->
    (forall (l : seq X), P l -> forall (x y : X), P (x :: l ++ [:: y])) ->
    forall (ln : seq X), P ln.
  Proof.
    move=> Hb1 Hb2 Hss ln.
    elim: (seq_alt_correct ln) => //= x y l IHl H.
      by apply: Hss.
  Qed.
  
  Lemma rev_one (x : X) : rev [:: x] = [:: x].
  Proof.
    done.
  Qed.
  
(*
  Lemma app_injective (l1 l2 s : seq X) : l1 ++ s = l2 ++ s -> l1 = l2.
  Proof.
  Admitted.                                 (*  *)
  (* これは証明できなかったので *)
  Theorem rev_pal' (l : seq X) : l = rev l -> palindrome l.
  Proof.
    elim/alt_induction : l => //= l IH x y H.
    rewrite -cat_cons rev_cat /= in H.
    inversion H.                 (* injection H as H1 *)
    (* H1 : x = y *)
    (* H2 : l ++ [:: y] = rev (y :: l) *)
    rewrite -H1 -[x :: l]cat1s rev_cat rev_one in H2.
    rewrite -H1.
    apply: palindrome_xs.
    apply: IH.
    move/(@app_injective l (rev l) [:: x]) in H2. (* XXX *)
    done.
  Abort.
*)  
  
  (* revK (= rev_injective) の特別なかたちとして、次を用意した。 *)
  Lemma rev_injective' (l1 l2 : seq X) : l1 = rev l2 -> rev l1 = l2.
  Proof.
    move=> H.
    rewrite -(revK l2).
      by rewrite -H.
  Qed.
  
  Theorem rev_pal' (l : seq X) : l = rev l -> palindrome l.
  Proof.
    elim/alt_induction : l => //= l IH x y H.
    rewrite -cat_cons rev_cat /= in H.
    (* H : x :: l ++ [:: y] = y :: rev (x :: l) *)
    inversion H.
    (* H1 : x = y *)
    (* H2 : l ++ [:: y] = rev (y :: l) *)
    
    rewrite -H1.
    
    rewrite -H1 -[x :: l]cat1s in H2.
    move/rev_injective' in H2.
    rewrite cat1s rev_cat rev_one cat_cons in H2.
    (* H2 : x :: [::] ++ rev l = x :: l *)
    inversion H2.
    (* H3 : revl = l *)
    
    apply: palindrome_xs.
    rewrite H3.
      by apply: IH.
  Qed.
  
End Pal.

(* END *)
