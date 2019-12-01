(**
egison の map
*)

From mathcomp Require Import all_ssreflect.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section List.
  
  Variable A : Type.
  
  (* append 命題 *)
  Inductive append : seq A -> seq A -> seq A -> Prop :=
  | app_nil (b : seq A) : append [::] b b
  | app_cons (h : A) (a b c : seq A) : append a b c -> append (h :: a) b (h :: c).
  Hint Constructors append.
  
  (* 命題と関数の同値の証明 *)
  Lemma appapp : forall (a b c : seq A), append a b c <-> a ++ b = c.
  Proof.
    split.
    - elim=> b'' //= a' b' c' H IH.
        by rewrite IH.
    - elim: a b c => //=.
      + by move=> b c ->.
      + move=> n' a' IH b' c' <-.
        apply: app_cons.
          by apply: IH.
  Qed.
  
End List.

Section map.

  Variable A : Type.
  Variable B : Type.
  
  Inductive egimap (f : A -> B) : seq A -> seq B -> Prop :=
  | egi_map_cons (x : A) (a b c : seq A) (p q r : seq B) :
      append a (x :: b) c -> append p (f x :: q) r ->
      egimap f a p -> egimap f b q -> egimap f c r
  | egi_map_nil : egimap f [::] [::].
  Hint Constructors egimap.
  
  Goal forall (f : A -> B) (s : seq A) (t : seq B),
      egimap f s t <-> [seq f i | i <- s] = t.
  Proof.
    move=> f s t.
    split.
    - elim=> //=.
      move=> x a b c p q r H1 H2 H3 H4 H5 H6.
      move/appapp in H1.
      move/appapp in H2.
      subst.
      Check map_cat.
      Check map_cons.
      rewrite map_cat.
      rewrite map_cons.
      done.
      
    - elim: s t => //=.
      + move=> t H.
        rewrite -H.
        apply: egi_map_nil.
      + move=> x s IH t H.
        rewrite -H.
        Check @egi_map_cons f x [::] s (x :: s)
              [::] [seq f i | i <- s] (f x :: [seq f i | i <- s]).
        apply: (@egi_map_cons f x [::] s (x :: s)
                              [::] [seq f i | i <- s] (f x :: [seq f i | i <- s])).
        * by apply: app_nil.
        * by apply: app_nil.
        * by apply: egi_map_nil.
        * by apply: IH.
  Qed.
  
End map.

Check S.
Check map.
Compute map S [:: 1; 2; 3].

Goal forall (s t : seq nat), egimap S s t <-> [seq i.+1 | i <- s] = t.
Proof.
  move=> s t.
  split.
  - elim=> //=.
    move=> x a b c p q r H1 H2 H3 H4 H5 H6.
    move/appapp in H1.
    move/appapp in H2.
    subst.
    Check map_cat.
    Check map_cons.
    rewrite map_cat.
    rewrite map_cons.
    done.
    
  - elim: s t => //=.
    + move=> t H.
      rewrite -H.
      apply: egi_map_nil.
    + move=> x s IH t H.
      rewrite -H.
      Check @egi_map_cons nat nat S x [::] s (x :: s)
            [::] [seq i.+1 | i <- s] (x.+1 :: [seq i.+1 | i <- s]).
      apply: (@egi_map_cons nat nat S x [::] s (x :: s)
                            [::] [seq i.+1 | i <- s] (x.+1 :: [seq i.+1 | i <- s])).
      * by apply: app_nil.
      * by apply: app_nil.
      * by apply: egi_map_nil.
      * by apply: IH.
Qed.

(* END *)
