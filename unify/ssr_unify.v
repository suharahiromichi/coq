From mathcomp Require Import all_ssreflect.

Module Types.

  Reserved Notation "x '@' y" (at level 50, left associativity).
  Inductive Term : Set :=
  | Base
  | Var of nat
  | Fun of Term & Term.
  Notation "x @ y" := (Fun x y).
  
  Fixpoint Size (t : Term) : nat :=
    match t with
    | Fun t1 t2 => (Size t1 + Size t2).+1
    | _ => 1
    end.

  (* ** *)
  (* == *)
  (* ** *)
  
  Fixpoint eqt (t1 t2 : Term) : bool :=
    match (t1, t2) with
    | (Base, Base) => true
    | (Var n1, Var n2) => n1 == n2
    | (t11 @ t21, t12 @ t22) => eqt t11 t12 && eqt t21 t22
    | (_ , _) => false
  end.
  
  Lemma Fun_eq (t11 t21 t12 t22 : Term) :
    eqt (t11 @ t21) (t12 @ t22) = eqt t11 t12 && eqt t21 t22.
  Proof.
    done.
  Qed.
  
  Lemma Term_eqP : forall (t1 t2 : Term), reflect (t1 = t2) (eqt t1 t2).
  Proof.
    move=> t1 t2.
    apply: (iffP idP).
    (* eqt t1 t2 -> t1 = t2 *)
    - elim: t1 t2.
      + by case.
      + by move=> n1; elim=> n2 // /eqP ->.
      + move=> t11 H1 t12 H2.
        elim=> // t21 _ t22 _ H.
        move: (H1 t21) => <-.
        move: (H2 t22) => <-.
        * done.
        * move: H.
          rewrite Fun_eq => /andP.
            by case.
        * move: H.
          rewrite Fun_eq => /andP.
            by case.
    (* t1 = t2 -> eqt t1 t2 *)
    - move=> ->.
      elim: t2 => //= u1 H1 v1 H2.
        by apply/andP.
  Qed.
  
  Definition Term_Mixin := @EqMixin Term eqt Term_eqP.
  Canonical Term_EqType := @EqType Term Term_Mixin.
  
  Compute (Var 1) @ (Var 2) @ Base == (Var 1) @ (Var 2) @ Base.
  Compute (Var 1) @ Base @ (Var 2) == (Var 1) @ (Var 2) @ Base.

  (* *** *)
  (* \in *)
  (* *** *)
  
  Inductive In x : Term -> Prop :=
  | In_Fun_dom : forall t1 t2, In x t1 -> In x (Fun t1 t2)
  | In_Fun_cod : forall t1 t2, In x t2 -> In x (Fun t1 t2)
  | In_Var : In x (Var x).
  
  Fixpoint inb (t : Term) (x : nat) : bool :=
    match t with
    | Base => false
    | Var y => x == y
    | t1 @ t2 => [predU inb t1 & inb t2] x
    end.
  
  Lemma In_inb (x : nat) (t : Term) : In x t <-> inb t x.
  Proof.
    split.
    - elim => //= t1 t2 Hp Hb; apply/orP.
      + by left.
      + by right.
    - elim: t => //=.
      + move=> y /eqP <-.
          by apply: In_Var.
      + move=> t1 Ht1 t2 Ht2 /orP.
        case=> H.
        * apply: In_Fun_dom.
            by apply: Ht1.
        * apply: In_Fun_cod.
            by apply: Ht2.
  Qed.
  
  Canonical Term_predType := @mkPredType nat Term inb.
  
  Compute 1 \in (Var 1) @ (Var 2) @ Base.
  Compute 3 \notin (Var 1) @ (Var 2) @ Base.
  
  Lemma notIn_Fun x t1 t2 : x \notin t1 @ t2 = (x \notin t1) && (x \notin t2).
  Proof.
    rewrite /mem /in_mem /inb /=.
      by apply: negb_or.
  Qed.
  
  Lemma In_Fun x t1 t2 : x \in t1 @ t2 = (x \in t1) || (x \in t2).
  Proof.
    by rewrite /mem /in_mem /inb /=.
  Qed.
  
  (* ********** *)
  (* [x := t0]t *)
  (* ********** *)
  
  Fixpoint subst (x : nat) (t0 t : Term) : Term :=
    match t with
    | Base => Base
    | Var y => if x == y then t0 else t
    | t1 @ t2 => (subst x t0 t1) @ (subst x t0 t2)
    end.
  
  Lemma eq_in_var (x : nat) : x \in Var x.
  Proof.
    by rewrite /mem /in_mem /inb /=.
  Qed.
  
  Lemma neq_notIn_var (x y : nat) : x <> y -> x \notin Var y.
  Proof.
    rewrite /mem /in_mem /inb /=.
    by move/eqP.
  Qed.
  
  Theorem subst_In_occur x t1 t2 : x \in subst x t1 t2 -> x \in t1.
  Proof.
    elim: t2.
    - done.
    - move=> y.
      rewrite /subst.
      case H : (x == y).
      + done.
      + move: H => /eqP /neq_notIn_var /negP.
        done.
    - move=> t12 H1 t22 H2.
      move/orP.
        by case.
  Qed.
  
  Theorem subst_notIn x t1 t2 : x \notin t2 -> subst x t1 t2 = t2.
  Proof.
    elim: t2.
    - done.                                 (* Base *)
    - move=> y.                             (* Var *)
      rewrite /subst.
      case H : (x == y).
      + move/eqP in H.                      (* x \notin Var x *)
        rewrite H.
        move/negP => Hc.
        exfalso.
        apply: Hc.
          by apply: eq_in_var.
      + done.                               (* x \notin Var x *)
    - move=> t11 H1 t21 H2.                 (* x \notin t11 @ t21 *)
      rewrite notIn_Fun.
      move/andP => [H11 H21] /=.
        by rewrite -{2}(H1 H11) -{2}(H2 H21).
  Qed.

  Theorem subst_In_or x y t1 t2 : x \in (subst y t1 t2) -> (x \in t1) || (x \in t2).
  Proof.
    elim: t2.
    - done.
    - move=> y'.
      rewrite /subst.
      case H : (y == y').
      + move/eqP in H => Hx.
        apply/orP.
          by left.
      + move/eqP in H => Hx.
        apply/orP.
          by right.
    - move=> t11 H1 t21 H2 /=.
      rewrite !In_Fun => /orP.
      case=> [H11 | H21].
      + rewrite Bool.orb_assoc.
        apply/orP.
        left.
          by auto.
      + rewrite [(x \in t11) || (x \in t21)]Bool.orb_comm Bool.orb_assoc.
        apply/orP.
        left.
          by auto.
  Qed.
  
  (*
    (* simpl で let (_, _) = a in Base がただの Base にならない。 *)
  Definition subst_list (subs : seq (nat * Term)) (t : Term) : Term :=
    foldl
      (fun t1 (sub : nat * Term) => let: (x, t0) := sub in subst x t0 t1)
      t subs.
   *)
  
  Definition subst_list (subs : seq (nat * Term)) (t : Term) : Term :=
    foldl
      (fun t1 (sub : nat * Term) => subst sub.1 sub.2 t1)
      t subs.
  
  Lemma subst_list_app subs1 subs2 t :
      subst_list (subs1 ++ subs2) t = subst_list subs2 (subst_list subs1 t).
  Proof.
      by apply: foldl_cat.
  Qed.
  
  Lemma subst_list_Base subs : subst_list subs Base = Base.
  Proof.
    elim: subs.
    + done.
    + by move=> a l /= IH.
  Qed.

  Lemma subst_list_Fun subs t1 t2 :
    subst_list subs (t1 @ t2) = (subst_list subs t1) @ (subst_list subs t2).
  Proof.
    elim: subs t1 t2.
    + done.
    + move=> a l IH t1 t2 /=.
      by apply: IH.
  Qed.
  
End Types.

(* END *)
