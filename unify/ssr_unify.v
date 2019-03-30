From mathcomp Require Import all_ssreflect.
Require Import Finite_sets_facts.

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
  
  Lemma size_gt0 (t : Term) : 0 < Size t.
  Proof.
      by elim: t.
  Qed.
  
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
  
  Theorem FV_Finite t : Finite nat (In^~ t). (* fun x => In x t *)
  Proof.
    elim: t => [ | x | t1 IHt1 t2 IHt2 ].
    - rewrite (Extensionality_Ensembles nat (In^~ Base) (Empty_set nat)).
      + by apply: Empty_is_finite.
      + by split=> [x H | x H]; inversion H.
    - rewrite (Extensionality_Ensembles nat (In^~ (Var x)) (Singleton nat x)).
      + by apply: Singleton_is_finite.
      + split=> [y H | y H]; inversion H.
        * done.
        * by apply: In_Var.                 (* constructor *)
    - rewrite (Extensionality_Ensembles
                 nat (In^~ (t1 @ t2))
                 (Union nat (fun x => In x t1) (fun x => In x t2))).
      + by apply: Union_preserves_Finite.
      + split=> x H; inversion H.
        * by left.
        * by right.
        * by apply: In_Fun_dom.             (* constructor *)
        * by apply: In_Fun_cod.             (* constructor *)
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
        rewrite -H.
        move/negP.
          by move: (eq_in_var x).           (* x \in Var x から矛盾 *)
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
      (fun t1 (sub : nat * Term) =>
         let: (x, t0) := (sub.1, sub.2) in subst x t0 t1)
      t
      subs.
  
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
  
(*
  Definition unifies subs t1 t2 := subst_list subs t1 = subst_list subs t2.
*)
  Notation unifies subs t1 t2 := (subst_list subs t1 = subst_list subs t2).
  
  Lemma subst_preserves_unifies x t0 subs t :
    unifies subs (Var x) t0 -> unifies subs t (subst x t0 t).
  Proof.
    elim: t.
    - done.
    - move=> y.
      case H : (x == y) => /=.
      + move: (H) => /eqP Hxy.
          by rewrite -[in (Var y)]Hxy H.
      + by rewrite H.
    - move=> t1 IHt1 t2 IHt2 Hu.
      rewrite subst_list_Fun /=.
      rewrite subst_list_Fun /=.
      f_equal.
      + by apply: IHt1.
      + by apply: IHt2.
  Qed.

  (*
  leq_addr と leq_addl を使う。
  
  Lemma test1' p n : p <= p + n.
  Proof.
    move: (leq_add2l p 0 n).
    have H2 : p + 0 = p by [].
    rewrite [p + 0]H2 => ->.
    (* 0 <= n *)
    done.
  Qed.
  
  (* ~(p + n < p) のときは、leqNgt で書き換える。実行例 *)
  Lemma test1 p m : ~(p + m < p).
  Proof.
    move: (test1' p m).
    rewrite leqNgt => /negP.
    by apply.
  Qed.
   *)  
  
  (* バニラCoq の同名の補題 *)
  Lemma lt_succ_l m n : m.+1 < n -> m < n.
  Proof.
    move/ltP => H.
    apply/ltP.
    Check PeanoNat.Nat.lt_succ_l.
      by apply: PeanoNat.Nat.lt_succ_l.
  Qed.
  
  (* バニラCoq の同名の補題 *)
  Lemma le_lt_add_lt n m p q :
    n <= m -> p + m < q + n -> p < q.
  Proof.
    move=> /leP H /ltP Hpm.
    apply/ltP.
    move: H Hpm.
      by apply: PeanoNat.Nat.le_lt_add_lt.
  Qed.
  
  Lemma lt_mpn__lt_mn p m n : m + p < n -> m < n.
  Proof.
    elim: p => [| n' IHn H].
    - have H2 : m + 0 = m by [].
        by rewrite H2.
    - apply: IHn.
      rewrite addnS in H.
        by apply: lt_succ_l.
     Restart.

     have H : n + 0 = n by [].
     rewrite -[in m + p < n]H.
       by apply: (le_lt_add_lt 0 p m n).
  Qed.
  
  Lemma lt_mpn__le_mn (p m n : nat) : 0 < p -> m + p < n -> m <= n.
  Proof.
    elim: m n.
    - done.
    - move=> m' IHm => n H1 H2.
      rewrite addSnnS in H2.
        by move/lt_mpn__lt_mn in H2.
  Qed.
  
  Lemma lt_pmn__le_mn (p m n : nat) : 0 < p -> p + m < n -> m <= n.
  Proof.
    rewrite [p + m]addnC.
      by apply: lt_mpn__le_mn.
  Qed.
  
  Lemma unifies_occur x t :
    Var x <> t -> x \in t -> forall subs, ~unifies subs (Var x) t.
  Proof.
    move=> Hneq Hoccur subs Hu.
    have H : (Size (subst_list subs (Var x)) >= Size (subst_list subs t))
      by rewrite Hu.
    move/In_inb in Hoccur.
    elim: Hoccur Hneq H => [ t1 t2 HIn IHHoccur | t1 t2 HIn IHHoccur | ] Hneq H.
    - rewrite subst_list_Fun in H.
      apply: IHHoccur.
      + move=> Heq.
        rewrite Heq /= in H.
        Search _ (_ <= _ + _).
        (* leq_addr の引数の順番に注意せよ。 *)
        move: (leq_addr (Size (subst_list subs t2)) (Size (subst_list subs t1))).
        by rewrite leqNgt => /negP.         (* not lt にする。 *)
      + rewrite /= in H.
        apply: (lt_mpn__le_mn (Size (subst_list subs t2))).
        * by apply: size_gt0.
        * done.
    - rewrite subst_list_Fun in H.
      apply: IHHoccur.
      + move=> Heq.
        rewrite Heq /= in H.
        move: (leq_addl (Size (subst_list subs t1)) (Size (subst_list subs t2))).
        by rewrite leqNgt => /negP.         (* not lt にする。 *)
      + rewrite /= in H.
        apply: (lt_pmn__le_mn (Size (subst_list subs t1))).
        * by apply: size_gt0.
        * done.
    - done.
  Qed.
End Types.

Module Constraint.
  Definition Term := (Types.Term * Types.Term)%type.

  Definition Size constraints :=
    foldr
      plus
      0
      (map
         (fun c : Term =>
            let: (t1, t2) := (c.1, c.2) in Types.Size t1 + Types.Size t2)
         constraints).
  
  Inductive Exists (A : Type) (P : A -> Prop) : seq A -> Prop :=
  | Exists_cons_hd : forall (x : A) (s : seq A), P x -> Exists A P (x :: s)
  | Exists_cons_tl : forall (x : A) (s : seq A), Exists A P s -> Exists A P (x :: s).
  
  Definition In (x : nat) (constraints : seq Term) : Prop :=
    Exists Term
           (fun c : Term =>
              let: (t1, t2) := (c.1, c.2) in Types.In x t1 \/ Types.In x t2)
           constraints.
  
  Definition inb (s : seq Term) (x : nat) : bool :=
    has
      (fun c : Term =>
         let: (t1, t2) := (c.1, c.2) in Types.inb t1 x || Types.inb t2 x)
      s.
  
  Lemma In_inb (x : nat) (s : seq Term) : In x s <-> inb s x.
  Proof.
    split.
    - elim: s => /= [| a s IHs] H.
      + by inversion H.
      + inversion H; subst; clear H.
        * case: H1 => H.
          ** apply/orP/or_introl/orP/or_introl. (* left. left *)
               by apply/Types.In_inb.
          ** apply/orP/or_introl/orP/or_intror. (* left. right *)
               by apply/Types.In_inb.
        * apply/orP/or_intror.              (* right *)
            by apply: IHs.
    - elim: s => /= [| a s IHs] H.
      + done.
      + move/orP in H.
        case: H => H.
        * apply Exists_cons_hd.
          move/orP in H.
          case: H => H.
          ** by apply/or_introl/Types.In_inb. (* left *)
          ** by apply/or_intror/Types.In_inb. (* right *)
        * apply Exists_cons_tl.
            by move/IHs in H.
  Qed.
  
  Lemma FV_Finite : forall constraints, Finite _ (fun x => In x constraints).
  Proof.


(* END *)
