From HB Require Import structures.          (* MathComp2 *)
From mathcomp Require Import all_ssreflect.

Module List.
  (* List.v にある定義 *)
  (* 互換のために、reflectとともに残してある。 *)
  
  Inductive Forall {A : Type} (P : A -> Prop) : seq A -> Prop :=
  | Forall_nil : Forall P nil
  | Forall_cons : forall (x : A) (s : seq A), P x -> Forall P s -> Forall P (x :: s).
  #[global] Hint Constructors Forall.
  
  Inductive Exists {A : Type} (P : A -> Prop) : seq A -> Prop :=
  | Exists_cons_hd : forall (x : A) (s : seq A), P x -> Exists P (x :: s)
  | Exists_cons_tl : forall (x : A) (s : seq A), Exists P s -> Exists P (x :: s).
  #[global] Hint Constructors Exists.
  
  Lemma ForallP {A : Type} (P : A -> Prop) (p : A -> bool) :
    (forall (a : A), reflect (P a) (p a)) ->
    forall (s : seq A), reflect (Forall P s) (all p s).
  Proof.
    move=> H s.
    apply/(iffP idP).
    - elim: s => [Hp | a s IHs /= /andP].
      + by apply: Forall_nil.
      + case.
        move/H => Hpa Hps.
        apply: Forall_cons.
        * done.
        * by apply: IHs.
    - elim: s => /= [| a s IHs].
      + done.
      + move=> HP.
        apply/andP.
        inversion HP; subst.
        split.
        * by apply/H.
        * by apply IHs.
  Qed.
  
  Lemma ExistsP {A : Type} (P : A -> Prop) (p : A -> bool) :
    (forall (a : A), reflect (P a) (p a)) ->
    forall (s : seq A), reflect (Exists P s) (has p s).
  Proof.
    move=> H s.
    apply/(iffP idP).
    - elim: s => [Hp | a s IHs /= /orP].
      + done.
      + case=> [Hpa | Hpa].
        * apply: Exists_cons_hd.
          by apply/H.
        * apply: Exists_cons_tl.
          by apply: IHs.
    - elim: s => /= [| a s IHs] HP.
      + by inversion HP.
      + apply/orP.
        inversion HP; subst.
        * left.
          by apply/H.
        * right.
          by apply: IHs.
  Qed.


  Fixpoint In {A : Type} (a : A) (s : seq A) : Prop :=
    match s with
    | [::] => False
    | b :: m => b = a \/ In a m
    end.
  
  Lemma In_inb {A : eqType} (x : A) (s : seq A) : In x s <-> x \in s.
  Proof.
    elim: s.
    - done.
    - move=> a s IHs.
      split=> /=; rewrite inE.
      + case=> H.
        * by apply/orP/or_introl/eqP.
        * by apply/orP/or_intror/IHs.
      + move/orP; case.
        * move/eqP => ->.
          by left.
        * move=> H.
          move/IHs in H.
          by right.
  Qed.
  
  Lemma InP {A : eqType} (x : A) (s : seq A) : reflect (In x s) (x \in s).
  Proof.
    apply: (iffP idP) => H.
    - by apply/In_inb.
    - by apply/In_inb.
  Qed.

End List.

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
  
  Lemma Term_eqP (t1 t2 : Term) : reflect (t1 = t2) (eqt t1 t2).
  Proof.
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
  
  HB.instance Definition _ := hasDecEq.Build Term Term_eqP. (* MathComp2 *)
  
  Compute (Var 1) @ (Var 2) @ Base == (Var 1) @ (Var 2) @ Base.
  Compute (Var 1) @ Base @ (Var 2) == (Var 1) @ (Var 2) @ Base.

  (* *** *)
  (* \in *)
  (* *** *)
  
  Inductive In x : Term -> Prop :=
  | In_Fun_dom : forall t1 t2, In x t1 -> In x (Fun t1 t2)
  | In_Fun_cod : forall t1 t2, In x t2 -> In x (Fun t1 t2)
  | In_Var : In x (Var x).
  #[global] Hint Constructors In.
  
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
  
  Lemma InP (x : nat) (t : Term) : reflect (In x t) (inb t x).
  Proof.
    apply: (iffP idP) => H.
    - by apply/In_inb.
    - by apply/In_inb.
  Qed.
  
(*
  Canonical Term_predType := @mkPredType nat Term inb.
*)
  Canonical Term_predType := @PredType nat Term inb.
  
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
  
  Lemma eq_in_varE (x y : nat) : (x == y) = (x \in Var y).
  Proof.
    apply/idP/idP.
    - move/eqP => H.
      rewrite -H.
      by apply: eq_in_var.
    - move/InP => H.
      by inversion H.
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
    - move=> t21 IHt21 t22 IHt22.
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
    - move=> t21 IHt21 t22 IHt22.           (* x \notin t11 @ t21 *)
      rewrite notIn_Fun.
      move/andP => [H11 H21] /=.
      by rewrite -{2}(IHt21 H11) -{2}(IHt22 H21).
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
    + move=> [x t] subs' IHsubs' t1 t2 /=.
      by apply: IHsubs'.
  Qed.
  
  Notation unifies subs t1 t2 := (subst_list subs t1 = subst_list subs t2).
  
  Notation unifiesb subs t1 t2 := (subst_list subs t1 == subst_list subs t2).

  Lemma unifiesP subs t1 t2 : reflect (unifies subs t1 t2) (unifiesb subs t1 t2).
  Proof.
    by apply: eqP.
  Qed.
  
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
      f_equal.                              (* 両辺を @ で分ける。 *)
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
    rewrite -{1}[n]addn0.
    by apply: le_lt_add_lt.
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
    elim: Hoccur Hneq H => [t1 t2 HIn IHHoccur | t1 t2 HIn IHHoccur |] Hneq H.
    - rewrite subst_list_Fun in H.
      apply: IHHoccur.
      + move=> Heq.
        rewrite Heq /= in H.
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

  Lemma unify_same sub t : unifiesb sub t t.
  Proof.
    done.
  Qed.

  Lemma unify_comm sub t1 t2 : unifiesb sub t1 t2 = unifiesb sub t2 t1.
  Proof.
    done.
  Qed.
  
  Lemma unify_fun_equal subs t11 t12 t21 t22 :
    (subst_list subs t11 @ subst_list subs t12) ==
    (subst_list subs t21 @ subst_list subs t22) =
    (subst_list subs t11 == subst_list subs t21) &&
    (subst_list subs t12 == subst_list subs t22).
  Proof.
    apply/idP/idP.
    - move=> /eqP H.
      inversion H as [[H1 H2]].
      apply/andP.
      by split.
    - move=> /andP [H1 H2].
      by apply/eqP; f_equal; apply/eqP.
  Qed.
  
  Lemma unify_fun subs t11 t12 t21 t22 :
    unifiesb subs t11 t21 && unifiesb subs t12 t22 =
    unifiesb subs (t11 @ t12) (t21 @ t22).
  Proof.
    by rewrite !subst_list_Fun unify_fun_equal.
  Qed.
  
End Types.

Notation "x @ y" := (Types.Fun x y) (at level 50, left associativity).
Notation Var x := (Types.Var x).
Notation Base := (Types.Base).

HB.instance Definition _ := hasDecEq.Build Types.Term Types.Term_eqP. (* MathComp2 *)
  
Compute (Var 1) @ (Var 2) @ Base == (Var 1) @ (Var 2) @ Base.
Compute (Var 1) @ Base @ (Var 2) == (Var 1) @ (Var 2) @ Base.

Canonical Types_Term := @PredType nat Types.Term Types.inb.

Compute 1 \in (Var 1) @ (Var 2) @ Base.
Compute 3 \notin (Var 1) @ (Var 2) @ Base.


(* Forall_map と Forall_impl の合わせ技の bool 版 *)

Lemma all_impl {A : Type} (p q : pred A) (s : seq A) :
  (forall a, p a -> q a) -> all p s -> all q s.
Proof.
  move=> Hp.
  elim: s.
  - done.
  - move=> a s IHs /= /andP.
    case=> Hpa Haps.
    apply/andP.
    split.
    + by apply: Hp.
    + by apply: IHs.
Qed.

Lemma all__all_map {A : Type} (p : pred A) (f : A -> A) (s : seq A) :
  (forall a, p a = p (f a)) -> all p s = all p [seq f i | i <- s].
Proof.
  move=> Hp.
  apply/idP/idP.
  - elim: s.
    + done.
    + move=> a s IHs /= /andP.
      case=> Hpa Haps.
      apply/andP.
      split.
      * by rewrite -Hp.
      * by apply: IHs.
  - elim: s.
    + done.
    + move=> a s IHs /= /andP.
      case=> Hpfa Haps.
      apply/andP.
      split.
      * by rewrite Hp.
      * by apply: IHs.
Qed.

(* all_map でよい。 *)
Check all_map
  : forall (T1 T2 : Type) (f : T1 -> T2) (a : pred T2) (s : seq T1),
    all a [seq f i | i <- s] = all (preim f a) s.
(*
Lemma all__all_map' {A : Type} (p : pred A) (f : A -> A) (s : seq A) :
  all (fun a => p (f a)) s = all p [seq f i | i <- s].
Proof.
  rewrite all_map.
  rewrite /preim.
  done.

  Restart.
  apply/idP/idP.
  - elim: s.
    + done.
    + move=> a s IHs /= /andP => H.
      case: H => H1 H2.
      apply/andP.
      split.
      * done.
      * apply: IHs.
        done.
  - elim: s.
    + done.
    + move=> a s IHs /= /andP H.
      case: H => H1 H2.
      apply/andP.
      split.
      * done.
      * by apply: IHs.
Qed.
*)

Module Constraint.
  Definition Term := (Types_Term * Types_Term)%type.  
  Definition Terms := (seq Term)%type.
  
  Fixpoint eqt (t1 t2 : Term) : bool :=
    (t1.1 == t2.1) && (t1.2 == t2.2).
  
  Lemma Term_eqP (t1 t2 : Term) : reflect (t1 = t2) (eqt t1 t2).
  Proof.
    apply: (iffP idP).
    - case: t1 => t1_1 t2_1; case: t2 => t1_2 t2_2 /=.
      move/andP.
      case.
      move/eqP => <-.
      move/eqP => <-.
      done.
    - move=> <-.
      case: t1 => t1' t2' /=.
      apply/andP.
      done.
  Qed.
  
  Definition Size constraints :=
    foldr
      plus
      0
      (map
         (fun c : Term => Types.Size c.1 + Types.Size c.2)
         constraints).
  
  Definition In (x : nat) (constraints : Terms) : Prop :=
    List.Exists (fun c : Term => Types.In x c.1 \/ Types.In x c.2)
           constraints.
  
  Definition inb (s : Terms) (x : nat) : bool :=
    has (fun c : Term => (x \in c.1) || (x \in c.2)) s.
  
  Lemma In_inb (x : nat) (s : Terms) : In x s <-> inb s x.
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
        * apply: List.Exists_cons_hd.
          move/orP in H.
          case: H => H.
          ** by apply/or_introl/Types.In_inb. (* left *)
          ** by apply/or_intror/Types.In_inb. (* right *)
        * apply: List.Exists_cons_tl.
          by move/IHs in H.
  Qed.
  
  Lemma InP (x : nat) (s : Terms) : reflect (In x s) (inb s x).
  Proof.
    apply: (iffP idP) => H.
    - by apply/In_inb.
    - by apply/In_inb.
  Qed.
  
  (* In_inb を使わず、ExistsP を使った別証明。 *)
  Lemma InP' (x : nat) (s : Terms) : reflect (In x s) (inb s x).
  Proof.
    apply/List.ExistsP => a.
    apply/(iffP idP).
    - move/orP => [/Types.InP H1 | /Types.InP H2].
      + by left.
      + by right.
    - case=> /Types.InP H.
      + apply/orP.
        by left.
      + apply/orP.
        by right.
  Qed.
  
  HB.instance Definition _ := hasDecEq.Build Constraint.Term Term_eqP. (* MathComp2 *)
  
  Check (Var 1 @ Var 2, Base) : Constraint.Term.
  Compute (Var 1 @ Var 2, Base) == (Var 1 @ Var 2, Base).

  Definition Constraint_Terms := (seq Constraint.Term)%type.
  Canonical Constraint_Term :=
    @PredType nat (Constraint_Terms) Constraint.inb.

  Check [:: (Var 1, Var 2)] : Constraint.Terms.
  Check [:: (Var 1, Var 2)] : seq Constraint.Term.
  Check [:: (Var 1, Var 2)] : Constraint_Terms.
  
  Definition sc := [:: (Var 1, Var 2)] : seq Constraint.Term.
  Definition sc' := [:: (Var 1, Var 2)] : Constraint.Terms.
  Definition sc'' := [:: (Var 1, Var 2)] : Constraint_Terms.
  
  Compute sc == sc''.
  Compute Constraint.inb sc'' 1.
  Compute 1 \in sc''.
  
  (* \in の右に書けるように EqType を返すようにする。 *)
  (* [x := t0](constraints) *)
  Definition subst x t0 constraints : Constraint_Terms :=
    [seq (Types.subst x t0 c.1, Types.subst x t0 c.2)
    | c <- constraints].
  (* 
     map (fun c : Term => (Types.subst x t0 c.1, Types.subst x t0 c.2))
          constraints.
   *)
  
  Theorem subst_In_occur x t0 constraints :
    x \in (subst x t0 constraints) -> x \in t0.
  (* In x (subst x t0 constraints) -> Types.In x t0 *)
  Proof.
    elim: constraints => [| [t1 t2] constraints IHconstraints' HIn] //=.
    move/InP in HIn.
    inversion HIn as [[t1' t2'] constraints'' Hor |]; subst.
    - case: Hor => /= [HIn' | HIn'].
      + apply: (@Types.subst_In_occur x t0 t1).
        by apply/Types.InP.
      + apply: (@Types.subst_In_occur x t0 t2).
        by apply/Types.InP.
    - apply: IHconstraints'.
      by apply/InP.
  Qed.    
  
  Theorem subst_In_or x y t0 (constraints : Constraint_Terms) :
    x \in (subst y t0 constraints) -> (x \in t0) || (x \in constraints).
  Proof.
    move=> HIn.
    apply/orP.                    (* 最初にゴールをPropにしておく。 *)
    elim: constraints HIn => [| [t1 t2] constraints IHconstraints' HIn] //=.
    move/InP in HIn.
    inversion HIn as [[t1' t2'] constraints'' Hor | [t1' t2'] constraints'' HIn'].
    subst. 
    - case: Hor => //= /Types.InP HIn';
                     case: (Types.subst_In_or _ _ _ _ HIn') => /orP [H | H].
      + by left.
      + apply/or_intror/InP.
        left.                       (* apply/or_introl は使えない。 *)
        left.
        by apply/Types.InP.
      + by left.
      + apply/or_intror/InP.
         left.
         right.
         by apply/Types.InP.
            
    - move/InP in HIn'.
      case: (IHconstraints' HIn') => [H' | H'].
      * by left.
      * apply/or_intror/InP.
        right.
        by apply/InP.
  Qed.
  
  Notation subst_list subs constraints :=
    [seq (Types.subst_list subs p.1, Types.subst_list subs p.2) |
     p <- constraints].
(*
    (map (fun p : Term => (Types.subst_list subs p.1, Types.subst_list subs p.2))
         constraints).
*)  
  
  Definition unifies subs constraints :=
    List.Forall (fun p : Term => Types.unifies subs p.1 p.2) constraints.
  
  Definition unifiesb subs constraints :=
    all (fun p : Term => Types.unifiesb subs p.1 p.2) constraints.

  Lemma unifiesP subs constraints :
    reflect (unifies subs constraints) (unifiesb subs constraints).  
  Proof.
    apply/List.ForallP => a.
    by apply/(iffP idP) => /Types.unifiesP.
  Qed.
  
  Theorem subst_preserves_unifiesb x t0 subs constraints :
    Types.unifies subs (Types.Var x) t0 ->
    unifiesb subs constraints ->
    unifiesb subs (subst x t0 constraints).
  Proof.
    move=> Hunifies Hunifies'.
    rewrite /unifiesb.
    rewrite -all__all_map => /=.
    - done.
    - move=> [t1 t2] /=.
      by rewrite -!(Types.subst_preserves_unifies _ _ _ _ Hunifies).
  Qed.
  
  (* unify_sound_same *)
  (* unify_complete_same *)
  Lemma unify_same t subs constraints :
    unifiesb subs constraints = unifiesb subs ((t, t) :: constraints).
  Proof.
    by rewrite /= Types.unify_same.
  Qed.

  Lemma unify_sound_subst x t subs constraints :
    x \notin t ->
    unifiesb subs (subst x t constraints) ->
    unifiesb ((x, t) :: subs) ((Types.Var x, t) :: constraints).
  Proof.
    move => Hoccur Hunifies /=.
    apply/andP.
    split.
    - case H : (x == x) => /=.
      + by rewrite Types.subst_notIn.
      + by move/eqP in H.
    - rewrite /unifiesb.
      rewrite /unifiesb in Hunifies.
      apply: (all_impl
                (fun p : Term => Types.subst_list subs (Types.subst x t p.1) ==
                                 Types.subst_list subs (Types.subst x t p.2))).

      + done.
      + rewrite /unifiesb in Hunifies.
        rewrite all_map in Hunifies.
        by simpl in Hunifies.        
  Qed.
  
  (* unify_sound_comm *)
  Lemma unify_comm t1 t2 subs constraints :
    unifiesb subs ((t2, t1) :: constraints) = unifiesb subs ((t1, t2) :: constraints).
  Proof.
    rewrite /=.
    by rewrite Types.unify_comm.
  Qed.
  
  (* unify_sound_fun *)
  (* unify_complete_fun *)
  Lemma unify_fun constraints t11 t12 t21 t22 subs :
      unifiesb subs ((t11, t21) :: (t12, t22) :: constraints) =
      unifiesb subs ((Types.Fun t11 t12, Types.Fun t21 t22) :: constraints).
  Proof.
    by rewrite /= -Types.unify_fun andbA.
  Qed.

End Constraint.

(*
← は、定義での参照をしめす。
.                 Types                   Constraint
.
subst             [x := t0]t      ←      [x := t0]constraints
.                 ↑
subst_list        subs t          ←      subs     constraints
.                 ↑
unfies            subs t1 t2      ←      subs     constraints (要素間の=)
                  ||                               ||
(subst_list subs t1 = subst_list subs t2)          [::(t1,t2);.....;(tn1, tn2)]

*)

(* END *)
