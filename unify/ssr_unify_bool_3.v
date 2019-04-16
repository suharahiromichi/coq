(* Constraint.In を \in 中置記法でかけるようにする。 *)
(* 変数をリテラルにして、finType にする。 *)
(* Constraint の変数の数 (cardinal) を #|inb cardinals| とかけるようにする。 *)
(* 互換性の部分とその reflect をのぞいて、Prop を削除した。 *)

From mathcomp Require Import all_ssreflect.
Require Import Recdef Wf_nat.

Module List.
  (* List.v にある定義 *)
  (* 互換のために、reflectとともに残してある。 *)
  
  Inductive Forall {A : Type} (P : A -> Prop) : seq A -> Prop :=
  | Forall_nil : Forall P nil
  | Forall_cons : forall (x : A) (s : seq A), P x -> Forall P s -> Forall P (x :: s).
  Hint Constructors Forall.
  
  Inductive Exists {A : Type} (P : A -> Prop) : seq A -> Prop :=
  | Exists_cons_hd : forall (x : A) (s : seq A), P x -> Exists P (x :: s)
  | Exists_cons_tl : forall (x : A) (s : seq A), Exists P s -> Exists P (x :: s).
  Hint Constructors Exists.
  
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
        * by apply: IHs.
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
        * move/eqP => ->. by left.
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

Module Literal.
  
  Inductive Literal := a | b | c | f | g | h | x | y | z.
  
  Definition eqLiteral (x y : Literal) :=
    match (x, y) with
    | (a, a) => true
    | (b, b) => true
    | (c, c) => true
    | (f, f) => true
    | (g, g) => true
    | (h, h) => true
    | (x, x) => true
    | (y, y) => true
    | (z, z) => true
    | _ => false
    end.
  
  Lemma Literal_eqP (x y : Literal) : reflect (x = y) (eqLiteral x y).
  Proof.
    rewrite /eqLiteral.
      by apply: (iffP idP); case: x; case: y.
  Qed.
  
  Definition Literal_eqMixin := EqMixin Literal_eqP.
  Canonical Literal_eqType := EqType Literal Literal_eqMixin.
  
  Definition Literal_enum := [:: a; b; c; f; g; h; x; y; z].

  Definition Literal_pickle (x : Literal_eqType) : nat :=
    match x with
    | a => 0
    | b => 1
    | c => 2
    | f => 3
    | g => 4
    | h => 5
    | x => 6
    | y => 7
    | z => 8
    end.
  
  Definition Literal_unpickle (n : nat) : option Literal_eqType :=
    match n with
    | 0 => Some a
    | 1 => Some b
    | 2 => Some c
    | 3 => Some f
    | 4 => Some g
    | 5 => Some h
    | 6 => Some x
    | 7 => Some y
    | 8 => Some z
    | _ => None
    end.

  Lemma Literal_pcancel : pcancel Literal_pickle Literal_unpickle.
  Proof.
    by case.
  Qed.
  
  Lemma Literal_finiteP (x : Literal_eqType)  :
    (count_mem x) Literal_enum = 1.
  Proof.
    by case: x.
  Qed.

  Lemma Literal_uniq : uniq Literal_enum.
  Proof.
    done.
  Qed.
  (* UniqFinMixin に使えるはずだが。。。 *)
  
End Literal.

Definition Literal_eqMixin := EqMixin Literal.Literal_eqP.
Canonical Literal_eqType := EqType Literal.Literal Literal_eqMixin.
Canonical Literal_eqType' := [eqType of Literal.Literal].

Definition Literal_countMixin := CountMixin Literal.Literal_pcancel.
Definition Literal_choiceMixin := CountChoiceMixin Literal_countMixin.

Canonical Literal_choiceType := ChoiceType Literal.Literal Literal_choiceMixin.
Canonical Literal_countType := CountType Literal_choiceType Literal_countMixin.

Definition Literal_finMixin :=
  @FinMixin Literal_countType Literal.Literal_enum Literal.Literal_finiteP.
Canonical Literal_finType := FinType Literal.Literal Literal_finMixin.

(* ちゃんと定義できていことを確認する。 *)
Check Literal_eqType : eqType.
Check Literal_choiceType : choiceType.
Check Literal_countType : countType.
Check Literal_finType : finType.

Notation Literal := Literal.Literal.        (* !!!!! *)

Module Types.

  Reserved Notation "x '@' y" (at level 50, left associativity).
  Inductive Term : Set :=
  | Base
  | Var of Literal                          (* !!!!! *)
  | Fun of Term & Term.
  Notation "x @ y" := (Fun x y).
  
  Notation varx := (Var (Literal.x)).
  Notation vary := (Var (Literal.y)).
  Notation varz := (Var (Literal.z)).
  
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
  
  Definition Term_Mixin := @EqMixin Term eqt Term_eqP.
  Canonical Term_EqType := @EqType Term Term_Mixin.
  
  Compute varx @ vary @ Base == varx @ vary @ Base.
  Compute varx @ Base @ vary == varx @ vary @ Base.

  (* *** *)
  (* \in *)
  (* *** *)
  
  Inductive In x : Term -> Prop :=
  | In_Fun_dom : forall t1 t2, In x t1 -> In x (Fun t1 t2)
  | In_Fun_cod : forall t1 t2, In x t2 -> In x (Fun t1 t2)
  | In_Var : In x (Var x).
  Hint Constructors In.
  
  Fixpoint inb (t : Term) (x : Literal) : bool :=
    match t with
    | Base => false
    | Var y => x == y
    | t1 @ t2 => [predU inb t1 & inb t2] x
    end.
  
  Lemma In_inb (x : Literal) (t : Term) : In x t <-> inb t x.
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
  
  Lemma InP (x : Literal) (t : Term) : reflect (In x t) (inb t x).
  Proof.
    apply: (iffP idP) => H.
    - by apply/In_inb.
    - by apply/In_inb.
  Qed.
  
  Canonical Term_predType := @mkPredType Literal Term inb.
  
  Compute Literal.x \in varx @ vary @ Base.
  Compute Literal.y \notin varx @ vary @ Base.
  
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
  
  Fixpoint subst (x : Literal) (t0 t : Term) : Term :=
    match t with
    | Base => Base
    | Var y => if x == y then t0 else t
    | t1 @ t2 => (subst x t0 t1) @ (subst x t0 t2)
    end.
  
  Lemma eq_in_var (x : Literal) : x \in Var x.
  Proof.
    by rewrite /mem /in_mem /inb /=.
  Qed.
  
  Lemma eq_in_varE (x y : Literal) : (x == y) = (x \in Var y).
  Proof.
    apply/idP/idP.
    - move/eqP => H.
      rewrite -H.
        by apply: eq_in_var.
    - move/InP => H.
        by inversion H.
  Qed.
  
  Lemma neq_notIn_var (x y : Literal) : x != y -> x \notin Var y.
  Proof.
    rewrite /mem /in_mem /inb /=.
    done.
  Qed.
  
  Theorem subst_In_occur x t1 t2 : x \in subst x t1 t2 -> x \in t1.
  Proof.
    elim: t2.
    - done.
    - move=> y.
      rewrite /subst.
      case H : (x == y).
      + done.
      + move: H => /(introT eqP).  (* /eqP だと <> になってしまう。 *)
        rewrite eqbF_neg => /neq_notIn_var.
          by move/negP.
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
      (fun t1 (sub : Literal * Term) => let: (x, t0) := sub in subst x t0 t1)
      t subs.
   *)
  
  Definition subst_list (subs : seq (Literal * Term)) (t : Term) : Term :=
    foldl
      (fun t1 (sub : Literal * Term) =>
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

Notation Term := Types.Term.
Notation Var x := (Types.Var x).
Notation Base := (Types.Base).
Notation "x @ y" := (Types.Fun x y) (at level 50, left associativity).

Notation varx := (Types.Var (Literal.x)).
Notation vary := (Types.Var (Literal.y)).
Notation varz := (Types.Var (Literal.z)).

Definition Types_Term_Mixin := @EqMixin Types.Term Types.eqt Types.Term_eqP.
Canonical Types_Term_EqType := @EqType Types.Term Types_Term_Mixin.
  
Compute varx @ vary @ Base == varx @ vary @ Base.
Compute varx @ Base @ vary == varx @ vary @ Base.

Canonical Types_Term_predType := @mkPredType Literal Types.Term Types.inb.
  
Compute Literal.x \in varx @ vary @ Base.
Compute Literal.y \notin varx @ vary @ Base.


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
  Definition Term := (Types_Term_EqType * Types_Term_EqType)%type.
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
      addn                    (* plus だと coq_nat になってしまう。 *)
      0
      (map
         (fun c : Term => Types.Size c.1 + Types.Size c.2)
         constraints).
  
  Definition In (x : Literal) (constraints : Terms) : Prop :=
    List.Exists (fun c : Term => Types.In x c.1 \/ Types.In x c.2)
           constraints.
  
  Definition inb (s : Terms) (x : Literal) : bool :=
    has (fun c : Term => (x \in c.1) || (x \in c.2)) s.
  
  Lemma In_inb (x : Literal) (s : Terms) : In x s <-> inb s x.
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
  
  Lemma InP (x : Literal) (s : Terms) : reflect (In x s) (inb s x).
  Proof.
    apply: (iffP idP) => H.
    - by apply/In_inb.
    - by apply/In_inb.
  Qed.
  
  (* In_inb を使わず、ExistsP を使った別証明。 *)
  Lemma InP' (x : Literal) (s : Terms) : reflect (In x s) (inb s x).
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
  
  Definition Constraint_Term_Mixin :=
    @EqMixin Constraint.Term Constraint.eqt Term_eqP.
  Canonical Constraint_Term_EqType :=
    @EqType Constraint.Term Constraint_Term_Mixin.

  Check (varx @ vary, Base) : Constraint.Term.
  Check (varx @ vary, Base) : Constraint_Term_EqType.
  
  Compute (varx @ vary, Base) == (varx @ vary, Base).

  Definition Constraint_Terms_EqType := (seq Constraint_Term_EqType)%type.
  
  Canonical Constraint_Term_predType :=
    @mkPredType Literal (Constraint_Terms_EqType) Constraint.inb.

  Check [:: (varx, vary)] : Constraint.Terms.
  Check [:: (varx, vary)] : seq Constraint_Term_EqType.
  Check [:: (varx, vary)] : Constraint_Terms_EqType.
  
  Definition sc := [:: (varx, vary)] : seq Constraint_Term_EqType.
  Definition sc' := [:: (varx, vary)] : Constraint.Terms.
  Definition sc'' := [:: (varx, vary)] : Constraint_Terms_EqType.
  
  Compute sc == sc''.
  Compute Constraint.inb sc'' Literal.x.
  Compute Literal.x \in sc''.
  
  (* \in の右に書けるように EqType を返すようにする。 *)
  (* [x := t0](constraints) *)
  Definition subst x t0 constraints : Constraint_Terms_EqType :=
    [seq (Types.subst x t0 c.1, Types.subst x t0 c.2)
    | c <- constraints].
  (* 
     map (fun c : Term => (Types.subst x t0 c.1, Types.subst x t0 c.2))
          constraints.
   *)
  
  Theorem subst_In_occur x t0 constraints :
    x \in (subst x t0 constraints) -> x \in t0.
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
  
  Theorem subst_In_or x y t0 (constraints : Constraint_Terms_EqType) :
    x \in subst y t0 constraints -> x \in t0 \/ x \in constraints.
  Proof.
    move=> HIn.
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

Definition Constraint_Term_Mixin :=
  @EqMixin Constraint.Term Constraint.eqt Constraint.Term_eqP.
Canonical Constraint_Term_EqType :=
  @EqType Constraint.Term Constraint_Term_Mixin.

Check (varx @ vary, Base) : Constraint.Term.
Check (varx @ vary, Base) : Constraint_Term_EqType.

Compute (varx @ vary, Base) == (varx @ vary, Base).

Definition Constraint_Terms_EqType := (seq Constraint_Term_EqType)%type.

(* Canonical Constraint_Term_predType := mkPredType Constraint.inb. *)
(* 第二引数を省くと、うまくいかない。Constraint.Terms と解釈されるため。 *)
Canonical Constraint_Term_predType :=
  @mkPredType Literal Constraint_Terms_EqType Constraint.inb.
Set Printing All.
Print Constraint_Term_predType.
Unset Printing All.

Check [:: (varx, vary)] : Constraint.Terms.
Check [:: (varx, vary)] : seq Constraint_Term_EqType.
Check [:: (varx, vary)] : Constraint_Terms_EqType.
  
Definition sc := [:: (varx, vary)] : seq Constraint_Term_EqType.
Definition sc' := [:: (varx, vary)] : Constraint.Terms.
Definition sc'' := [:: (varx, vary)] : Constraint_Terms_EqType.

Compute sc == sc''.

Compute Constraint.inb sc Literal.x.
Compute Constraint.inb sc' Literal.x.
Compute Constraint.inb sc'' Literal.x.

Compute Literal.x \in sc''.                 (* ちょっと制限がある？ *)

(* コアーション *)
(* Constraint_Terms_EqType への型推論のほうが便利なので、使わない。 *)
Coercion card_constraints (constraints : Constraint_Terms_EqType) :
  Literal -> bool := Constraint.inb constraints.

(* 変数の個数 cardinal *)
(* Literal_finType を利用している。 *)
Check #|Constraint.inb sc|.
Compute #|Constraint.inb sc|.

(* コアーションの例 *)
Check #|sc''|.
Compute #|sc''|.

Notation subst := (Constraint.subst).
Notation inb := (Constraint.inb).
Notation Size := (Constraint.Size).
Notation unifiesb := (Constraint.unifiesb).

Module Unify.

  Lemma ex_inb constraints : exists i, #|inb constraints| = i.
  Proof.
  Admitted.                                 (* XXXX *)

  (* 変数の数についての順序関係は、次のようにかける。 *)
  
  Definition lt constraints1 constraints2 :=
    forall n m,
      #|inb constraints1| = n ->
      #|inb constraints2| = m ->
      n <= m /\ (m <= n -> Size constraints1 < Size constraints2).
  
  Lemma lt_well_founded : well_founded lt.
  Proof.
    move=> constraints1.
    case: (ex_inb constraints1) => n Hcardinal1.
    move: constraints1 Hcardinal1.
    
    induction n as [n IHn] using lt_wf_ind.
    induction constraints1 as [constraints1 IHconstraints1]
                                using (induction_ltof1 _ Size).
    
    move=> Hcardinal1.
    apply: Acc_intro => constraints2 Hlt.
    case: (ex_inb constraints2) => m Hcardinal2.
    case: (Hlt m n Hcardinal2 Hcardinal1) => [Hcard Hsize].
    
    case Heq : (m == n); move/eqP in Heq.
    - apply: IHconstraints1.
      apply/ltP.                      (* coq_nat を ssrnat にする。 *)
      apply: Hsize.
      + by rewrite Heq in Hcard *.          (* gool も書き換える。 *)
      + by rewrite -Heq.
    - apply: (IHn m).
      + apply/ltP.                    (* coq_nat を ssrnat にする。 *)
        rewrite ltn_neqAle.
        apply/andP.
        split.
        * by apply/eqP.
        * done.
      + done.
  Defined.
  
  (* ****************************** *)
  (* boolean の論理式 *)
  (* ****************************** *)
  
  Definition lt' constraints1 constraints2 :=
    let: n := #|inb constraints1| in
    let: m := #|inb constraints2| in
    (n <= m) && ((m <= n) ==> (Size constraints1 < Size constraints2)).
  

  Lemma lt_well_founded' : well_founded lt'.
  Proof.
    move=> constraints1.
    case: (ex_inb constraints1) => n Hcardinal1.
    move: constraints1 Hcardinal1.
    
    induction n as [n IHn] using lt_wf_ind.
    induction constraints1 as [constraints1 IHconstraints1]
                                using (induction_ltof1 _ Size).
    
    move=> Hcardinal1.
    apply: Acc_intro => constraints2 Hlt.
    case: (ex_inb constraints2) => m Hcardinal2.
    case: Hlt => /andP [Hcard Hsize].       (* ここが異なる。 *)
    
    case Heq : (m == n); move/eqP in Heq.
    - apply: IHconstraints1.
      move/implyP in Hsize.
      apply/ltP.                      (* coq_nat を ssrnat にする。 *)
      apply: Hsize.
      + by rewrite Hcardinal1 Hcardinal2 Heq. (* subst ではいけない。 *)
      + by rewrite -Heq Hcardinal2.         (* subst ではいけない。 *)
    - apply: (IHn m).
      + apply/ltP.                    (* coq_nat を ssrnat にする。 *)
        rewrite ltn_neqAle.
        apply/andP.
        split.
        * by apply/eqP.
        * by rewrite Hcardinal1 Hcardinal2 in Hcard. (* subst でもよい。 *)
      + done.
  Defined.
  
  Lemma subsetE (s1 s2 : Constraint_Terms_EqType) :
    s1 \subset s2 = [forall x, (x \in s1) ==> (x \in s2)].
  Proof.
    rewrite subset_disjoint /disjoint.
    apply/idP/idP.
    - move/pred0P => H.
      apply/forallP => x.
      apply/implyP => Hs1.
      move: (H x) => {H} /= /eqP.
      rewrite inE eqbF_neg negb_and /=.
      move/orP => [Hn1 | Hnn2].
      + by move/negP in Hn1.
      + by rewrite Bool.negb_involutive in Hnn2.
        
    - move/forallP => H.
      apply/pred0P => x.
      move: (H x) => {H} /implyP H /=.
      apply/andP => [[H1 Hn2]].
      rewrite inE /= in Hn2.
      move/negP in Hn2.
      apply: Hn2.
        by apply: H.
  Qed.
  
  Lemma subst_subset x t constraints :
    inb (Constraint.subst x t constraints) \subset inb ((Var x, t) :: constraints).
  Proof.
    rewrite subsetE.
    apply/forallP => x'.
    apply/implyP => HIn.
    move/Constraint.subst_In_or in HIn.
    case: HIn => [HIn | HIn].
    - rewrite /mem /in_mem /inb /=.
        by apply/orP/or_introl/orP/or_intror.
    - rewrite /mem /in_mem /inb /=.
        by apply/orP/or_intror.
  Qed.

  Lemma subst_not_subset x t constraints :
    x \notin t ->
    ~~ (inb ((Var x, t) :: constraints) \subset inb (Constraint.subst x t constraints)).
  Proof.
    move=> HnotIn.
    rewrite subsetE negb_forall.
    apply/existsP.
    exists x.
    rewrite negb_imply.
    apply/andP.
    split.
    - rewrite /mem /in_mem /inb /=.
      apply/orP/or_introl/orP/or_introl.
      by rewrite /mem /in_mem /inb /=.
    - apply/negP=> Hc.
      move/Constraint.subst_In_occur in Hc.
      by move/negP in HnotIn.
  Qed.
  
  Lemma subst_proper x t constraints :
    x \notin t ->
    inb (Constraint.subst x t constraints) \proper (inb ((Var x, t) :: constraints)).
  Proof.
    move=> HnotIn.
    Check properEneq.          (* これは {set T} 用なので使えない。 *)
    Check properE.
      by rewrite properE subst_subset subst_not_subset.
  Qed.    
  
  Lemma lt_subst_1 constraints x t :
      x \notin t ->
      lt (Constraint.subst x t constraints) ((Var x, t) :: constraints).
  Proof.
    move=> HnotIn.
    rewrite /lt => m n Hcardinal1 Hcardinal2.
    
    split.
    - rewrite -Hcardinal1 -Hcardinal2.
      apply: subset_leq_card.
        by apply: subst_subset.

    Check subset_leq_card
      : forall (T : finType) (A B : pred T), A \subset B -> #|A| <= #|B|.
    Check proper_card
      : forall (T : finType) (A B : pred T), A \proper B -> #|A| < #|B|.
    
    - move: (proper_card (subst_proper x t constraints HnotIn)) => Hmn.
      rewrite Hcardinal1 Hcardinal2 in Hmn.
        by rewrite leqNgt => /negP Hn_mn.
  Qed.
  
  Lemma term_comm x t constraints :
    inb ((Var x, t) :: constraints) = inb ((t, Var x) :: constraints).
  Proof.
(*
(* =1 なら証明できる。 *)
    move=> x' /=.
    by rewrite [(x' \in Var x) || (x' \in t)]Bool.orb_comm.
  Qed.
 *)
  Admitted.                                 (* XXXX *)
  
  
  Lemma lt_subst_2 constraints x t :
      x \notin t ->
      lt (Constraint.subst x t constraints) ((t, Var x) :: constraints).
  Proof.
    move=> HnotIn.
    rewrite /lt => m n Hcardinal1 Hcardinal2.
    
    rewrite -term_comm in Hcardinal2.       (* !!! *)
    
    split.
    - rewrite -Hcardinal1 -Hcardinal2.
      apply: subset_leq_card.
        by apply: subst_subset.

    - move: (proper_card (subst_proper x t constraints HnotIn)) => Hmn.
      rewrite Hcardinal1 Hcardinal2 in Hmn.
        by rewrite leqNgt => /negP Hn_mn.
  Qed.
  
  Lemma lt_fun t11 t12 t21 t22 constraints :
    lt ((t11, t21) :: (t12, t22) :: constraints) ((t11 @ t12, t21 @ t22) :: constraints).
  Proof.
    move=> m n Hcardinal1 Hcardinal2.
    split.
    - rewrite -Hcardinal1 -Hcardinal2.
      apply: subset_leq_card.

      rewrite subsetE.
      apply/forallP => x'.
      apply/implyP.
      rewrite /mem /in_mem /inb /=.
      move/orP => [/orP [H11 | H21] | /orP [/orP [H12 | H22] | Hc]].
      + apply/orP/or_introl/orP/or_introl.
        rewrite Types.In_Fun.
          by apply/orP; left.
      + apply/orP/or_introl/orP/or_intror.
        rewrite Types.In_Fun.
          by apply/orP; left.
      + apply/orP/or_introl/orP/or_introl.
        rewrite Types.In_Fun.
          by apply/orP; right.
      + apply/orP/or_introl/orP/or_intror.
        rewrite Types.In_Fun.
          by apply/orP; right.
      + apply/orP/or_intror.
        done.

    - move=> Hnm.
      rewrite /Size /= addnA ltn_add2r addnS addSnnS ltnS addnS.
      rewrite addnACA.      (* m + (n + (p + q)) = m + p + (n + q) *)
        by rewrite leqnSn.
  Qed.
  
  Lemma lt_cons c constraints : lt constraints (c :: constraints).
  Proof.
    move: c => [t1 t2].
    move=> m n Hcardinal1 Hcardinal2.
    split.
    - rewrite -Hcardinal1 -Hcardinal2.
      apply: subset_leq_card.
      
      rewrite subsetE.
      apply/forallP => x'.
      apply/implyP.
      rewrite /mem /in_mem /inb /= => HIn.
        by apply/orP/or_intror.
        
    - move=> Hnm.
      rewrite /Size /=.
      rewrite -{1}[foldr _ _ _]add0n ltn_add2r.
      rewrite addn_gt0.
        (* (0 < Types.Size t1) || (0 < Types.Size t2) *)
        by apply/orP/or_introl/Types.size_gt0.
  Qed.
  
  Function unify constraints {wf lt constraints} :=
    match constraints with
    | nil => Some nil
    | (Types.Base, Types.Base) :: constraints' =>
      unify constraints'
    | (Types.Var x, Types.Var y) :: constraints'  =>
      if x == y then unify constraints'
      else
        option_map (cons (x, Types.Var y)) (unify (subst x (Types.Var y) constraints'))
    | (Types.Var x, t2) :: constraints' =>
      if x \in t2 then None
      else
        option_map (cons (x, t2)) (unify (subst x t2 constraints'))
    | (t1, Types.Var y) :: constraints' =>
      if y \in t1 then None
      else
        option_map (cons (y, t1)) (unify (subst y t1 constraints'))
    | (Types.Fun t11 t12, Types.Fun t21 t22) :: constraints' =>
      unify ((t11, t21) :: (t12, t22) :: constraints')
    | _ => None
    end.
  Proof.
    - move=> constraints1 t constraints2 t1 t2 Ht1 Ht2 Ht H.
        by apply: lt_cons.
      
    - move=> constraints1 t constraints2 t1 t2 Ht1 Ht2 Ht H H1 H2.
        by apply: lt_subst_2.
        
    - move=> constraints1 t constraints2 t1 t2 x Ht1 Ht2 Ht H H1.
        by apply: lt_subst_1.
        
    - move=> constraints1 t constraints2 t1 t2 x Ht1 y Ht2 Ht H H1.
        by apply: lt_cons.
        
    - move=> constraints1 t constraints2 t1 t2 x Ht1 y Ht2 Ht H H1.
      apply: lt_subst_1.
      apply: Types.neq_notIn_var.
      (* H1 : (x == y) = false を x != y にする。 *)
      move: H1 => /(introT eqP).   (* /eqP だと <> になってしまう。 *)
        by rewrite eqbF_neg.
        
    - move=> constraints1 t constraints2 t1 t2 x Ht1 t3 t4 Ht H H1 H2.
      apply: lt_subst_1.
      (* H2 : (x \in t3 @ t4) = false を x \notin t3 @ t4 にする。 *)
      move: H2 => /negP.
        by move/negP.
        
    - move=> constraints1 t constraints2 t1 t2 t3 t4 Ht1 x Ht2 Ht H H1.
      apply: lt_subst_2.
      (* H1 : (x \in t3 @ t4) = false を x \notin t3 @ t4 にする。 *)
      move: H1 => /negP.
        by move/negP.
        
    - move=> constraints1 t constraints2 t1 t2 t3 t4 Ht1 t5 t6 Ht2 Ht H1.
        by apply: lt_fun.
      
    - by apply: lt_well_founded.
  Defined.
  
  Extraction unify.
(** val unify :
    (Types.coq_Term, Types.coq_Term) prod list -> (Literal.coq_Literal, Types.coq_Term)
    prod list option **)
  
  (*
let rec unify = function
| Nil -> Some Nil
| Cons (p, constraints') ->
  let Pair (t1, t2) = p in
  (match t1 with
   | Types.Base ->
     (match t2 with
      | Types.Base -> unify constraints'
      | Types.Var y ->
        (match in_mem y (mem types_Term_predType (Obj.magic Types.Base)) with
         | True -> None
         | False ->
           option_map (fun x -> Cons ((Pair (y, Types.Base)), x))
             (Obj.magic unify (Constraint.subst y Types.Base constraints')))
      | Types.Fun (_, _) -> None)
   | Types.Var x ->
     (match t2 with
      | Types.Var y ->
        (match eq_op literal_eqType (Obj.magic x) (Obj.magic y) with
         | True -> unify constraints'
         | False ->
           option_map (fun x0 -> Cons ((Pair (x, (Types.Var y))), x0))
             (Obj.magic unify (Constraint.subst x (Types.Var y) constraints')))
      | x0 ->
        (match in_mem x (mem types_Term_predType (Obj.magic x0)) with
         | True -> None
         | False ->
           option_map (fun x1 -> Cons ((Pair (x, x0)), x1))
             (Obj.magic unify (Constraint.subst x x0 constraints'))))
   | Types.Fun (t11, t12) ->
     (match t2 with
      | Types.Base -> None
      | Types.Var y ->
        (match in_mem y (mem types_Term_predType (Obj.magic (Types.Fun (t11, t12)))) with
         | True -> None
         | False ->
           option_map (fun x -> Cons ((Pair (y, (Types.Fun (t11, t12)))), x))
             (Obj.magic unify (Constraint.subst y (Types.Fun (t11, t12)) constraints')))
      | Types.Fun (t21, t22) ->
        unify (Cons ((Pair (t11, t21)), (Cons ((Pair (t12, t22)), constraints'))))))
  *)
    
  Theorem unify_sound constraints subs :
    unify constraints = Some subs -> unifiesb subs constraints.
  Proof.
    move: subs.
    functional induction (unify constraints) => subs Hunify.
    
    (* unifiesb subs [::] *)
    - done.

    (* unifiesb subs ((Base, Base) :: constraints') *)
    - rewrite -Constraint.unify_same.
        by apply: IHo.

    (* unifiesb subs ((Var x, Var y) :: constraints') *)
    - move/eqP in e0.
      rewrite -e0.
      rewrite -Constraint.unify_same.
        by apply: IHo.
      
    (* unifiesb subs ((Var x, Var y) :: constraints') *)
    - destruct (unify (subst x (Types.Var y) constraints')).
      + case H : (x == y).
        * by rewrite H in y0.
        * inversion Hunify.
          apply: Constraint.unify_sound_subst.
          ** apply: Types.neq_notIn_var.
             move: H => /(introT eqP).   (* /eqP だと <> になってしまう。 *)
               by rewrite eqbF_neg.
          ** by apply: IHo.
      + done.                               (* Hunify が矛盾 *)
        
    - done.                                 (* Hunify が矛盾 *)
      
    (* unifiesb subs ((Var x, t2) :: constraints') *)
    - destruct (unify (subst x t2 constraints')).
      + case H : (x \in t2).
        * by rewrite H in y0.
        * inversion Hunify.
          apply: Constraint.unify_sound_subst.
          ** apply/negP.
             by move: H => /negP.
          ** by apply: IHo.
      + done.                               (* Hunify が矛盾 *)
        
    - done.                                 (* Hunify が矛盾 *)
      
    - rewrite Constraint.unify_comm.
      destruct (unify (subst y t1 constraints')).
      + case H : (y \in t1).
        * by rewrite H in y1.
        * inversion Hunify.
          apply: Constraint.unify_sound_subst.
          ** apply/negP.
             by move: H => /negP.
          ** by apply: IHo.
      + done.                               (* Hunify が矛盾 *)
        
    (* unifiesb subs ((t11 @ t12, t21 @ t22) :: constraints') *)
    - rewrite -Constraint.unify_fun.
        by apply: IHo.

    - done.                                 (* Hunify が矛盾 *)
  Qed.

  Notation moregen subs subs' :=
    (exists subs0, forall t,
          Types.subst_list subs' t = Types.subst_list subs0 (Types.subst_list subs t)).

  Lemma moregen_extend subs x t subs' :
    Types.unifies subs (Var x) t ->
    moregen subs' subs ->
    moregen ((x, t) :: subs') subs.
  Proof.
    move=> Hunifies Hmoregen.
    case: Hmoregen => [subs0 Hmoregen'].
    exists subs0.
    move=> t1 /=.
      by rewrite -Hmoregen' -Types.subst_preserves_unifies.
  Qed.
  
  Lemma unify_complete_subst x t subs constraints :
    (* x \notin t ->  これなくても、成立する。 *)
    (forall subs,
        unifiesb subs (subst x t constraints) ->
        exists subs', unify (subst x t constraints) = Some subs' /\ moregen subs' subs) ->
    unifiesb subs ((Types.Var x, t) :: constraints) ->
    (exists subs',
        option_map (cons (x, t)) (unify (subst x t constraints)) =
        Some subs' /\ moregen subs' subs).
  Proof.
    move=> IH Hunifies.
    inversion Hunifies as [H].
    move: H => /andP [[/eqP Hu] Hunifies'].
    move/(Constraint.subst_preserves_unifiesb _ _ _ _ Hu) in Hunifies'.
    case: (IH _ Hunifies') => [subs' [Heq Hmoregen]].
    rewrite Heq.
    exists ((x, t) :: subs').
    split.
    - done.
    - by apply: moregen_extend.
  Qed.
  
  Theorem unify_complete constraints subs :
    unifiesb subs constraints ->
    exists subs', unify constraints = Some subs' /\ moregen subs' subs.
  Proof.
    move: subs.
    functional induction (unify constraints) => subs Hunifies.
    
    - exists nil.
      split.
      + done.
      + exists subs.
        done.
        
    - rewrite -Constraint.unify_same in Hunifies.
        by apply: IHo.

    - move/eqP in e0.
      subst.
      rewrite -Constraint.unify_same in Hunifies.
        by apply: IHo.

    - apply: unify_complete_subst.
      + inversion Hunifies as [H].
        move: H.
        move=> /andP [[/eqP Hunifies'] H].
        case Hxy : (x == y).
        * by rewrite Hxy in y0.
        * move: Hxy => /(introT eqP).  (* /eqP だと <> になってしまう。 *)
            by rewrite eqbF_neg.
      + done.
        
    - inversion Hunifies as [H].
      move: H.
      move=> /andP [[/eqP Hunifies'] H].
      exfalso.
      
      apply Types.unifies_occur with (x:=x) (t:=t2) (subs:=subs).
      (* 最後の分岐で、eタクティクを使わなくてすむように、 *)
      (* 結論の forall に値subsを与えるために、with を使う。 *)
      + by case: t2 y e0 Hunifies Hunifies'.
      + done.
      + done.
        
    - apply: unify_complete_subst.
      + case Hxy : (x \in t2).
        * by rewrite Hxy in y0.
        * done.
      + done.
        
    - inversion Hunifies as [H].
      move: H.
      move=> /andP [[/eqP Hunifies'] H].
      exfalso.
      apply Types.unifies_occur with (x:=y) (t:=t1) (subs:=subs).
      (* 最後の分岐で、eタクティクを使わなくてすむように、 *)
      (* rewriteで書き換えられるよう、結論の forall に値subsを与えるために、with を使う。 *)
      + by case: t1 y0 e0 Hunifies Hunifies'.
      + done.
      + done.
        
    - rewrite Constraint.unify_comm in Hunifies.
      apply: unify_complete_subst.
      + case Hxy : (y \in t1).
        * by rewrite Hxy in y1.
        * done.
      + done.
        
    - rewrite -Constraint.unify_fun in Hunifies.
        by apply: IHo.
        
    - case: constraints y Hunifies => //= [[t1 t2]] constraints y H.
      case: t1 y H; case: t2 => //= t1 t2 y H.
      * move: H => /andP [[/eqP Hcontra] Hunifies'].
        rewrite Types.subst_list_Fun in Hcontra.
        rewrite Types.subst_list_Base in Hcontra.
        done.
      * move: H => /andP [[/eqP Hcontra] Hunifies'].
        rewrite Types.subst_list_Fun in Hcontra.
        rewrite Types.subst_list_Base in Hcontra.
        done.
  Qed.
  
  Definition unify' constraints :
    { subs | unifiesb subs constraints } + { ~exists subs, unifiesb subs constraints }.
  Proof.
    case Heqo : (unify constraints) => [subs |].
    
    - left.
      exists subs.
        by rewrite unify_sound.
        
    - right.
      case=> [subst].
      move/unify_complete.
      case=> [subs' [Hcontra]].
        by rewrite Hcontra in Heqo.
  Defined.
  
  Extraction unify'.
(** val unify' :
    Constraint.coq_Term list -> (Literal.coq_Literal, Types.coq_Term) prod list sumor **)

  (* 
let unify' constraints =
  let o = unify (Obj.magic constraints) in
  (match o with
   | Some subs -> Inleft subs
   | None -> Inright)
   *)
  
End Unify.


(* END *)

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
