From mathcomp Require Import all_ssreflect.
Require Import Finite_sets_facts.

(* List.v にある定義 *)

Inductive Forall {A : Type} (P : A -> Prop) : seq A -> Prop :=
| Forall_nil : Forall P nil
| Forall_cons : forall (x : A) (s : seq A), P x -> Forall P s -> Forall P (x :: s).

Inductive Exists {A : Type} (P : A -> Prop) : seq A -> Prop :=
| Exists_cons_hd : forall (x : A) (s : seq A), P x -> Exists P (x :: s)
| Exists_cons_tl : forall (x : A) (s : seq A), Exists P s -> Exists P (x :: s).

(* List.In の定義のbool版 など *)
(*
List.In = 
fun A : Type =>
fix In (a : A) (l : seq A) {struct l} : Prop :=
  match l with
  | [::] => False
  | b :: m => b = a \/ In a m
  end
     : forall A : Type, A -> seq A -> Prop
 *)

Lemma In_inb {A : eqType} (x : A) (s : seq A) : List.In x s <-> x \in s.
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

Lemma InP {A : eqType} (x : A) (s : seq A) : reflect (List.In x s) (x \in s).
Proof.
  apply: (iffP idP) => H.
    - by apply/In_inb.
    - by apply/In_inb.
Qed.

(* List.v にある補題 *)

Lemma Forall_forall (A : Type) (P : A -> Prop) (s : seq A) :
  Forall P s <-> (forall x : A, List.In x s -> P x).
Proof.
  split.
  - elim.
    + move=> x H.
        by inversion H.
    + move=> // x s' HP H1 IHs y.
      case=> H3.
      * by rewrite -H3.
      * by apply: IHs.
  - elim: s => [| a s IHs] H.
    + by apply: Forall_nil.
    + apply: Forall_cons.
      * apply: H => /=.
          by left.
      * apply: IHs => x H1 /=.
        apply: H => /=.
          by right.
Qed.

Lemma Exists_exists (A : Type) (P : A -> Prop) (s : seq A) :
  Exists P s <-> (exists x : A, List.In x s /\ P x).
Proof.
  split.
  - induction 1; firstorder.
  - induction s; firstorder; subst; auto.
    + by apply: Exists_cons_hd.
    + apply: Exists_cons_tl.
      apply: (H1 x).
      by split.
Qed.

Lemma in_map (A B : Type) (f : A -> B) (s : seq A) (x : A) :
  List.In x s -> List.In (f x) (map f s).
Proof.
    by induction s; firstorder (subst; auto).
Qed.

Lemma in_map_iff (A B : Type) (f : A -> B) (s : list A) (y : B) :
  List.In y (map f s) <-> (exists x : A, f x = y /\ List.In x s).
Proof.
    by induction s; firstorder (subst; auto).
Qed.

Lemma Forall_impl {A : Type} (P Q : A -> Prop) :
  (forall a, P a -> Q a) -> forall s, Forall P s -> Forall Q s.
Proof.
  move=> H s.
  rewrite !Forall_forall.
    by firstorder.
Qed.

Lemma map_id {A :Type} (s : seq A) : map (fun x => x) s = s.
Proof.
  induction s; simpl; auto; rewrite IHs; auto.
Qed.

Lemma map_map {A B C : Type} (f : A -> B) (g : B -> C) s :
  map g (map f s) = map (fun x => g (f x)) s.
Proof.
  induction s; simpl; auto.
  rewrite IHs; auto.
Qed.

Lemma map_ext_in {A B : Type} (f g : A -> B) s :
  (forall a, List.In a s -> f a = g a) -> map f s = map g s.
Proof.
  induction s; simpl; auto.
  intros; erewrite H by intuition; rewrite IHs; auto.
Qed.

Lemma map_ext {A B : Type} (f g : A -> B) :
  (forall a, f a = g a) -> forall s, map f s = map g s.
Proof.
  intros; apply map_ext_in; auto.
Qed.

(* List.v にある補題。ここまで *)

Lemma Forall_map X Y (P : Y -> Prop) (f : X -> Y) l :
  Forall P (map f l) <-> Forall (fun x => P (f x)) l.
Proof.
  split=> H.
  - apply/Forall_forall => x HListIn.
    move/Forall_forall in H.
    + apply: H.
      by apply: in_map.
    + induction l as [| x l'];
      inversion H;
      constructor;
      by auto.
Qed.

Lemma Exists_map X Y (P : Y -> Prop) (f : X -> Y) s :
  Exists P (map f s) <-> Exists (fun x => P (f x)) s.
Proof.
  split=> HExists.
  - move/Exists_exists in HExists.
    apply Exists_exists.
    destruct HExists as [x [HListIn HP]].
    apply in_map_iff in HListIn.
    destruct HListIn as [y [Heq HListIn]].
    exists y.
    subst; auto.

  - move/Exists_exists in HExists.
    apply Exists_exists.
    destruct HExists as [x [HListIn HP]].
    exists (f x).
    split; auto.
    apply in_map; auto.
Qed.

Lemma Exists_preserves_Finite U family :
  Forall (Finite _) family ->
  Finite _ (fun x : U => Exists (fun s => s x) family).
Proof.
  intros Hall.
  induction family as [| s family'].
  - rewrite (Extensionality_Ensembles U
             (fun x : U => Exists (@^~ x) [::]) (Empty_set _)).
    by constructor.
  - by split; intros x H; inversion H.
  - inversion Hall.
    rewrite (Extensionality_Ensembles U
             (fun x0 : U => Exists (@^~ x0) (s :: family'))
             (Union _ s (fun x : U => Exists (fun s => s x) family'))).
      apply Union_preserves_Finite; auto.
      split;
        intros y HIn;
        (inversion HIn; [ left | right ]);
        auto.
Qed.

Lemma Exists_app X (P : X -> Prop) l1 l2 :
  Exists P (l1 ++ l2) -> Exists P l1 \/ Exists P l2.
Proof.
  intros Hexists.
  induction l1.
  - auto.
  - inversion Hexists.
    + left. left. auto.
    + assert (IHl1':  Exists P l1 \/ Exists P l2).
      * apply IHl1.
        auto.
      * destruct IHl1' as [IHl1' | IHl1'].
        left. right. auto.
        right. auto.
Qed.

Lemma Forall_app X (P : X -> Prop) l1 l2 :
  Forall P (l1 ++ l2) -> Forall P l1 /\ Forall P l2.
Proof.
  intros HForall.
  induction l1.
  - split; auto.
    by apply: Forall_nil.
  - inversion HForall.
    specialize (IHl1 H2).
    destruct IHl1.
    split.
      constructor; auto.
      auto.
Qed.

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
  
  Lemma InP (x : nat) (t : Term) : reflect (In x t) (inb t x).
  Proof.
    apply: (iffP idP) => H.
    - by apply/In_inb.
    - by apply/In_inb.
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
  
  Theorem FV_Finite t : Finite nat (In ^~ t). (* fun x => In x t *)
  Proof.
    elim: t => [| x | t1 IHt1 t2 IHt2 ].
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
  
  Definition unifies subs t1 t2 := subst_list subs t1 = subst_list subs t2.
  
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
      rewrite /unifies.
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
    elim: Hoccur Hneq H => [t1 t2 HIn IHHoccur | t1 t2 HIn IHHoccur |] Hneq H.
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

Notation "x @ y" := (Types.Fun x y) (at level 50, left associativity).
Notation Var x := (Types.Var x).
Notation Base := (Types.Base).

Definition Types_Term_Mixin := @EqMixin Types.Term Types.eqt Types.Term_eqP.
Canonical Types_Term_EqType := @EqType Types.Term Types_Term_Mixin.
  
Compute (Var 1) @ (Var 2) @ Base == (Var 1) @ (Var 2) @ Base.
Compute (Var 1) @ Base @ (Var 2) == (Var 1) @ (Var 2) @ Base.

Canonical Types_Term_predType := @mkPredType nat Types.Term Types.inb.
  
Compute 1 \in (Var 1) @ (Var 2) @ Base.
Compute 3 \notin (Var 1) @ (Var 2) @ Base.

Module Constraint.
  Definition Term := (Types_Term_EqType * Types_Term_EqType)%type.
  Definition Terms := (seq Term)%type.

  Fixpoint eqt (t1 t2 : Term) : bool :=
    (t1.1 == t2.1) && (t1.2 == t2.2).
  
  Lemma Term_eqP : forall (t1 t2 : Term), reflect (t1 = t2) (eqt t1 t2).
  Proof.
    move=> t1 t2.
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
    Exists (fun c : Term => Types.In x c.1 \/ Types.In x c.2)
           constraints.
  
  Definition inb (s : Terms) (x : nat) : bool :=
    has
      (fun c : Term => (x \in c.1) || (x \in c.2))
      s.
  
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
        * apply: Exists_cons_hd.
          move/orP in H.
          case: H => H.
          ** by apply/or_introl/Types.In_inb. (* left *)
          ** by apply/or_intror/Types.In_inb. (* right *)
        * apply: Exists_cons_tl.
            by move/IHs in H.
  Qed.
  
  Lemma InP (x : nat) (s : Terms) : reflect (In x s) (inb s x).
  Proof.
    apply: (iffP idP) => H.
    - by apply/In_inb.
    - by apply/In_inb.
  Qed.
  
  Definition Constraint_Term_Mixin :=
    @EqMixin Constraint.Term Constraint.eqt Term_eqP.
  Canonical Constraint_Term_EqType :=
    @EqType Constraint.Term Constraint_Term_Mixin.

  Check (Var 1 @ Var 2, Base) : Constraint.Term.
  Check (Var 1 @ Var 2, Base) : Constraint_Term_EqType.
  
  Compute (Var 1 @ Var 2, Base) == (Var 1 @ Var 2, Base).

  Definition Constraint_Terms_EqType := (seq Constraint_Term_EqType)%type.
  
  Canonical Constraint_Term_predType :=
    @mkPredType nat (Constraint_Terms_EqType) Constraint.inb.

  Check [:: (Var 1, Var 2)] : Constraint.Terms.
  Check [:: (Var 1, Var 2)] : seq Constraint_Term_EqType.
  Check [:: (Var 1, Var 2)] : Constraint_Terms_EqType.
  
  Definition sc := [:: (Var 1, Var 2)] : seq Constraint_Term_EqType.
  Definition sc' := [:: (Var 1, Var 2)] : Constraint.Terms.
  Definition sc'' := [:: (Var 1, Var 2)] : Constraint_Terms_EqType.
  
  Compute sc == sc''.
  Compute Constraint.inb sc'' 1.
  Compute 1 \in sc''.
  
  (* fun x => In x constraints *)
  Lemma FV_Finite constraints : Finite nat (In ^~ constraints).
  Proof.
    rewrite /In.
    rewrite (Extensionality_Ensembles nat
            (fun x : nat =>
               Exists (fun c : Term => Types.In x c.1 \/ Types.In x c.2) constraints)
            (fun x => Exists (fun s => s x)
                             (map (fun c : Term => Union _ (fun x => Types.In x c.1)
                                                         (fun x => Types.In x c.2))
                                  constraints))).
    - apply: Exists_preserves_Finite.
      apply/Forall_map.
      apply/Forall_forall.
      move=> [t1 t2] HIn.
      apply: Union_preserves_Finite.
      + by apply: Types.FV_Finite.
      + by apply: Types.FV_Finite.
        
    - split=> x HIn.
      + apply Exists_map.
        apply Exists_exists in HIn.
        apply Exists_exists.
        case: HIn => [[t1 t2] [HListIn HIn]]; exists (t1, t2).
        split.
        * done.
        * by case HIn; [left | right]; auto.
          
      + apply Exists_map in HIn.
        apply Exists_exists in HIn.
        apply Exists_exists.
        case: HIn => [[t1 t2] [HListIn HIn]]; exists (t1, t2).
        split.
        * done.
        * by case HIn; [left | right]; auto.
  Qed.
  
  (* \in の右に書けるように EqType を返すようにする。 *)
  (* [x := t0](constraints) *)
  Definition subst x t0 constraints : Constraint_Terms_EqType :=
    map (fun c : Term => (Types.subst x t0 c.1, Types.subst x t0 c.2))
        constraints.
  
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
  
  Theorem subst_In_or x y t0 (constraints : Constraint_Terms_EqType) :
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
  
  Definition subst_list subs constraints :=
    map (fun p : Term => (Types.subst_list subs p.1, Types.subst_list subs p.2))
        constraints.
  
  Lemma subst_list_app subs1 subs2 constraints :
    subst_list (subs1 ++ subs2) constraints =
    subst_list subs2 (subst_list subs1 constraints).
  Proof.
    rewrite /subst_list map_map.
    apply: map_ext => [[t1 t2]].
    f_equal.
    - by apply: Types.subst_list_app.
    - by apply: Types.subst_list_app.
  Qed.
  
  Definition unifies subs constraints :=
    Forall (fun p : Term => Types.unifies subs p.1 p.2) constraints.
  
  Theorem subst_preserves_unifies'' x t0 subs constraints :
    Types.unifies subs (Types.Var x) t0 ->
    unifies subs constraints ->
    unifies subs (subst x t0 constraints).
  Proof.
    rewrite /subst.
    move=> Hunifies Hunifies'.
    apply/Forall_map.
    apply: (Forall_impl (fun a => Types.unifies subs a.1 a.2)).
    - move=> [t1 t2] Hunifies'' /=.
      rewrite /Types.unifies.
      rewrite -!(Types.subst_preserves_unifies _ _ _ _ Hunifies).
      done.
    - by apply Hunifies'.
  Qed.
  
End Constraint.

(* END *)
