(* Constraint.In を \in 中置記法でかけるようにする。 *)
(* データ構造の部分のみ。 *)
(* 2019_03_31 @suharahiromichi *)

From mathcomp Require Import all_ssreflect.
Require Import Finite_sets_facts.

Module List.

  Inductive Forall {A : Type} (P : A -> Prop) : seq A -> Prop :=
  | Forall_nil : Forall P nil
  | Forall_cons : forall (x : A) (s : seq A), P x -> Forall P s -> Forall P (x :: s).
  
  Inductive Exists {A : Type} (P : A -> Prop) : seq A -> Prop :=
  | Exists_cons_hd : forall (x : A) (s : seq A), P x -> Exists P (x :: s)
  | Exists_cons_tl : forall (x : A) (s : seq A), Exists P s -> Exists P (x :: s).
  
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
        * move/eqP => ->.
          by left.
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
End List.

(* Test *)
Check [:: 1; 2] == [:: 1; 2].
Check 1 \in [:: 1].
Check List.InP.
Goal [:: 1; 2] == [:: 1; 2]. Proof. apply/eqP. done. Qed.
Goal 1 \in [:: 1; 2]. Proof. apply/List.InP. left. done. Qed.

Module Types.

  Reserved Notation "x '@' y" (at level 50, left associativity).
  Inductive Term : Set :=
  | Base
  | Var of nat
  | Fun of Term & Term.
  Notation "x @ y" := (Fun x y).
  
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

  Definition In (x : nat) (constraints : Terms) : Prop :=
    List.Exists (fun c : Term =>
                   let: (t1, t2) := (c.1, c.2) in Types.In x t1 \/ Types.In x t2)
                constraints.

  Definition inb (s : Terms) (x : nat) : bool :=
    has
      (fun c : Term =>
         let: (t1, t2) := (c.1, c.2) in Types.inb t1 x || Types.inb t2 x)
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

End Constraint.

Definition Constraint_Term_Mixin :=
  @EqMixin Constraint.Term Constraint.eqt Constraint.Term_eqP.
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

(* END *)

Check @set0.
Variable nf : nat_finType.
Variable s : {set nat_finType}.

Inductive Finite (U : {set: nat}) : Prop :=
| Emptt_is_finite : Finite set0
| Union_is_finite : Finite U ->  forall n, n \notin sc -> Finite 


  Print Ensemble.

  (* 
  Ensemble = fun U : Type => U -> Prop
   *)
  Print Finite.
  (* 
  Inductive Finite (U : Type) : Ensemble U -> Prop :=
    Empty_is_finite : Finite U (Empty_set U)
  | Union_is_finite : forall A : Ensemble U,
                      Finite U A ->
                      forall x : U, ~ Ensembles.In U A x -> Finite U (Add U A x)
   *)
  Print Empty_set.
  (*
  Inductive Empty_set (U : Type) : Ensemble U :=  
   *)
