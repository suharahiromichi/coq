(* Constraint.In を \in 中置記法でかけるようにする。 *)
(* データ構造の部分のみ。 *)
(* 2019_03_31 @suharahiromichi *)
(* 変数をリテラルにする。 *)
(* 2019_04_07 @suharahiromichi *)

From mathcomp Require Import all_ssreflect.
Require Import Finite_sets_facts.

Module List.
  
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

Notation Literal := Literal.Literal.        (* XXXXX *)

Module Types.

  Reserved Notation "x '@' y" (at level 50, left associativity).
  Inductive Term : Set :=
  | Base
  | Var of Literal
  | Fun of Term & Term.
  Notation "x @ y" := (Fun x y).

  Notation varx := (Var (Literal.x)).
  Notation vary := (Var (Literal.y)).
  Notation varz := (Var (Literal.z)).
  
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

Compute Types.inb (varx @ vary @ Base) Literal.x.
Compute Literal.x \in varx @ vary @ Base.
Compute Literal.y \notin varx @ vary @ Base.

(* 変数の個数 cardinal *)
(* Literal_finType を利用している。 *)
Check #| Types.inb (varx @ vary @ Base) |.
Compute #| Types.inb (varx @ vary @ Base) |.

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

  Definition In (x : Literal) (constraints : Terms) : Prop :=
    List.Exists (fun c : Term =>
                   let: (t1, t2) := (c.1, c.2) in Types.In x t1 \/ Types.In x t2)
                constraints.

  Definition inb (s : Terms) (x : Literal) : bool :=
    has
      (fun c : Term =>
         let: (t1, t2) := (c.1, c.2) in Types.inb t1 x || Types.inb t2 x)
      s.
  
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

(* 変数の個数 cardinal *)
(* Literal_finType を利用している。 *)
Check #| Constraint.inb sc |.
Compute #| Constraint.inb sc |.

Notation inb := (Constraint.inb).

Module Unify.

  Lemma Base0 : #|Base| = 0.
  Proof. by rewrite card0. Qed.
  
  Lemma Var1 (x : Literal) : #|Var x| = 1.
  Proof. by rewrite card1. Qed.

  Lemma Funs (x y : Term) : #|x @ y| <= #|x| + #|y|.
  Proof.
  Admitted.
  
  Lemma nil0 : #|inb [::]| = 0.
  Proof.
(*  rewrite /inb /Types.inb /=. *)
    by rewrite card0.
  Qed.
  
  Definition test_le constraints1 constraints2 :=
    #|inb constraints1| <= #|inb constraints2|.
  
End Unify.

(* END *)
