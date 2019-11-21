
From mathcomp Require Import all_ssreflect.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.


Inductive append : seq nat -> seq nat -> seq nat -> Prop :=
| app_nil (b : seq nat) : append [::] b b
| app_cons (n : nat) (a b c : seq nat) : append a b c -> append (n :: a) b (n :: c)
.

Fixpoint app (a b : seq nat) : seq nat :=
  match a with
  | [::] => b
  | n :: a => n :: app a b
  end.

Lemma test : forall (a b c : seq nat), append a b c <-> app  a b = c.
Proof.
  split.
  - elim=> b'' //= a' b' c' H IH.
      by rewrite IH.
  - elim: a b c => //=.
    + move=> b c ->.
        by apply: app_nil.
    + move=> n' a' IH b' c' <-.
      apply: app_cons.
        by apply: IH.
Qed.



Inductive reverse : seq nat -> seq nat -> Prop :=
| rev_nil : reverse [::] [::]
| rev_cons (n : nat) (a b c : seq nat) :
    reverse a b -> append b [:: n] c -> reverse (n :: a) c
.

Fixpoint rev (a : seq nat) : seq nat :=
  match a with
  | [::] => [::]
  | n :: a => app (rev a) [:: n]
  end.

Goal forall (a b : seq nat), reverse a b <-> rev a = b.
Proof.
  split.
  - elim=> //= n a' b' c' H1 H2 H3.
    apply/test.
      by rewrite H2.
  - elim: a b.
    + move=> b' <- /=.
      by apply: rev_nil.
    + move=> n a IH c H.
      simpl in H.
      apply: rev_cons.
      * by apply: IH.
      * by apply/test.
Qed.


Inductive reverse2 : seq nat -> seq nat -> seq nat -> Prop :=
| rev2_nil (b : seq nat) : reverse2 [::] b b
| rev2_cons (n : nat) (a b c : seq nat) :
    reverse2 a (n :: b) c -> reverse2 (n :: a) b c
.

Goal reverse2 [:: 1;2;3] [::] [:: 3;2;1].
Proof.
  apply: rev2_cons.
  apply: rev2_cons.
  apply: rev2_cons.
  apply: rev2_nil.
Qed.

Fixpoint rev2 (a b : seq nat) : seq nat :=
  match a with
  | [::] => b
  | n :: a => rev2 a (n :: b)
  end.

Compute rev2 [:: 1;2;3] [::].               (* [:: 3;2;1] *)

Lemma test2 : forall (a b c : seq nat), reverse2 a b c <-> rev2 a b = c.
Proof.
  split.
  - by elim=> //=.
  - elim: a b c.
    + move=> b c.
      rewrite /rev2 => <-.
        by apply: rev2_nil.
    + move=> n a IH b c H.
      apply: rev2_cons.
      by apply: IH.
Qed.


Require Import Program.

Program Fixpoint rev2' (a b : seq nat) : {c : seq nat | reverse2 a b c} :=
  match a with
  | [::] => b
  | n :: a => rev2' a (n :: b)
  end.
Next Obligation.
Proof.
    by apply: rev2_nil.
Defined.
Next Obligation.
Proof.
    by apply: rev2_cons.
Defined.

Print rev2'.

Compute proj1_sig (rev2' [:: 1;2;3] [::]).  (* [:: 3;2;1] *)

Section Vector.

  Variable A : Set.

  Inductive vector : nat -> Set :=
  | Vnil : vector 0
  | Vcons : forall n, A -> vector n -> vector n.+1.
  
End Vector.

Check Vnil nat : vector nat 0.
Check Vcons 100 (Vnil nat).

Inductive vappend : forall (n m : nat),
    vector nat n -> vector nat m -> vector nat (n + m) -> Prop :=
| vapp_nil : forall (n : nat) (b : vector nat n), vappend (Vnil nat) b b
| vapp_cons : forall (h : nat) (n m : nat)
                     (a : vector nat n) (b : vector nat m) (c : vector nat (n + m)),
    vappend a b c -> vappend (Vcons h a) b (Vcons h c).
Hint Constructors vappend.

Definition data1 := Vcons 1 (Vcons 2 (Vnil nat)).
Definition data2 := Vcons 3 (Vcons 4 (Vnil nat)).
Definition data12 := Vcons 1 (Vcons 2 (Vcons 3 (Vcons 4 (Vnil nat)))).

Goal vappend data1 data2 data12.
Proof.
  apply: vapp_cons.
  apply: vapp_cons.
  apply: vapp_nil.
Qed.

Fixpoint vapp (n m : nat) (a : vector nat n) (b : vector nat m) : vector nat (n + m) :=
  match a with
  | Vnil => b
  | Vcons n h t => Vcons h (vapp t b)
  end.

Compute vapp data1 data2. (* = Vcons 1 (Vcons 2 (Vcons 3 (Vcons 4 (Vnil nat)))) *)

Goal forall (n m : nat) (a : vector nat n) (b : vector nat m) (c : vector nat (n + m)),
    vappend a b c <-> vapp a b = c.
Proof.
  move=> n m a b c.
  split.
  - elim=> //=.
    move=> h n' m' a' b' c' H1 H2.
      by subst.
  - elim: a b c => //=.
    + move=> b c H.
      subst.
      by apply: vapp_nil.
    + move=> n' m' a IHa b c H.
      subst.
      apply: vapp_cons.
      by apply: IHa.
Qed.

Program Fixpoint vapp' (n m : nat)
        (a : vector nat n) (b : vector nat m) : {c | vappend a b c} :=
  match a with
  | Vnil => b
  | Vcons n h t => Vcons h (vapp' t b)
  end.

Compute vapp data1 data2.
Compute proj1_sig (vapp' data1 data2).
(* (* = Vcons 1 (Vcons 2 (Vcons 3 (Vcons 4 (Vnil nat)))) *) *)


Fail Inductive vreverse : forall (n m : nat),
    vector nat n -> vector nat m -> vector nat (n + m) -> Prop :=
| vrev_nil : forall (n : nat) (b : vector nat n), vreverse (Vnil nat) b b
| vrev_cons : forall (h : nat) (n m : nat)
                     (a : vector nat n) (b : vector nat m) (c : vector nat (n + m).+1),
    vreverse a (Vcons h b) c -> vreverse (Vcons h a) b c.
Fail Hint Constructors vreverse.


Fail Inductive vreverse : forall (n : nat), vector nat n -> vector nat n -> Prop :=
| vrev_nil : vreverse (Vnil nat) (Vnil nat)
| vrev_cons (h : nat) (n : nat) (a b : vector nat n) (c : vector nat n.+1) :
  vreverse a b -> vappend b (Vcons h (Vnil nat)) c -> vreverse (Vcons h a) c.

Fail Fixpoint vrev (n : nat) (a : vector nat n) : vector nat n :=
  match a with
  | Vnil => Vnil nat
  | Vcons n h t => vapp (vrev a) (Vcons h (Vnil nat))
  end.

Program Fixpoint vrev (n m : nat) (a : vector nat n) (b : vector nat m)
  : (vector nat (n + m)) :=
  match a with
  | Vnil => b
  | Vcons n h t => vrev t (Vcons h b)
  end.
Next Obligation.
Proof.
  by rewrite addSnnS.
Qed.

(* END *)
