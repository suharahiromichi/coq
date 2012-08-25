(** ソフトウエアの基礎 Benjamin C. Pierceさん他、梅村さん他訳
   Prop_J: 命題と根拠からの抜粋
   「Inductive xx : xxx -> Prop := xxxx.」の定義の例
   練習問題の回答が含まれていても、正解ではないかもしれない。
   @suharahiromichi *)

(** ev *)
Inductive ev : nat -> Prop :=
| ev_0 : ev O
| ev_SS : forall n : nat, ev n -> ev (S (S n)).

(** MyProp *)
Inductive MyProp : nat -> Prop :=
| MyProp1 : MyProp 4
| MyProp2 : forall n : nat, MyProp n -> MyProp (4 + n)
| MyProp3 : forall n : nat, MyProp (2 + n) -> MyProp n.

Theorem ev_plus4 : forall n,
  ev n -> ev (4 + n).
Proof.
  intros.
  simpl.
  apply ev_SS.                              (* Goal : ev SSSSn *)
  apply ev_SS.                              (* Goal : ev SSn *)
  apply H.                                  (* Goal : n *)
Qed.

Theorem SSev_even : forall n,
  ev (S (S n)) -> ev n.
Proof.
  intros n E.
  inversion E as [| n' E'].
  apply E'.
Qed.

Theorem ev_MyProp : forall n : nat,
  MyProp n -> ev n.
Proof.
  intros n H.
  induction H as [| n' E1 | n' E2].
  (* MyProp 4 -> ev 4 *)
  apply ev_SS.
  apply ev_SS.
  apply ev_0.
  (* MyProp (4 + n) -> ev (4 + n) *)
  apply ev_plus4.
  apply IHE1.
  (* MyProp n' -> ev n' *)
  apply SSev_even.
  apply IHE2.
Qed.

Theorem MyProp_0 : MyProp 0.
Proof.
  SearchAbout MyProp.
  apply MyProp3.
  simpl.                                    (* Goal : MyProp 2 *)
  apply MyProp3.
  simpl.                                    (* Goal : MyProp 4 *)
  apply MyProp1.
Qed.

Theorem MyProp_plustwo : forall n : nat,
  MyProp n -> MyProp (S (S n)).
Proof.
  intros n H.
  inversion H.
  (* Goal : MyProp 6 *)
  apply (MyProp2 2).
  apply (MyProp3 2).
  apply MyProp1.
  
  (* Goal : MyProp SS(4 + n0) *)
  simpl.                (* Goal : MyProp (S (S (S (S (S (S n0)))))) *)
  apply (MyProp2 (S (S n0))).   (* -4する。 *)
  simpl.                        (* Goal : MyProp (S (S n0)) *)
  apply (MyProp3 (S (S n0))).   (* +2する。 *)
  simpl.                        (* Goal : MyProp (S (S (S (S n0)))) *)
  apply (MyProp2 n0).           (* -4する。 *)
  simpl.                        (* Goal : MyProp n0 *)
  apply H0.
  (* MyProp (S (S n)) *)
  apply H0.
Qed.

Theorem MyProp_ev : forall n : nat,
  ev n -> MyProp n.
Proof.
  intros n E.
  induction E as [| n' E'].
  (* Case "E = ev_0". *)
  apply MyProp_0.
  (* Case "E = ev_SS n' E'". *)
  apply MyProp_plustwo.
  apply IHE'.
Qed.

(** p *)
Inductive tree (X:Type) : Type :=
| leaf : X -> tree X
| node : tree X -> tree X -> tree X.

Inductive p : (tree nat) -> nat -> Prop :=
| c1 : forall n, p (leaf _ n) 1
| c2 : forall t1 t2 n1 n2,
  p t1 n1 -> p t2 n2 -> p (node _ t1 t2) (n1 + n2)
| c3 : forall t n, p t n -> p t (S n).

(* list *)
Inductive list (X:Type) : Type :=
| nil : list X
| cons : X -> list X -> list X.

Implicit Arguments nil [[X]].
Implicit Arguments cons [[X]].
Notation "x :: l" := (cons x l) (at level 60, right associativity).
Notation "[ ]" := nil.
Notation "[ x , .. , y ]" := (cons x .. (cons y nil) ..).
Notation "x ++ y" := (app x y)
  (at level 60, right associativity).

Fixpoint length {X : Type} (l : list X) : nat :=
  match l with
    | nil      => 0
    | cons h t => S (length t)
  end.

Fixpoint app {X : Type} (l1 l2 : list X) : (list X) :=
  match l1 with
    | nil      => l2
    | cons h t => cons h (app t l2)
  end.

Lemma app_ass : forall (X : Type) (l1 l2 l3 : list X),
  app (app l1 l2) l3 = app l1 (app l2 l3).
Proof.
  intros X l1 l2 l3.
  induction l1 as [ | n l1'].
  simpl.
  reflexivity.
  
  simpl.
  rewrite <- IHl1'.
  reflexivity.
Qed.

Fixpoint snoc {X : Type} (l : list X) (v : X) : (list X) :=
  match l with
    | nil      => cons v []
    | cons h t => cons h (snoc t v)
  end.

Lemma snoc_append : forall (X : Type) (l : list X) (x : X),
  snoc l x = app l [x].
Proof.
  intros X l x.
  induction l.
  simpl.
  reflexivity.
  
  simpl.
  rewrite IHl.  
  reflexivity.
Qed.

Lemma snoc_with_append : forall X : Type,
  forall l1 l2 : list X, forall v : X,
    snoc (app l1 l2) v = app l1 (snoc l2 v).
Proof.
  intros X l1 l2 x.
  rewrite snoc_append.
  rewrite snoc_append.
Admitted.

Fixpoint rev {X : Type} (l : list X) : list X :=
  match l with
    | nil      => []
    | cons h t => snoc (rev t) h
  end.

(** pal *)
Inductive pal : list nat -> Prop :=
| pal0 : pal []
| pal1 : forall (x : nat), pal [x]
| pal2 : forall (x : nat) (l : list nat),
  pal l -> pal (x :: (snoc l x)).

Theorem pal_app_rev : forall (l : list nat),
  pal (app l (rev l)).
Proof.
  intros l.
  induction l.
  (* pal ([] ++ rev []) *)
  simpl.
  apply pal0.
  (* pal ((x :: l) ++ rev (x :: l)) *)
  simpl.
  SearchAbout list.
  Check snoc_with_append.
  rewrite <- snoc_with_append.
  apply pal2.
  apply IHl.
Qed.

Lemma rev_snoc : forall (x : nat) (l : list nat),
  x :: rev l = rev (snoc l x).
Proof.
  intros x l.
  induction l.
  simpl.  
  reflexivity.
  
  simpl.
  rewrite <- IHl.
  simpl.
  reflexivity.
Qed.

Lemma snoc_rev : forall (x : nat) (l : list nat),
  snoc (rev l) x = rev (x :: l).
Proof.
  intros x l.
  induction l.
  simpl.
  reflexivity.
  simpl.
  reflexivity.
Qed.

Lemma snoc_xlx : forall (x : nat)  (l : list nat),
  x :: (snoc l x) = snoc (x :: l) x.
Proof.
  intros x l.
  induction l.
  simpl.
  reflexivity.
  simpl.
  reflexivity.
Qed.

Theorem pal_eq_rev : forall l, pal l -> l = rev l.
Proof.
  intros l H.
  induction H.
  (* [] = rev [] *)
  simpl.
  reflexivity.  
  
  (* [x] = rev [x] *)
  simpl.
  reflexivity.  
  
  (* x :: snoc l x = rev (x :: snoc l x) *)
  rewrite <- snoc_rev.
  rewrite <- rev_snoc.
  rewrite <- snoc_xlx.
  rewrite <- IHpal.
  reflexivity.
Qed.

Theorem eq_rev_pal : forall l, l = rev l -> pal l.
Proof.
  intros l E.
  rewrite E.
  induction l.
  simpl.
  apply pal0.

  simpl.
  rewrite snoc_rev.
  rewrite <- E.
Abort.                                      (* XXXXX *)

(** subseq *)      
Inductive subseq : list nat -> list nat -> Prop :=
| nseq0 : subseq [] []
| nseq1 : forall (n : nat) (l1 : list nat) (l2 : list nat),
  subseq l1 l2 -> subseq (n :: l1) (n :: l2)
| nseq2 : forall (n : nat) (l1 : list nat) (l2 : list nat),
  subseq l1 l2 -> subseq       l1  (n :: l2).

Theorem subseq_sym : forall l : list nat, subseq l l.
Proof.
  intros.
  induction l.
  apply nseq0.
  apply nseq1.
  apply IHl.
Qed.

Theorem subseq_app :
  forall l1 l2 l3 : list nat, subseq l1 l2 -> subseq l1 (app l2 l3).
Proof.
  intros l1 l2 l3 H.
  induction H.
  simpl.
  (* subseq [] l3 *)
  induction l3.
  (** subseq [] [] *)
  apply nseq0.
  (** subseq [] (x :: l3) *)
  apply nseq2.
  apply IHl3.
  simpl.
  (* subseq (n :: l1) (n :: l2 ++ l3) *)
  apply nseq1.
  apply IHsubseq.
  simpl.
  (*  subseq l1 (n :: l2 ++ l3) *)
  apply nseq2.
  apply IHsubseq.
Qed.

Theorem subseq_trs :                        (* XXXXXX *)
  forall l1 l2 l3 : list nat, subseq l1 l2 -> subseq l2 l3 -> subseq l1 l3.
Proof.
  intros l1 l2 l3.
Abort.

(* END *)
