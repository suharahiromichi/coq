(** ソフトウエアの基礎 Benjamin C. Pierceさん他、梅村さん他訳
   Prop_J: 命題と根拠からの抜粋
   証明オブジェクトを直接定義する。
   練習問題の回答が含まれていても、正解ではないかもしれない。
   @suharahiromichi *)

(*
   Inductive nat : Type :=
   | O : nat
   | S : nat -> nat.
*)

Fixpoint plus (n : nat) (m : nat) : nat :=
  match n with
    | O => m
    | S n' => S (plus n' m)
  end.
Notation "x + y" := (plus x y)  (at level 50, left associativity) : nat_scope.

Definition nat_ind' :
  forall P : nat -> Prop,
    P O ->                                  (* O : nat *)
    (forall n : nat, P n -> P (S n))  ->    (* S : nat -> nat *)
    forall n : nat, P n :=
      fun P : nat -> Prop => nat_rect P.

Theorem plus_one_r : forall n : nat,
  n + 1 = S n.
Proof.
  intros.
  induction n.
  reflexivity.
  simpl.
  rewrite IHn.
  reflexivity.
Qed.

Definition plus_one_r' : forall n : nat, n + 1 = S n :=
  fun n : nat =>
    nat_ind' (fun n0 : nat => n0 + 1 = S n0)
    (eq_refl 1)
    (fun (n0 : nat) (IHn : n0 + 1 = S n0) =>
      eq_ind_r
      (fun n1 : nat => S n1 = S (S n0))
      (eq_refl (S (S n0)))
      IHn)
    n.

(* inducitonとelimでは、同じオブジェクトが作られる。 *)
Theorem plus_one_r'' : forall n : nat,
  n + 1 = S n.
Proof.
  intros.
  elim n.
  reflexivity.
  simpl.
  intros n0 IHn.
  rewrite IHn.
  reflexivity.
Qed.

Theorem mult_0_r2 : forall n : nat,
  n * O = O.
Proof.
  intros n.                                 (* 省略できる。 *)
  induction n.
  reflexivity.
  simpl.
  rewrite -> IHn.
  reflexivity.
Qed.

Definition mult_0_r2' : forall n : nat, n * 0 = 0 :=
  fun n : nat =>
    nat_ind' (fun n0 : nat => n0 * 0 = 0)
    (eq_refl 0)
    (fun (n0 : nat) (IHn : n0 * 0 = 0) =>
      eq_ind_r (fun n1 : nat => n1 = 0)
      (eq_refl 0)
      IHn)
    n.

Fixpoint double (n:nat) :=
  match n with
  | O => O
  | S n' => S (S (double n'))
  end.


(* ****** *)
(* ev_ind *)
(* ****** *)
Inductive ev : nat -> Prop :=
| ev_0 : ev O
| ev_SS : forall n : nat, ev n -> ev (S (S n)).

Definition ev_ind' : forall P : nat -> Prop,
  P 0 ->
  (forall n : nat, ev n -> P n -> P (S (S n))) ->
  forall n : nat, ev n -> P n :=
    fun (P : nat -> Prop) (f : P 0)
      (f0 : forall n : nat, ev n -> P n -> P (S (S n))) =>
      fix F (n : nat) (e : ev n) {struct e} : P n :=
      match e in (ev n0) return (P n0) with
        | ev_0 => f
        | ev_SS n0 e0 => f0 n0 e0 (F n0 e0)
      end.
     
Theorem double_even : forall n,
  ev (double n).
Proof.
  intros.
  induction n.
  simpl.
  apply ev_0.
  simpl.
  apply ev_SS.
  apply IHn.
Qed.

Definition double_even' : forall n : nat, ev (double n) :=
  fun n : nat =>
    nat_ind' (fun n0 : nat => ev (double n0))
    ev_0
    (fun (n0 : nat) (IHn : ev (double n0)) => ev_SS (double n0) IHn)
    n.

Fixpoint evenb (n:nat) : bool :=
  match n with
  | O        => true
  | S O      => false
  | S (S n') => evenb n'
  end.

Definition even (n : nat) : Prop :=
  evenb n = true.

Theorem ev_even : forall n,
  ev n -> even n.
Proof.
  intros n E.
  induction E as [| n' E'].
  unfold even.
  reflexivity.
  unfold even.
  apply IHE'.
Qed.

Definition ev_even' : forall n : nat, ev n -> even n :=
  fun (n : nat) (E : ev n) =>
    ev_ind' (fun n0 : nat => even n0)
    (eq_refl true)
    (fun (n' : nat) (_ : ev n') (IHE' : even n') => IHE')
    n E.

Theorem ev_minus : forall n,
  ev n -> ev (pred (pred n)).
Proof.
  intros n E.
  induction E as [| n' E'].
  simpl.
  apply ev_0.
  simpl.
  apply E'.
Qed.
(* inducitonとelimでは、同じオブジェクトが作られる。 *)
Theorem ev_minus''' : forall n,
  ev n -> ev (pred (pred n)).
Proof.
  intros n E.
  elim E.
  simpl.
  apply ev_0.
  intros n' E' IHE.
  simpl.
  apply E'.
Qed.

Definition ev_minus' :  forall n : nat, ev n -> ev (pred (pred n)) :=
  fun (n : nat) (E : ev n) =>
    ev_ind' (fun n0 : nat => ev (pred (pred n0)))
    ev_0
    (fun (n' : nat) (E' : ev n') (_ : ev (pred (pred n'))) => E')
    n E.

Theorem ev_minus'' : forall n,
  ev n -> ev (pred (pred n)).
Proof.
  intros n E.
  destruct E as [| n' E'].
  simpl.
  apply ev_0.
  simpl.
  apply E'.
Qed.
(* destructとcaseでは、同じオブジェクトが作られる。*)
Theorem ev_minus'''' : forall n,
  ev n -> ev (pred (pred n)).
Proof.
  intros n E.
  case E.
  simpl.
  apply ev_0.
  simpl.
  intros n0 E'.
  apply E'.
Qed.
(* それは、inductionとelimとは、異なる。 *)
Definition ev_minus''''' :  forall n : nat, ev n -> ev (pred (pred n)) :=
fun (n : nat) (E : ev n) =>
  match E in (ev n0) return (ev (pred (pred n0))) with
    | ev_0 => ev_0
    | ev_SS _ E' => E'
  end.

Theorem SSev_even : forall n,
  ev (S (S n)) -> ev n.
Proof.
  intros n E.
  inversion E as [| n' E'].
  apply E'.
Qed.


(* ********** *)
(* MyProp_ind *)
(* ********** *)
Inductive MyProp : nat -> Prop :=
  | MyProp1 : MyProp 4
  | MyProp2 : forall n : nat, MyProp n -> MyProp (4 + n)
  | MyProp3 : forall n : nat, MyProp (2 + n) -> MyProp n.

(** 例えば以下のように定義される[MyProp] という性質について考えてみましょ
   う。
       - [4] は性質 [MyProp] を満たす
       - [n] が性質 [MyProp] を満たすならば、 [4+n] も満たす
       - もし[2+n]が性質 [MyProp] を満たすならば、 [n] も満たす
       - その他の数は、性質 [MyProp] を満たさない
    [MyProp] の非形式的な定義の最初の3つの節は、帰納的な定義の最初の3つ
    の節に反映されています。4つ目の節は、[Inductive] キーワードによって
    強制されます。
    
    補足：Inductiveは、その性質を満たす最小の集合であるから、「その他の
    数は、性質 [MyProp] を満たさない」ことは、Inductiveを使った時点で、
    その性質として決まっているので、記載する必要はない。最大の集合を示
    すのがcoinductiveである。*)

Definition MyProp_ind' : forall P : nat -> Prop,
  P 4 ->
  (forall n : nat, MyProp n -> P n -> P (4 + n)) ->
  (forall n : nat, MyProp (2 + n) -> P (2 + n) -> P n) ->
  forall n : nat, MyProp n -> P n :=
    fun (P : nat -> Prop) (f : P 4)
      (f0 : forall n : nat, MyProp n -> P n -> P (4 + n))
      (f1 : forall n : nat, MyProp (2 + n) -> P (2 + n) -> P n) =>
      fix F (n : nat) (m : MyProp n) {struct m} : P n :=
      match m in (MyProp n0) return (P n0) with
        | MyProp1 => f
        | MyProp2 n0 m0 => f0 n0 m0 (F n0 m0)
        | MyProp3 n0 m0 => f1 n0 m0 (F (2 + n0) m0)
      end.

Theorem MyProp_0 : MyProp 0.
Proof.
  apply MyProp3.
  simpl.                                    (* Goal : MyProp 2 *)
  apply MyProp3.
  simpl.                                    (* Goal : MyProp 4 *)
  apply MyProp1.
Qed.

Definition MyProp_0' : MyProp 0 :=
  MyProp3 0 (MyProp3 2 MyProp1).

Theorem MyProp_plustwo : forall n : nat, MyProp n -> MyProp (S (S n)).
Proof.
  intros n H.
  induction H.
  apply (MyProp2 2).
  apply (MyProp3 2).
  apply MyProp1.
  simpl.
  apply (MyProp2 (S (S n))).                (* -4する。 *)
  simpl.
  apply (MyProp3 (S (S n))).                (* +2する。 *)
  simpl.
  apply (MyProp2 n).                        (* -4する。 *)
  simpl.
  apply H.
  apply H.
Qed.

Theorem MyProp_ev : forall n : nat,
  ev n -> MyProp n.
Proof.
  intros n E.
  induction E as [| n' E'].
  apply MyProp_0.
  apply MyProp_plustwo.
  apply IHE'.
Qed.

Definition MyProp_ev' : forall n : nat, ev n -> MyProp n :=
  fun (n : nat) (E : ev n) =>
    ev_ind' (fun n0 : nat => MyProp n0)
    MyProp_0
    (fun (n' : nat) (_ : ev n') (IHE' : MyProp n') =>  MyProp_plustwo n' IHE')
    n E.

Theorem ev_plus4 : forall n,
  ev n -> ev (4 + n).
Proof.
  intros.
  simpl.
  apply ev_SS.                              (* Goal : ev SSSSn *)
  apply ev_SS.                              (* Goal : ev SSn *)
  apply H.                                  (* Goal : n *)
Qed.

Definition ev_plus4' : forall n, ev n -> ev (4 + n) :=
  fun n : nat => fun H : ev n => (ev_SS (S (S n)) (ev_SS n H)).

Theorem four_ev :
  ev 4.
Proof.
  apply ev_SS.                              (* Goal : ev 4 *)
  apply ev_SS.                              (* Goal : ev 2 *)
  apply ev_0.                               (* Goal : ev 0 *)
Qed.

Definition four_ev' : ev 4 :=
  (ev_SS (S (S O)) (ev_SS O ev_0)).

Theorem ev_MyProp : forall n : nat,
  MyProp n -> ev n.
Proof.
  intros n H.
  induction H as [| n' E1 | n' E2].
  apply four_ev.
  apply ev_plus4.
  apply IHE1.                               (* ev n' *)
  apply SSev_even.
  apply IHE2.                               (* ev (S (S n')) *)
Qed.

Definition ev_MyProp' : forall n : nat, MyProp n -> ev n :=
  fun (n : nat) (H : MyProp n) =>
    MyProp_ind' (fun n0 : nat => ev n0)
    four_ev'
    (fun (n' : nat) (_ : MyProp n') (IHE1 : ev n') => ev_plus4' n' IHE1)
    (fun (n' : nat) (_ : MyProp (2 + n')) (IHE2 : ev (2 + n')) =>
      SSev_even n' IHE2)
    n H.


(* *********** *)
(* natlist_ind *)
(* *********** *)
Inductive natlist : Type :=
  | nnil : natlist
  | ncons : nat -> natlist -> natlist.
Notation "x :: l" := (ncons x l) (at level 60, right associativity).
Notation "[ ]" := nnil.
Notation "[ x , .. , y ]" := (ncons x .. (ncons y nnil) ..).

Definition natlist_ind' : forall P : natlist -> Prop,
  P [] ->
  (forall (n : nat) (n0 : natlist), P n0 -> P (n :: n0)) ->
  forall n : natlist, P n :=
    fun P : natlist -> Prop => natlist_rect P.

Fixpoint app (l1 l2 : natlist) : natlist :=
  match l1 with
  | [] => l2
  | h :: t => h :: (app t l2)
  end.
Notation "x ++ y" := (app x y) (right associativity, at level 60).

Theorem app_ass : forall l1 l2 l3 : natlist,
  (l1 ++ l2) ++ l3 = l1 ++ (l2 ++ l3).
Proof.
  intros l1 l2 l3.
  induction l1 as [| n l1'].
  reflexivity.
  simpl.
  rewrite -> IHl1'.
  reflexivity.
Qed.

Definition pp_ass : forall l1 l2 l3 : natlist, (l1 ++ l2) ++ l3 = l1 ++ l2 ++ l3 :=
  fun l1 l2 l3 : natlist =>
    natlist_ind' (fun l4 : natlist => (l4 ++ l2) ++ l3 = l4 ++ l2 ++ l3)
    (eq_refl ([] ++ l2 ++ l3))
    (fun (n : nat) (l1' : natlist)
      (IHl1' : (l1' ++ l2) ++ l3 = l1' ++ l2 ++ l3) =>
      eq_ind_r (fun n0 : natlist => n :: n0 = n :: l1' ++ l2 ++ l3)
      (eq_refl (n :: l1' ++ l2 ++ l3)) IHl1')
    l1.


(* ******** *)
(* list_ind *)
(* ******** *)
Inductive list (X : Type) : Type :=
  | nil : list X
  | cons : X -> list X -> list X.

Definition list_ind' : forall (X : Type) (P : list X -> Prop),
  P (nil X) ->
  (forall (x : X) (l : list X), P l -> P (cons X x l)) ->
  forall l : list X, P l :=
    fun (X : Type) (P : list X -> Prop) => list_rect X P.

(* END *)
