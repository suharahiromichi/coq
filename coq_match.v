(* Coq Reference Manual
  Chaper 16. Extended Pattern-matching *)


(* 16.1  Patterns *)


Fixpoint max (n m:nat) {struct m} : nat :=
  match n with
  | O => m
  | S n' => match m with
            | O => S n'
            | S m' => S (max n' m')
            end
  end.
Reset max.


Fixpoint max (n m:nat) {struct m} : nat :=
  match n, m with
  | O, _ => m
  | S n', O => S n'
  | S n', S m' => S (max n' m')
  end.
Check (fun x:nat => match x return nat with
                    | y => y
                    end).
Reset max.


Fixpoint max (n m:nat) {struct n} : nat :=
  match n, m with
    | O, _ => m
    | S n' as p, O => p                       (* as p は、S n'の別名 *)
    | S n', S m' => S (max n' m')
  end.
Reset max.


Fixpoint even (n:nat) : bool :=
  match n with
  | O => true
  | S O => false
  | S (S n') => even n'
  end.
Print even.


Fixpoint lef (n m:nat) {struct m} : bool :=
  match n, m with
  | O, x => true
  | x, O => false
  | S n, S m => lef n m
  end.
Reset lef.


Fixpoint lef (n m:nat) {struct m} : bool :=
  match n, m with
  | O, x => true
  | S n, S m => lef n m
  | _, _ => false
  end.


Fixpoint max (n m:nat) {struct m} : nat :=
  match n, m with
  | S n', S m' => S (max n' m')
  | 0, p | p, 0 => p
  end.


Definition filter_2_4 (n:nat) : nat :=
  match n with
  | 2 as m | 4 as m => m
  | _ => 0
  end.


Definition filter_some_square_corners (p:nat*nat) : nat*nat :=
  match p return (nat*nat) with             (* return (nat*nat)は省略できる。 *)
  | ((2 as m | 4 as m), (3 as n | 5 as n)) => (m,n)
  | _ => (0,0)
  end.
Eval compute in filter_some_square_corners (2, 3). (* 2, 3 *)


(* 補足。match対象が nat*nat であることは同じ *)
Definition filter_some_square_corners'' (p:nat) (q:nat) : nat*nat :=
  match (p, q) return (nat*nat) with             (* return (nat*nat)は省略できる。 *)
  | ((2 as m | 4 as m), (3 as n | 5 as n)) => (m,n)
  | (_, _) => (0, 0)                        (* _ => (0, 0) でもよい。 *)
  end.
Eval compute in filter_some_square_corners'' 2 3. (* 2, 3 *)


(* 補足。match対象が nat*nat であることは同じ *)
Definition filter_some_square_corners' (p:nat) (q:nat) : nat*nat :=
  match p, q return (nat*nat) with             (* return (nat*nat)は省略できる。 *)
  | (2 as m | 4 as m), (3 as n | 5 as n) => (m,n)
  | _, _ => (0, 0)
  end.
Eval compute in filter_some_square_corners' 2 3. (* 2, 3 *)




(* 16.2  About patterns of parametric types *)


Inductive List (A:Set) : Set :=
  | nil : List A
  | cons : A -> List A -> List A.


Check
  (fun l:List nat =>
     match l with
     | nil _ => nil nat
     | cons _ _ l' => l'
     end).


(* 16.3  Matching objects of dependent types *)


Inductive listn : nat -> Set :=
  | niln : listn 0
  | consn : forall n:nat, nat -> listn n -> listn (S n).
Definition length (n:nat) (l:listn n) := n.
Reset length.


Definition length (n:nat) (l:listn n) :=
  match l with
  | niln => 0
  | consn n _ _ => S n
  end.


(*******************)
(* match-in-return *)
(*******************)


Fixpoint concat (n:nat) (l:listn n) (m:nat) (l':listn m) {struct l} :
 listn (n + m) :=
  match l in listn n return listn (n + m) with
  | niln => l'
  | consn n' a y => consn (n' + m) a (concat n' y m l')
  end.
Reset concat.


Fixpoint concat (n:nat) (l:listn n) (m:nat) (l':listn m) {struct l} :
 listn (n + m) :=
  match l in listn n, l' return listn (n + m) with
  | niln, x => x
  | consn n' a y, x => consn (n' + m) a (concat n' y m x)
  end.


(* 16.4  Using pattern matching to write proofs *)


Fixpoint buildlist (n:nat) : listn n :=
  match n return listn n with
  | O => niln
  | S n => consn n 0 (buildlist n)
  end.


Inductive LE : nat -> nat -> Prop :=
  | LEO : forall n:nat, LE 0 n
  | LES : forall n m:nat, LE n m -> LE (S n) (S m).


Fixpoint dec (n m:nat) {struct n} : LE n m \/ LE m n :=
  match n, m return LE n m \/ LE m n with
  | O, x => or_introl (LE x 0) (LEO x)
  | x, O => or_intror (LE x 0) (LEO x)
  | S n as n', S m as m' =>
      match dec n m with
      | or_introl h => or_introl (LE m' n') (LES n m h)
      | or_intror h => or_intror (LE n' m') (LES m n h)
      end
  end.


Lemma dec' (n m : nat) : LE n m \/ LE m n.
(*  intros n m. *)
  case (dec n m).
  intros h.
  left.
  apply h.
  intros h.
  right.
  apply h.
Qed.
Print dec'.


Definition dec'' (n m:nat) :=
  match dec n m with
    | or_introl h => or_introl (LE m n) h
    | or_intror h => or_intror (LE n m) h
  end.
Print dec''.


(* A Tutorial on [Co-]Inductive Types in Coq *)


(*******************)
(* match-return    *)
(*******************)
(* 3.1.1 Example: the predecessor function. *)


Definition pred (n:nat) :=
  match n return nat with                   (* return nat は省略できる。 *)
  | O => O
  | S m => m
  end.
Print pred.


Definition pred'' :=
  fun n : nat =>
    match n with                            (* inとreturn は省略できる。
                                               asは使わないので無意味 *)
(* match n as n0 in nat return nat with *)
    | 0 => 0
    | S m => m
    end.


(*******************)
(* match-as-return *)
(*******************)


(* 3.2.1 Example: strong specification of the predecessor function. *)


Definition pred_spec (n:nat) :=
  {m:nat | n = 0 /\ m = 0 \/ n = S m}.


Definition predecessor : forall n : nat, pred_spec n.
  intros.
  case n.


  (* Goal : pred_spec 0 *)
  unfold pred_spec.
  exists 0.
  auto.


  (* Gaol : pred_spec (S n0) *)
  intros.
  unfold pred_spec.
  exists n0.
  auto.
Qed.
Print predecessor.


Definition predecessor'' := 
  fun n : nat =>
    match n as n0 return (pred_spec n0) with (* as n0 は単なる別名である。 *)
    | 0 =>
      exist (fun m : nat => 0 = 0 /\ m = 0 \/ 0 = S m) 0
        (or_introl (0 = 1) (conj (refl_equal 0) (refl_equal 0)))
    | S n0 =>
      exist (fun m : nat => S n0 = 0 /\ m = 0 \/ S n0 = S m) n0
        (or_intror (S n0 = 0 /\ n0 = 0) (refl_equal (S n0)))
    end.




(*******************)
(* match-return    *)
(*******************)
(* 3.3.1 The Empty Type *)


Fact Nosense : 0 <> 0 -> 2 = 3.
  intro H.
  case H.
  reflexivity.
Qed.
Print Nosense.


Definition Nosense'' := 
  fun H : 0 <> 0 =>
    match H (refl_equal 0) return (2 = 3) with
    end.


(*******************)
(* match-in-return *)
(*******************)


(* 3.3.2 The Equality Type *)


Theorem trans : forall n m p : nat, n = m -> m = p -> n = p.
  intros n m p H H0.
  case H0.
  apply H.
Qed.
Print trans.


Definition trans'' :=
  fun (n m p : nat) (H : n = m) (H0 : m = p) =>
    match H0 with                           (* match H0 in (_ = y) return (n = y) with *)
      | refl_equal => H
    end.




(* 3.3.3 The Predicate n <= m *)


Lemma predecessor_of_positive :
  forall n, 1 <= n -> exists p : nat, n = S p.
  intros n H.
  case H.                                   (* eapply nat_ind with (n := n) in H. *)
    
  (* Goal :: exists p : nat, 1 = S p *)
  exists 0.
  reflexivity.
  
  (* Goal :: forall m : nat, 1 <= m -> exists p : nat, S m = S p *)
  intros m H0.
  exists m.
  reflexivity.
Qed.
Print predecessor_of_positive.


Definition predecessor_of_positive'' := 
  fun (n : nat) (H : 1 <= n) =>
    match H in (_ <= n0) return (exists p : nat, n0 = S p) with
    | le_n _ => ex_intro (fun p : nat => 1 = S p) 0 (refl_equal 1)
    | le_S _ m _ => ex_intro (fun p : nat => S m = S p) m (refl_equal (S m))
  end.


(* **** *)
(* 追記 *)
(* **** *)

(*
依存型の話 田中哲 産業技術総合研究所
Proof Summit 2018

dependent match (return 節を使うmatch) を使う用途はいくつかある
 *)

(*
(3) 型を計算して求める類の依存型の値を返したい (p.80)
*)

(* b の真偽で型が異なる型の例 *)
Definition D (b : bool) : Set :=
  if b then nat else unit.

(* 「D b」型とすれば正しいはずだが、Coqは見抜いてくれない *)
Fail Definition f b :=
  match b with
  | true => 0
  | false => tt
  end.

(* return節にD bと書けばCoqは正しく確認してくれる *)
Definition f b :=
  match b return D b with
  | true => 0
  | false => tt
end.

(* END *)
