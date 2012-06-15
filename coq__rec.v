(* _rec を使った関数定義 *)
(* お茶大 浅井研、Coqゼミ 第5回 を参考にした。 *)


(* one *)


Inductive one : Set :=
  | One : one.                              (* : one は省略できる。 *)


Print one.
Check one.
Check One.
Print one_ind.
Check one_ind.
Print one_rec.
Check one_rec.


Definition f_one :=
  one_rec (fun n : one => nat) 1.
Check f_one.
Eval compute in f_one One.                  (* 1 *)


Definition f_one' (m : nat) :=
  one_rec (fun n : one => nat) m.
Check f_one'.
Eval compute in f_one'.
Eval compute in f_one' 11 One.              (* 11 *)


Definition f_one'' (m : nat) :=
  one_rec (fun f : one => nat -> nat)
    (fun n : nat => m + 1).
Check f_one''.
Eval compute in f_one''.
Eval compute in f_one'' 111 One.            (* 112 *)


(* season *)


Inductive season : Set :=
  | Spring : season
  | Summer : season
  | Fall : season
  | Winter : season.


Print season_ind.
Check season_ind.
Print season_rec.
Check season_rec.


Definition f :=
  season_rec (fun s : season => nat)
    0 1 2 3.


Eval compute in f Spring.                   (* 0 *)
Eval compute in f Summer.                   (* 1 *)
Eval compute in f Fall.                     (* 2 *)
Eval compute in f Winter.                   (* 3 *)




(* nat *)


Print nat_ind.
Check nat_ind.
Print nat_rec.
Check nat_rec.


Definition plus (m : nat) :=
  nat_rec (fun n : nat => nat)
   m
   (fun (n : nat) (x : nat) => S x).


Eval compute in plus 1 2.                   (* 3 *)
  
  
Lemma plus_n_0 : forall n : nat, n = n + 0.
  intros.
  induction n.
  simpl.
  reflexivity.
  simpl.
  rewrite <- IHn.
  reflexivity.
  Restart.


  intros.
  apply nat_ind with (n := n).
  simpl.
  reflexivity.
  intros.                                   (* *** *)
  simpl.
  rewrite <- H.
  reflexivity.
Qed.




(** おまけ **)


Definition pred_spec (n : nat) :=
  {m : nat | n = 0 /\ m = 0 \/ n = S m}.


Definition predecessor : forall n : nat, pred_spec n.
  intros n.
  apply nat_rec with (n := n).              (* case n *)
  (* ！！しかし、nat_ind ではだめであることに、注意！！ *)
  
  (* Goal : pred_spec 0 *)
  unfold pred_spec.
  exists 0.
  auto.


  (* Goal : forall n0 : nat, pred_spec n0 -> pred_spec (S n0) *)
  intros.
  unfold pred_spec.
  exists n0.
  auto.
Qed.


Print predecessor.


(* END *)