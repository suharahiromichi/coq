(** sumbool は、Bool.Sumbool で定義さてているが、
   ここではすべて自分で定義してみる。 *)

(* 標準ライブラリ Sumbool.v *)
Hypothesis Aeq_dec :
  forall A : Type, forall a b : A, {a = b} + {a <> b}.

Definition bool_of_sumbool :
  forall A B:Prop, {A} + {B} -> {b : bool | if b then A else B}.
  intros A B H.
  elim H; intro; [exists true | exists false]; assumption.
Defined.

(* 標準ライブラリ List.v *)
Inductive list (A : Type) : Type :=
| nil : list A
| cons : A -> list A -> list A.

Fixpoint In (A:Type) (a:A) (l:list A) : Prop :=
  match l with
    | nil => False
    | (cons b m) => b = a \/ In _ a m
  end.

Theorem in_nil : forall A:Type, forall a : A, ~ In _ a (nil _).
Proof.
  unfold not; intros A a H; inversion_clear H.
Qed.

Theorem in_dec :
  (forall (A:Type) (x y:A), {x = y} + {x <> y}) ->
  forall (A:Type) (a:A) (l:list A), {In _ a l} + {~ In _ a l}.
Proof.
  intro H; induction l as [| a0 l IHl].
  right; apply in_nil.
  destruct (H A a0 a); simpl; auto.
  destruct IHl; simpl; auto.
  right; unfold not; intros [Hc1 | Hc2]; auto.
Defined.

(* Init/Specif.v
   つねにRequireされているので、proj1_sigは定義済み。*)
Definition proj1'_sig (A : Type) (P : A -> Prop) (e:sig P) :=
  match e with
    | exist a b => a
  end.

(* erutuf さんの diff.v *)
(* boolを返すin関数を定義する。 *)
Definition in_bool (A : Type) (a : A)(l : list A) : bool :=
  proj1'_sig _ _ (bool_of_sumbool _ _ (in_dec Aeq_dec _ a l)).

(* in_bool と In が、同値であることを証明する。 *)
Lemma in_bool_impl_In :
  forall A:Type, forall a l, in_bool A a l = true -> In A a l.
Proof.
  unfold in_bool.
  intros a l H.
  destruct (in_dec Aeq_dec a l); simpl in *; congruence.
Qed.

Lemma In_impl_in_bool :
  forall A:Type, forall a l, In A a l -> in_bool A a l = true.
Proof.
  unfold in_bool.
  intros a l H.
  destruct (in_dec Aeq_dec a l); simpl in *; congruence.
Qed.

(* END *)
