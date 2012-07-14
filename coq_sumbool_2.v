(** sumbool は、Bool.Sumbool で定義さてているが、
   ここではすべて自分で定義してみる。 *)

Variable A : Type.

(* 標準ライブラリ Sumbool.v *)
Hypothesis Aeq_dec :
  forall a b : A, {a = b} + {a <> b}.

Definition bool_of_sumbool :
  forall x y:Prop, {x} + {y} -> {b : bool | if b then x else y}.
intros x y H.
  elim H; intro; [exists true | exists false]; assumption.
Defined.

(* 標準ライブラリ List.v *)
Inductive list (a : Type) : Type :=
| nil : list a
| cons : a -> list a -> list a.

Fixpoint In (a:A) (l:list A) : Prop :=
  match l with
    | nil => False
    | (cons b m) => b = a \/ In a m
  end.

Theorem in_nil : forall a : A, ~ In a (nil _).
Proof.
  unfold not; intros a H; inversion_clear H.
Qed.

Theorem in_dec :
  (forall x y:A, {x = y} + {x <> y}) ->
  forall (a:A) (l:list A), {In a l} + {~ In a l}.
Proof.
  intro H; induction l as [| a0 l IHl].
  right; apply in_nil.
  destruct (H a0 a); simpl; auto.
  destruct IHl; simpl; auto.
  right; unfold not; intros [Hc1 | Hc2]; auto.
Defined.

(* Init/Specif.v
   つねにRequireされているので、proj1_sigは定義済み。*)
Definition proj1'_sig (a : Type) (P : a -> Prop) (e:sig P) :=
  match e with
    | exist a b => a
  end.

(* erutuf さんの diff.v *)
(* boolを返すin関数を定義する。 *)
Definition in_bool (a : A)(l : list A) : bool :=
  proj1'_sig _ _ (bool_of_sumbool _ _ (in_dec Aeq_dec a l)).

(* in_bool と In が、同値であることを証明する。 *)
Lemma in_bool_impl_In :
  forall a l, in_bool a l = true -> In a l.
Proof.
  unfold in_bool.
  intros a l H.
  destruct (in_dec Aeq_dec a l); simpl in *; congruence.
Qed.

Lemma In_impl_in_bool :
  forall a l, In a l -> in_bool a l = true.
Proof.
  unfold in_bool.
  intros a l H.
  destruct (in_dec Aeq_dec a l); simpl in *; congruence.
Qed.

(* END *)
