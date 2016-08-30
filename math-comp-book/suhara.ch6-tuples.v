From mathcomp Require Import all_ssreflect.

(* 6. Sub-Types Terms with properties *)
(* 6.1 n-tuples, lists with an invariant on the length *)

Structure tuple_of n T :=
  Tuple {
      tval :> seq T;
      _ : size tval == n
    }.

Notation "n .-tuple T" := (tuple_of n T)
                            (at level 2, format "n .-tuple T") : type_scope.

Lemma size_tuple T n (t : n.-tuple T) : size t = n.
Proof.
  case: t => s i.
  by apply/eqP.
Qed.

Example seq_on_tuple n (t : n.-tuple nat) :
  size (rev [seq 2 * x | x <- rev t]) = size t.
Proof.
  rewrite map_rev.                          (* t の rev を外に出す。 *)
  rewrite revK.                             (* 二重のrevを消す。 *)
  rewrite size_map.                         (* mapの結果のサイズは、引数のサイズと同じ。 *)
  done.

  Restart.
    by rewrite map_rev revK size_map.
Qed.


(* Unification debugging toolkit *)
Notation "X (*...*)" :=
  (let x := X in let y := _ in x)   (at level 100, format "X  (*...*)").
Notation "[LHS ’of’ equation ]" :=
  (let LHS := _ in
   let _infer_LHS := equation : LHS = _ in LHS)   (at level 4).
Notation "[unify X ’with’ Y ]" :=
  (let unification := erefl _ : X = Y in True).

Section CanonicalTuples.
  Variables (n : nat) (A B : Type).

  Lemma rev_tupleP (t : n.-tuple A) : size (rev t) == n.
  Proof.
      by rewrite size_rev size_tuple.
  Qed.
  Canonical rev_tuple (t : n.-tuple A) :=
    Tuple n A (rev t) (rev_tupleP t).
  
  Lemma map_tupleP (f: A -> B) (t: n.-tuple A) : size (map f t) == n.
  Proof.
      by rewrite size_map size_tuple.
  Qed.
  Canonical map_tuple (f: A -> B) (t: n.-tuple A) :=
    Tuple n B (map f t) (map_tupleP f t).
  
  Lemma cons_tupleP (t : n.-tuple A) x : size (x :: t) == n.+1.
  Proof.
      by rewrite /= size_tuple.
  Qed.
  Canonical cons_tuple x (t : n.-tuple A) : n.+1 .-tuple A :=
    Tuple n.+1 A (x :: t) (cons_tupleP t x).
End CanonicalTuples.


(* 証明 *)

Example just_tuple n (t : n.-tuple nat) :
  size (rev [seq 2 * x | x <- rev t]) = size t.
Proof.
    by rewrite !size_tuple.
Qed.

(*  6.2 n-tuples, a sub-type of sequences *)

Definition tcmp n (T : eqType) (t1 t2 : n.-tuple T) := tval n T t1 == tval n T t2.

Lemma eqtupleP n (T : eqType) : Equality.axiom (@tcmp n T).
Proof.
  move=> x y; apply: (iffP eqP); last first.
    by move=> ->.
    case: x; case: y => s1 p1 s2 p2 /= E.
    rewrite E in p2 *.
      by rewrite (eq_irrelevance p1 p2).
Qed.

Canonical tuple_eqType' (n : nat_eqType) (T : eqType) : eqType :=
  Equality.Pack (Equality.Mixin (@eqtupleP n T)) nat.

Check forall t : 3.-tuple nat, [:: t] == [::] : Prop.
Check forall t : 3.-tuple bool, uniq [:: t; t] : Prop.
(* Check forall t : 3.-tuple (7.-tuple nat), undup_uniq [:: t; t]. *)

Canonical tuple_subType (n : nat_eqType) (T : eqType) :=
  Eval hnf in [subType for tval n T].

Definition tuple_eqMixin (n : nat_eqType) (T : eqType) :=
  Eval hnf in [eqMixin of n.-tuple T by <:].

Canonical tuple_eqType (n : nat_eqType) (T : eqType) :=
  Eval hnf in EqType (n.-tuple T) (tuple_eqMixin n T).


(* 6.2.1 The sub-type kit *)

(* END *)
