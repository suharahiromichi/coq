From mathcomp Require Import all_ssreflect.

(* 6. Sub-Types Terms with properties *)
(* 6.1 n-tuples, lists with an invariant on the length *)

Structure tuple_of n T :=
  Tuple {
      tval :> seq T;                        (* コアーション *)
      _ : size tval == n
    }.

Notation "n .-tuple T" := (tuple_of n T)
                            (at level 2, format "n .-tuple T") : type_scope.

Lemma Hsize : size [::1;1;1] == 3. Proof. done. Qed.
Check Tuple 3 nat [::1;1;1] Hsize : 3.-tuple nat.
Check Tuple 3 nat [::1;1;1] Hsize : seq nat. (* コアーション による。 *)
Check size (Tuple 3 nat [::1;1;1] Hsize) : nat. (* seq nat のサイズ *)

(* n.-tuple T 型の値のサイズは、n である。 *)
Lemma size_tuple n T (t : n.-tuple T) : size t = n.
Proof.
  case: t => s i /=.
  Check (Tuple n T s i) : n.-tuple T.
  Check (Tuple n T s i) : seq T.            (* コアーション による。 *)
  Check size (Tuple n T s i).               (* seq T のサイズ *)
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
  (let x := X in let y := _ in x)
    (at level 100, format "X  (*...*)").
Notation "[LHS ’of’ equation ]" :=
  (let LHS := _ in
   let _infer_LHS := equation : LHS = _ in LHS)
    (at level 4).
Notation "[unify X ’with’ Y ]" :=
  (let unification := erefl _ : X = Y in True).


Section CanonicalTuples.
  Variables (n : nat) (A B : Type).

  (* tuple 全体に対する操作を tuple の tval に対する操作とみなすことができる。 *)
  (* rev_tuple ............. rev_tupleP *)

  Lemma rev_tupleP (t : n.-tuple A) : size (rev t) == n.
  Proof.
      by rewrite size_rev size_tuple.
  Qed.
(* Definition rev_tuple (t : n.-tuple A) := Tuple n A (rev t) (rev_tupleP t). *)
  Canonical rev_tuple (t : n.-tuple A) := Tuple n A (rev t) (rev_tupleP t).
  Print Canonical Projections.         (* rev <- tval ( rev_tuple ) *)
  
  Lemma map_tupleP (f: A -> B) (t: n.-tuple A) : size (map f t) == n.
  Proof.
      by rewrite size_map size_tuple.
  Qed.
(* Definition map_tuple (f: A -> B) (t: n.-tuple A) := Tuple n B (map f t) (map_tupleP f t). *)
  Canonical map_tuple (f: A -> B) (t: n.-tuple A) := Tuple n B (map f t) (map_tupleP f t).
  Print Canonical Projections.              (* map <- tval ( map_tuple ) *)
  
  Lemma cons_tupleP (t : n.-tuple A) x : size (x :: t) == n.+1.
  Proof.
      by rewrite /= size_tuple.
  Qed.
  Canonical cons_tuple x (t : n.-tuple A) : n.+1 .-tuple A :=
    Tuple n.+1 A (x :: t) (cons_tupleP t x).
End CanonicalTuples.

Check size_tuple : forall (n : nat_eqType) (T : Type) (t : n.-tupleT), size t = n.

(* 証明 *)

Example just_tuple n (t : n.-tuple nat) :
  size (rev [seq 2 * x | x <- rev t]) = size t.
Proof.
  Check size_tuple n nat t.
  rewrite (size_tuple n nat t).
  
  Check (size_tuple n nat
                    (rev_tuple n nat
                               (map_tuple n nat nat [eta muln 2] (rev_tuple n nat t)))).
  rewrite (size_tuple n nat
                      (rev_tuple n nat
                                 (map_tuple n nat nat [eta muln 2] (rev_tuple n nat t)))).
  reflexivity.

  Restart.
  rewrite size_tuple.
  (* rev_tuple と map_tuple のカノニカルをつかう。 *)
  rewrite size_tuple. (* カノニカルをDefinitionにすると、ふたつめの rewrite がエラーになる。 *)  
  reflexivity.

  Restart.
  by rewrite 2!size_tuple.
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

Canonical tuple_subType := Eval hnf in [subType for tval].

Variables (s : seq nat) (t : 3.-tuple nat).

Hypothesis size3s : size s == 3.

Let t1 : 3.-tuple nat := Sub s size3s.
Let s2 := if insub s is Some t then val (t : 3.-tuple nat) else nil.
Let t3 := insubd t s.                       (* : 3.-tuple nat *)

Definition pred T := T -> bool.

Section SubTypeKit.
  Variables (T : Type) (P : pred T).
  
  Structure subType : Type :=
    SubType {
        sub_sort :> Type;
        val : sub_sort -> T;
        Sub : forall x, P x -> sub_sort;
        (* elimination rule for sub_sort *)
        _: forall K (_ : forall x Px, K (@Sub x Px)) u, K u;
        _: forall x Px, val (@Sub x Px) = x
      }.

  Notation "[ ’subType’ ’for’ v ]" :=
    (SubType _ v _
             (fun K K_S u => let (x, Px) as u return K u := u in K_S x Px)
             (fun x px => erefl x)).

End SubTypeKit.
  
(* 6.2.2 A note on boolean Σ-types *)

Theorem eq_irrelevance (T : eqType) (x y : T) : forall e1 e2 : x = y, e1 = e2.
Proof.
Admitted.

 (* END *)
