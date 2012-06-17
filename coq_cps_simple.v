(*
   再帰関数と CPS との等価性の証明。単純版
   （ひとつ前の値だけを使う再帰には、同じフレームワークで
   対応できるが、fibは不完全である）
   2010_10_30
   *)


Inductive tree : Set :=
| leaf : tree 
| node : tree->tree->tree.
Eval cbv in node (node leaf leaf) (node leaf leaf).


(* 再帰版 *)
Fixpoint leaf_count (t : tree) : nat :=
  match t with
    | leaf => 1
    | node r l => (leaf_count r) + (leaf_count l)
  end.
Eval cbv in leaf_count (node (node leaf leaf) (node leaf leaf)). (* 4 *)


(* CPS版 *)
Fixpoint leaf_count_cps (t : tree) (cont : nat -> nat) : nat :=
  match t with
    | node r l =>
      leaf_count_cps r
      (fun n => leaf_count_cps l
        (fun m => cont (n + m)))
    | leaf =>
      cont 1
  end.
Eval cbv in leaf_count_cps (node (node leaf leaf) (node leaf leaf)) (fun n => n). (* 4 *)
Eval cbv in leaf_count_cps (node (node (node leaf leaf) (node leaf leaf))
  (node leaf (node leaf leaf))) (fun n => n). (* 7 *)


Eval cbv in leaf_count_cps (node leaf leaf) (fun (r:nat) => r).   (* 2 *)
Eval cbv in leaf_count_cps leaf
  (fun (n1:nat) => leaf_count_cps leaf
    (fun (n2:nat) => n1 + n2)).             (* 2 *)


Lemma leaf_count_cps_plus :
  forall l r f,
    leaf_count_cps (node l r) f =
    leaf_count_cps l (fun n1:nat => leaf_count_cps r (fun n2:nat => f (n1 + n2))).
Proof.
  intros.
  simpl.
  (* このGoalの左辺が右辺とおなじになるように、定理を用意するのだ。*)
  reflexivity.
Qed.


Theorem eq_leaf_count_leaf_count_cps :
  forall (t : tree),
    (forall f, f (leaf_count t) = (leaf_count_cps t f)).
Proof.
    induction t.
    intros.
    simpl.
    reflexivity.
    
    intro f.
    rewrite leaf_count_cps_plus.
    rewrite <- IHt1.
    rewrite <- IHt2.
    simpl.
    reflexivity.
Qed.




(***************)
(* List Length *)
(***************)
Require Export List.


(* 再帰版 *)
Fixpoint len (lst : list nat) :=
   match lst with 
     | nil => 0
     | hd :: tl => S (len tl)
   end.
Eval cbv in len (1::2::3::4::nil).


(* CPS版 *)
Fixpoint len_cps (lst : list nat) (cont : nat -> nat) :=
   match lst with 
     | nil => cont 0
     | hd :: tl => len_cps tl (fun x => cont (S x))
   end.
Eval cbv in len_cps (1::2::3::4::nil) (fun n:nat => n).


Lemma len_cps_Sn :
  forall n l f,
    len_cps (n::l) f =
    len_cps l (fun (r:nat) => f (S r)).
Proof.
  intros.
  simpl.
  reflexivity.
Qed.


Theorem eq_len_len_cps :
  forall (t : list nat),
    (forall f, f (len t) = (len_cps t f)).
Proof.
    induction t.
    intros.
    simpl.
    reflexivity.
    
    intro f.
    rewrite len_cps_Sn.
    rewrite <- IHt.
    simpl.
    reflexivity.
Qed.


(************)
(* 階乗     *)
(************)


(* 階乗の再帰版 *)
Fixpoint fact (n : nat) : nat :=
  match n with
    | 0 => 1
    | (S n') => n * fact n'
  end.
Eval cbv in fact 6.                         (* 720 *)


(* CPS 版 *)
Fixpoint fact_cps (n : nat) (cont : nat -> nat) : nat :=
  match n with
    | 0 => cont 1
    | (S n') => fact_cps n' (fun (a : nat) => cont (n * a))
  end.
Eval cbv in fact_cps 6 (fun a => a).        (* 720 *)


Lemma fact_cps_Sn :
  forall n f,
    fact_cps (S n) f =
    fact_cps n (fun (r:nat) => (f (S n * r))).
Proof.
  intros.
  simpl.
  reflexivity.
Qed.


(* fact_cps_Sn の実験 *)
Eval cbv in fact_cps 6 (fun (r:nat) => r).  (* 720 *)
Eval cbv in fact_cps 5 (fun (r:nat) => (6 * r)). (* 720 *)


Theorem eq_fact_fact_cps :
  forall (n:nat),
    (forall f, f (fact n) = fact_cps n f).
Proof.
  induction n.
  intros.
  simpl.
  reflexivity.
    
  intro f.
  rewrite fact_cps_Sn.
  rewrite <- IHn.
  simpl.
  reflexivity.
Qed.


(******************)
(* フィボナッチ数 *)
(******************)


(** 普通のフィボナッチ関数の定義 *)
Fixpoint fib (n: nat) : nat :=
  match n with
    | 0 => 1
    | 1 => 1
    | S (S m as sm) => fib sm + fib m
  end.


(** CPS変換されたフィボナッチ関数の定義 *)
Fixpoint fib_cps (n:nat) (cont:nat -> nat) : nat :=
  match n with
    | 0 =>  cont 1
    | 1 =>  cont 1
    | S (S m as sm) =>
      fib_cps sm (fun r1 =>
        fib_cps m (fun r2 => cont (r1 + r2)))
  end.


Lemma fib_SSn : forall n, fib (S (S n)) = fib (S n) + fib n.
  reflexivity.
Qed.


Lemma fib_cps_SSn :
  forall n f,
    fib_cps (S (S n)) f = fib_cps (S n) (fun r1 => fib_cps n (fun r2 => f (r1+r2))).
Proof.
  reflexivity.
Qed.


Hypothesis eq_fib_fib_cps_SSn :             (* XXXX *)
  forall n f,
    f (fib (S (S n))) = fib_cps n (fun r2 : nat => f (fib (S n) + r2)).


Theorem eq_fib_fib_cps :
  forall n f, f (fib (S n)) = fib_cps (S n) f.
Proof.
  induction n.
  intros.
  simpl.
  reflexivity.
    
  intro f.
  rewrite fib_cps_SSn.
  rewrite <- IHn.
  apply eq_fib_fib_cps_SSn.                 (* XXXX *)
Qed.


(* END *)
