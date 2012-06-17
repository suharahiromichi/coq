(*
   CPS ツリーの葉の数 (leaf_count)
   2010_10_29
   
   この証明は複雑すぎる。
   coq_cps_simple.v
   を参照のこと。
   *)


(**************)
(* Leaf-count *)
(**************)


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




Lemma leaf_count_1:
  leaf_count leaf = 1.
Proof.
  reflexivity.
Qed.


Lemma leaf_count_plus :
  forall l r, leaf_count (node l r) = (leaf_count l) + (leaf_count r).
Proof.
  reflexivity.
Qed.


Lemma leaf_count_cps_1 :
  forall f, leaf_count_cps leaf f = f 1.
Proof.
  reflexivity.
Qed.


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


Lemma eq_leaf_count_leaf_count_cps_aux :
  forall (t : tree),
    (forall f, f (leaf_count t) = (leaf_count_cps t f)) /\
    (forall g, g (leaf_count (node t leaf)) = (leaf_count_cps (node t leaf) g)) /\
    (forall h, h (leaf_count (node leaf t)) = (leaf_count_cps (node leaf t) h)).
  Proof.
    induction t.
    intros.
    split.
    intro f.
    rewrite leaf_count_1.
    rewrite leaf_count_cps_1.
    simpl.
    reflexivity.
    
    split.
    intro g.
    simpl.
    reflexivity.


    intro h.
    simpl.
    reflexivity.


    destruct IHt1 as [IHt10 [IHt11 IHt12]].
    destruct IHt2 as [IHt20 [IHt21 IHt22]].
    split.
    
    intro f.
    rewrite leaf_count_cps_plus.
    rewrite <- IHt10.
    rewrite <- IHt20.
    simpl.
    reflexivity.


    split.
    intro g.
    rewrite leaf_count_cps_plus.
    rewrite leaf_count_plus.
    rewrite leaf_count_1.
    simpl.
    rewrite <- IHt10.
    rewrite <- IHt20.
    reflexivity.


    intro g.
    rewrite leaf_count_cps_plus.
    rewrite leaf_count_plus.
    rewrite leaf_count_1.
    simpl.
    rewrite <- IHt10.
    rewrite <- IHt20.
    reflexivity.
Qed.
Check eq_leaf_count_leaf_count_cps_aux.


Theorem eq_leaf_count_leaf_count_cps :
  forall (l : tree), (forall f,
    f (leaf_count l) = (leaf_count_cps l f)).
Proof.
  intros.
  destruct (eq_leaf_count_leaf_count_cps_aux l).
  apply H.
Qed.


(* END *)
