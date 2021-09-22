(**
# EqChain

- Julien Tesson, Hideki Hashimoto, Zhenjiang Hu, Frederic Loulergue,
and Masato Takeichi, "Program Calculation in Coq"

- 村田康佑 「定理証明支援系Coq によるデータ型汎用なプログラム運算」
§2.2 鎖状記法の設計と実装

- https://github.com/muratak17/Recursion-Schemes-in-Coq
eqchain.v
 *)

Require Import Coq.Program.Basics.

Module EqChain.

(* state for memorizing direction of equational reasoning *)

Inductive equational_reasoning_direction : Type :=
  Rightwards : equational_reasoning_direction
| Leftwards  : equational_reasoning_direction.

Inductive direction (cs : equational_reasoning_direction) : Prop :=
  state : direction cs.

(* tactic for obvious rewriting *)

Ltac obvious := (simpl; reflexivity) + easy + auto.

(* rewriting *)

Ltac eq_rewrite_l c t :=
  let Hre := fresh "H" in(
    match goal with
    | [ |- _ ?l _ ] =>
      ( assert (l = c) as Hre );
      [ t; obvious | idtac ];
      (erewrite Hre at 1) +                 (* coq の rewrite *)
      (match goal with
       | [ H : _ c c |- _] => idtac
       end);
      clear Hre
    end
  ).

Lemma flipgoal1 :
  forall {A B : Type} (R : A -> B -> Prop) (x : A) (y : B),
    flip R y x -> R x y. 
Proof.
  easy.
Qed.

Lemma flipgoal2 :
  forall {A B : Type} (R : A -> B -> Prop) (x : A) (y : B),
    R x y -> flip R y x. 
Proof.
  easy.
Qed.

End EqChain.

Tactic Notation "eqChain_add_state" constr(cs) :=
  let statename := fresh "d" in (
    pose ( statename := EqChain.direction cs )).

Tactic Notation "eqChain_set_state" constr(cs) :=
  match goal with
  | [d := EqChain.direction cs : Prop |- _] => idtac
  | [d := EqChain.direction _  : Prop |- _] => fail 1 "illegal direction"
  | _ => eqChain_add_state cs
  end.

Ltac eqChain_flipgoal :=
  match goal with
  | [ |- flip _ _ _ ] => apply EqChain.flipgoal2
  | [ |- _ _ _ ] => apply EqChain.flipgoal1
  end.

Ltac eqChain_eq_rewrite_r c t :=
  match goal with
  | [ |- ?R _ _ ] =>
    eqChain_flipgoal;
    EqChain.eq_rewrite_l c t;
    eqChain_flipgoal
  end.

(**
## 公開される Notation

最低限のTacticのみ公開しています。
*)

Tactic Notation (at level 2) "Left" "=" constr(c) "{" tactic(t) "}" :=
  EqChain.eq_rewrite_l c t ; eqChain_set_state EqChain.Rightwards.

Tactic Notation (at level 2) "=" constr(c) "{" tactic(t) "}" :=
  match goal with
  | [_ := EqChain.direction EqChain.Rightwards : Prop |- _] => EqChain.eq_rewrite_l c t
  | [_ := EqChain.direction EqChain.Leftwards  : Prop |- _] => eqChain_eq_rewrite_r c t
  end.

Tactic Notation (at level 2) "=" "Right" "{" tactic(t) "}" :=
  match goal with
  | [_ := EqChain.direction EqChain.Rightwards : Prop |- _ _ ?r] =>
    EqChain.eq_rewrite_l r t; reflexivity
  end.

(**
# テスト
*)
From mathcomp Require Import all_ssreflect.
From mathcomp Require Import all_algebra.
Require String.

Section Test.
  
  Goal 1 = 1.
  Proof.
    Left
    = (1)   {idtac}.
    = Right {idtac}.
  Qed.
  
  Goal 1 + 0 = 1.
  Proof.
    Left
    = (1)   {rewrite addn0}.
    = Right {done}.
  Qed.
  
  Lemma square_eq' a b : (a + b) * (a + b) = a * a + 2 * a * b + b * b.
  Proof.
    rewrite [LHS]mulnDr.
    rewrite 2![in LHS]mulnDl.
    rewrite [LHS]addnA.
    rewrite [b * a in LHS]mulnC.
    rewrite -2![LHS]addnA.
    rewrite [(a * b + (a * b + b * b)) in LHS]addnA.
    rewrite [a * b + a * b in LHS]addnn.
    rewrite [in LHS]doubleMl.
    rewrite -[in LHS]mul2n.
    rewrite [LHS]addnA.
    done.
  Qed.
  
  Lemma square_eq a b : (a + b) * (a + b) = a * a + 2 * a * b + b * b.
  Proof.
    Left
    = ((a + b) * a + (a + b) * b)         {rewrite mulnDr}.
    = (a * a + b * a + (a * b + b * b))   {rewrite 2!mulnDl}.
    = (a * a + b * a + a * b + b * b)     {rewrite addnA}.
    = (a * a + a * b + a * b + b * b)     {rewrite [a * b]mulnC}.
    = (a * a + (a * b + (a * b + b * b))) {rewrite -2!addnA}.
    = (a * a + (a * b + a * b + b * b))   {rewrite [(a * b + (a * b + b * b))]addnA}.
    = (a * a + ((a * b).*2 + b * b))      {rewrite addnn}.
    = (a * a + (a.*2 * b + b * b))        {rewrite doubleMl}.
    = (a * a + (2 * a * b + b * b))       {rewrite -mul2n}.
    = (a * a + 2 * a * b + b * b)         {rewrite addnA}.
    = Right                               {done}.
  Qed.
  
End Test.

Section Test2.

  Import GRing.Theory.        (* mulrA などを使えるようにする。 *)
  Import Num.Theory.          (* unitf_gt0 などを使えるようにする。 *)
  Import intZmod.             (* addz など *)
  Import intRing.             (* mulz など *)
  Open Scope ring_scope.      (* 環の四則演算を使えるようにする。 *)

  Lemma mulKq' (p q : rat) : 0 < p -> (p * q) / p = q.
  Proof.
    move=> Hp.
    rewrite [p * q]mulrC.                   (* q * p / p = q *)
    rewrite -mulrA.                         (* q * (p / p) = q *)
    rewrite divrr; last by rewrite unitf_gt0. (* q * 1 = q *)
      by rewrite mulr1.
  Qed.
  
  Lemma mulKq (p q : rat) : 0 < p -> (p * q) / p = q.
  Proof.
    move=> Hp.
    Left
    = (q * p / p)   {rewrite [p * q]mulrC}.
    = (q * (p / p)) {rewrite -mulrA}.
    = (q * 1)       {rewrite divrr; last by rewrite unitf_gt0}.
    = Right         {by rewrite mulr1}.
  Qed.

End Test2.

(**
ゴールそのものを転記できてもよいのではないか。
*)

Section Test3.
  
  Definition var := 'I_3.                     (* nat *)
  Notation symbol := String.string.
  Definition union (vl1 vl2 : {set var}) := vl1 :|: vl2.
  
  Inductive tree (* : Set *) :=
  | Var : var -> tree
  | Sym : symbol -> tree
  | Fork : tree -> tree -> tree.
  
  Fixpoint subs (x : var) (t t' : tree) : tree :=
    match t' with
    | Var v => if v == x then t else t'
    | Sym b => Sym b
    | Fork t1 t2 => Fork (subs x t t1) (subs x t t2)
    end.

  Fixpoint vars (t : tree) : {set var} :=     (* tree -> {set var} *)
    match t with
    | Var x => [set x]
    | Sym _ => set0
    | Fork t1 t2 => union (vars t1) (vars t2)
  end.
  
  Fixpoint vars_pairs (l : list (tree * tree)) : {set var} :=
    match l with
    | nil => set0                     (* 集合を後部から作るようにする *)
    | (t1, t2) :: r => union (union (vars t1) (vars t2)) (vars_pairs r)
    end.

  Definition subs_pair x t (p : tree * tree) := (subs x t p.1, subs x t p.2).

Lemma subs_pairs_sub x t l :                (* set *)
  {subset vars_pairs (map (subs_pair x t) l) <= union (vars t) (vars_pairs l)}.
(* *** *)
Admitted.

  Lemma l_vars_pairs_subset x t l :         (* set *)
    x \notin (vars t) ->
    x |: vars_pairs (map (subs_pair x t) l) \subset vars_pairs ((Var x, t) :: l).
  Proof.
    move=> Hx.
    apply/subsetP.
    move=> /= y /setU1P.
    case.
    + move=> ->.
      rewrite /union.
      rewrite -setUA.
      apply/setU1P.
        by left.
    + move/subs_pairs_sub.
      rewrite /union.
      move/setUP => [H1 | H2].
      * rewrite -setUA.
        apply/setU1P.
        right.
        apply/setUP.
          by left.
      *  rewrite -setUA.
         apply/setU1P.
         right.
         apply/setUP.
           by right.
  Qed.
  