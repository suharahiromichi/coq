(* John Backus's FP programming language, Backus's FP *)
(* プログラム代数 *)
(* Backus's FP Algebra *)


Require Import Setoid.                      (* rewrite H at n *)
Require Import Arith.


Inductive fp : Set :=
(* 組込関数 *)
| Id : fp
| None : fp                                 (* construction の端 *)
| Left : fp
| Right : fp
| Apndl : fp
(* 高階関数 *)
| Composition : fp -> fp -> fp
| Construction : fp -> fp -> fp
| Condition : fp -> fp -> fp -> fp
| Apply_to_all : fp -> fp
| Insert_right : fp -> fp
  .


Implicit Arguments Composition.
Infix "**" := Composition (at level 151, right associativity).
Implicit Arguments Construction.
Infix ":::" := Construction (at level 161, right associativity).
Notation "a ? b ; c" := (Condition a b c) (at level 190).
Implicit Arguments Apply_to_all.
Notation "@" := Apply_to_all (at level 141).
Implicit Arguments Insert_right.
Notation "//" := Insert_right (at level 141).


Variables obj : Set.
Variables cons : obj -> obj -> obj.
Infix "::" := cons (at level 60, right associativity). (* Listはつかえなくなる。 *)
Variables none : obj.
Variables tt : obj.


Inductive exec : obj -> fp -> obj -> Prop := .
(* | execId : forall x : obj, exec x Id x. 
   以下の公理をここに書いてしまうこともできる。
   *)


Axiom execId :
  forall x : obj, exec x Id x.


Axiom execLeft :
  forall (x y : obj),
    exec (cons x (cons y none)) Left x.
Axiom execRight :
  forall (x y : obj),
    exec (cons x (cons y none)) Right y.
Axiom execAppend :
  forall (x y : obj),
    exec (x :: y :: none) Apndl (x :: y).
(* 1 :: (2::3::4::none) :: none => 1 :: 2 :: 3 :: 4 :: none *)


Axiom execComp :
  forall (x z : obj) (f g : fp),
    (exists y, exec z g y /\ exec y f x) -> exec z (Composition f g) x.


Axiom execCons0 :
  forall (x : obj),
    exec x None none.
Axiom execCons :
  forall (x y z : obj) (f g : fp),
    (exec z f x /\ exec z g y) -> exec z (Construction f g) (cons x y).


Axiom execCondTrue :
  forall (x y : obj) (p f g : fp),
    (exec x p tt /\ exec x f y) -> exec x (Condition p f g) y.
Axiom execCondFalse :
  forall (x y : obj) (p f g : fp),
    (exec x p none /\ exec x g y) -> exec x (Condition p f g) y.
    
Axiom execMap0 :
  forall (f : fp),
    exec none (Apply_to_all f) none.
Axiom execMap :
  forall (x y xl yl : obj) (f : fp),
    exec y f x /\ exec yl (Apply_to_all f) xl ->
    exec (cons y yl) (Apply_to_all f) (cons x xl).


Axiom execInst0 :
  forall (x : obj) (f : fp),
    exec (cons x none) f x.
Axiom execInst :
  forall (x z l : obj) (f : fp),
    (exists y, exec (cons x (cons y none)) f z /\ exec l (Insert_right f) y) ->
    exec (cons x l) (Insert_right f) z.


(* 証明の例 *)


Lemma test_Id :
  forall xi xo : obj,
    xi = xo -> exec xi Id xo.
Proof.
  intros.
  rewrite <- H.
  apply execId.
Qed.


Lemma test_cond_comp :
  forall (x y : obj) (p f g : fp),
    (exec x p tt /\ exec x f y) -> exec x (p ? f ** Id ; g) y.
Proof.
  intros.
  apply execCondTrue.
  split.
  apply H.
  apply execComp.
  exists x.
  split.
  apply execId.
  destruct H as [Hp Hf].
  apply Hf.
Qed.


Lemma test_map_Id :
  forall xi xo : obj,
    exec xi Id xo -> exec (xi :: none) (@ Id) (xo :: none).
Proof.
  intros.
  apply execMap.
  split.
  apply H.
  apply execMap0.
Qed.


Lemma test_inst_Left :
  forall x y z : obj,
    exec (x :: y :: z :: none) (// Left) x.
Proof.
  intros.
  apply execInst.
  exists y.
  split.
  apply execLeft.


  apply execInst.
  exists z.
  split.
  apply execLeft.
  apply execInst0.
Qed.


Lemma test_inst_Right :
  forall x y z : obj,
    exec (x :: y :: z :: none) (// Right) z.
Proof.
  intros.
  apply execInst.
  exists z.
  split.
  apply execRight.


  apply execInst.
  exists z.
  split.
  apply execRight.
  apply execInst0.
Qed.


Lemma test_left_append :
  forall x y : obj,
    exec (x :: (y :: none) :: none) (Left ** Apndl) x.
Proof.
  intros.
  apply execComp.
  exists (x :: y :: none).
  split.
  apply execAppend.
  apply execLeft.
Qed.


Lemma test_append0 :                        (* Id ** [Left,Right] = Id *)
  forall x y,
    exec (x :: y :: none) (Id ** (Left ::: Right ::: None)) (x :: y :: none).
Proof.
  intros.
  apply execComp.
  exists (x :: y :: none).
  split.
  apply execCons.
  split.
  apply execLeft.
  apply execCons.
  split.
  apply execRight.
  apply execCons0.
  apply execId.
Qed.




Lemma test_append :                         (* Apndl ** [Left,[Right]] = Id *)
  forall x y,
    exec (x :: y :: none) (Apndl ** (Left ::: (Right ::: None) ::: None)) (x :: y :: none).
Proof.
  intros.
  apply execComp.
  exists (x :: (y :: none) :: none).
  split.
  apply execCons.
  split.
  apply execLeft.
  apply execCons.
  split.
  apply execCons.
  split.
  apply execRight.
  apply execCons0.
  apply execCons0.
  apply execAppend.
Qed.


(*
Lemma test :
  forall f g h,
    (Apndl ** (f ** g ::: @ f ** h ::: None)) =
    (@ f ** Apndl ** (g ::: h ::: None)).
*)


(* END *)