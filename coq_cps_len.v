(*
   CPS その1、リストの長さ (len_cps)
   2010_10_29
   *)


Require Export List.
Require Export Arith.


(**************)
(* Len        *)
(**************)


(* 再帰関数 *)
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


Lemma len_Sn :
  forall n l, len (n::l) = S (len l).
Proof.
  reflexivity.
Qed.


Eval cbv in len_cps (1::2::3::4::nil) (fun (r:nat) => r).  (* 4 *)
Eval cbv in len_cps (2::3::4::nil) (fun (r:nat) => S r).   (* 4 *)


Lemma len_cps_Sn :
  forall n l f,
    len_cps (n::l) f =
    len_cps l (fun (r:nat) => f (S r)).
Proof.
  intros.
  simpl.
  (* ここでGoalの左辺が右辺とおなじになるように、定理を用意するのだ。*)
  reflexivity.
Qed.


Lemma eq_len_len_cps_aux :
  forall (l : list nat) (a : nat),
    (forall f, f (len l) = (len_cps l f)) /\
    (forall g, g (len (a::l)) = len_cps (a::l) g).
Proof.
  intros.
  induction l.
  auto.


  destruct IHl.
  split.
  apply H0.
  
  intros.
  rewrite len_cps_Sn.
  rewrite len_Sn.
  simpl.
  rewrite <- H.
  reflexivity.
Qed.
Check eq_len_len_cps_aux.


Theorem eq_len_len_cps :
  forall (l : list nat) (n : nat) (f : nat -> nat), f (len l) = (len_cps l f).
Proof.
  intros.
  destruct (eq_len_len_cps_aux l n).
  apply H.
Qed.


(* END *)
