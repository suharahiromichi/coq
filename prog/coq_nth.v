Require Import Omega.
Require Import List.
Require Import Arith.
Require Import Program.

Set Implicit Arguments.

Section Nth.
  Variable A : Type.
  
  Fixpoint nth' (l : list A) (n : nat) (default : A) {struct l} : A :=
    match n with
    | 0 => match l with
           | [] => default
           | x :: _ => x
           end
    | S m => match l with
             | [] => default
             | _ :: t => nth' t m default
             end
    end.
  
  Lemma len__S_len (x : A) (l : list A) : length (x :: l) = S (length l).
  Proof.
    now simpl.
  Qed.
  
  Program Fixpoint safe_nth (l : list A)
          (n : nat | n < length l)
          {measure (length l)} : A :=
    match n with
    | 0 => match l with
           | [] => !
           | x :: l' => x
           end
    | S m => match l with
             | [] => !
             | x' :: l' => safe_nth l' m
             end
    end.
  Obligations.
  Obligation 1.
  Proof.
    now inversion H.
  Defined.
  Obligation 2.
  Proof.
    now inversion H.
  Defined.
  Obligation 3.
  Proof.
    rewrite len__S_len in H.
    omega.
  Defined.
End Nth.

Definition ll := [1;2;3].
Definition n_of_ll : { n : nat | n < length ll}.
Proof.
  exists 2.
  simpl.
  omega.
Defined.

Compute safe_nth nat ll n_of_ll.            (* 3 *)

Extraction safe_nth.

(* **** *)
(* 応用 *)
(* **** *)

Check proj1_sig.
Locate "` _".

Definition sorted' (al : list nat) :=       (* := での定義！ *)
  forall (Hi : {i : nat | i < length al})
         (Hj : {j : nat | j < length al}),
    `Hi < `Hj ->
    safe_nth nat al Hi <= safe_nth nat al Hj.

Goal sorted' [1;2;3].
Proof.
  unfold sorted'.
  intros.
  case Hi as [xn Hn].
  case Hj as [xm Hm].
  simpl in *.
  (* 
   Goal : 
   xn < xm ->   
   safe_nth nat [1; 2; 3] (exist (fun n : nat => n < 3) xn Hn) <=
   safe_nth nat [1; 2; 3] (exist (fun n : nat => n < 3) xm Hm)
   *)
  Admitted.

Definition sorted''' (al: list nat) :=
  forall i j, i < j < length al -> nth i al 0 <= nth j al 0.

Goal sorted''' [1;2;3].
Proof.
  unfold sorted'''.
  intros.
  simpl in H.
  (* Goal : i < j < 3 -> nth i [1; 2; 3] 0 <= nth j [1; 2; 3] 0 *)
  Admitted.

(* END *)
