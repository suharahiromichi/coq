(* CTL を 0の連続するストリーム zeros と isZeros に対して、
   Possible と Safepath を証明してみる *)


Inductive Label : Set :=
| LblA
| LblB
| LblC
| LblD
| LblE
| LblF.


Inductive tr : nat -> Label -> nat -> Prop :=   (* Transitions *)
| tra : tr 0 LblA 0
| trb : tr 0 LblB 0
| trc : tr 0 LblC 0
| trd : tr 0 LblD 0.


Require Import Streams.


Infix "^" := Cons.


(* CTL operators with co-inductives types: definitions and properties *)


CoInductive ForAllS (P : Stream nat -> Prop) : Stream nat -> Prop :=
  forallS :
  forall (x : Stream nat) (s : nat),
    P (s ^ x) -> ForAllS P x -> ForAllS P (s ^ x).


Inductive ExistsS (P : Stream nat -> Prop) : Stream nat -> Prop :=
| Here : forall x : Stream nat, P x -> ExistsS P x
| Further :
  forall (x : Stream nat) (s : nat), ExistsS P x -> ExistsS P (s ^ x).


CoInductive isTrace : Stream nat -> Prop :=
  is_trace :
  forall (x : Stream nat) (s1 s2 : nat) (l : Label),
    tr s1 l s2 -> isTrace (s2 ^ x) -> isTrace (s1 ^ s2 ^ x).      


Definition isTraceFrom (Sini : nat) (x : Stream nat) :=
  Sini = hd x /\ isTrace x.
  
(* Init => FA[] P *)
Definition Always (Sini : nat) (P : Stream nat -> Prop) :=
  forall x : Stream nat, isTraceFrom Sini x -> ForAllS P x.


(* Init => FA<> P *)
Definition Inevitable (Sini : nat) (P : Stream nat -> Prop) :=
  forall x : Stream nat, isTraceFrom Sini x -> ExistsS P x.


(* Init => EX<> P *)
Inductive Posible (Sini : nat) (P : Stream nat -> Prop) : Prop :=
  posible :
  forall x : Stream nat,
    isTraceFrom Sini x -> ExistsS P x -> Posible Sini P.


(* Init => EX[] P *)
Inductive SafePath (Sini : nat) (P : Stream nat -> Prop) : Prop :=
  safePath :
  forall x : Stream nat,
    isTraceFrom Sini x -> ForAllS P x -> SafePath Sini P.


Definition hd (x:Stream nat) := let (a,s) := x in a.
Definition tl (x:Stream nat) := let (a,s) := x in s.


(* Zero列 *)


CoFixpoint zeros : Stream nat :=
Cons 0 (zeros).


CoInductive isZeros : Stream nat -> Prop :=
  testz : forall s:Stream nat, hd s = 0 -> isZeros (tl s) -> isZeros s.


Definition frob (s : Stream nat) : Stream nat :=
  match s with
    | Cons h t => Cons h t
  end.


Theorem frob_eq : forall (s : Stream nat), s = frob s.
  intros. case s. intros.                   (* destruct s. *)
  unfold frob.
  reflexivity.
Qed.


Lemma lemma_is_zeros : isZeros zeros.
Proof.
  cofix H100.                               (* isZeros zeros *)
  
  Check (frob_eq zeros).
  rewrite (frob_eq zeros).
  simpl.
  apply testz.
  simpl.
  reflexivity.
  
  simpl.
  assumption.                               (* izZeros zeros *)
Qed.


Lemma lemma_is_trace : isTrace zeros.
Proof.
  rewrite (frob_eq zeros).
  simpl.
  
  cofix H110.                               (* isTrace (0 ^ zeros) *)
  
  rewrite (frob_eq zeros).
  simpl.
  Check ((is_trace zeros 0 0 LblA) tra).
  apply ((is_trace zeros 0 0 LblA) tra).
  
  assumption.                               (* isTrace (0 ^ zeros) *)
Qed.


Lemma lemma_foralls_isz_z : ForAllS isZeros zeros.
Proof.
  cofix H10.                                (* ForAllS isZeros zeros *)


  rewrite (frob_eq zeros).
  simpl.
  apply (forallS isZeros zeros).
  apply testz.
  simpl.
  reflexivity.
  simpl.


  (* isZeros zeros の証明 *)
  apply lemma_is_zeros.
  
  assumption.                               (* ForAllS isZeros zeros *)
Qed.


Goal Always 0 isZeros.
Proof.
  unfold Always.
  intros.
  inversion_clear H.
  rewrite (frob_eq x).
Abort.                                      (* XXXX *)




Goal Inevitable 0 isZeros.
Proof.
  unfold Inevitable.
  intros.
Abort.                                      (* XXXX *)




Goal Posible 0 isZeros.
Proof.
  Check (posible 0 isZeros zeros).
  apply (posible 0 isZeros zeros).
  unfold isTraceFrom.
  split.
  simpl.
  reflexivity.


  (* isTrace zeros の証明 *)
  apply lemma_is_trace.
  
  Check (Here isZeros zeros).
  apply (Here isZeros zeros).
  apply lemma_is_zeros.
Qed.




Goal SafePath 0 isZeros.
Proof.
  Check (safePath 0 isZeros zeros).
  apply (safePath 0 isZeros zeros).
  unfold isTraceFrom. 
  split.
  simpl.
  reflexivity.


  (* isTrace zeros の証明 *)
  apply lemma_is_trace.


  (* ForAllS isZeros zeros の証明 *)
  apply lemma_foralls_isz_z.
Qed.


(* END *)