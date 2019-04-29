From mathcomp Require Import all_ssreflect.
Require Import Omega.
(*
(* https://github.com/affeldt-aist/seplog/blob/master/lib/ssrnat_ext.v *)
Require Import ssrnat_ext.                  (* ssromega *)
*)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
(* Set Print All. *)

Ltac ssromega :=
  (repeat ssrnat2coqnat_hypo ;
   ssrnat2coqnat_goal ;
   omega)
with ssrnat2coqnat_hypo :=
  match goal with
    | H : context [?L < ?R] |- _ => move/ltP: H => H
    | H : context [?L <= ?R] |- _ => move/leP: H => H
    | H : context [?L < ?M < ?R] |- _ => let H1 := fresh in case/andP: H => H H1
    | H : context [?L <= ?M < ?R] |- _ => let H1 := fresh in case/andP: H => H H1
    | H : context [?L <= ?M <= ?R] |- _ => let H1 := fresh in case/andP: H => H H1
    | H : context [addn ?L ?R] |- _ => rewrite <- plusE in H
    | H : context [muln ?L ?R] |- _ => rewrite <- multE in H
    | H : context [subn ?L ?R] |- _ => rewrite <- minusE in H
    | H : ?x == _ |- _ => match type of x with nat => move/eqP in H end; idtac x
    | H : _ == ?x |- _ => match type of x with nat => move/eqP in H end; idtac x
    | H : _ != ?x |- _ => match type of x with nat => move/eqP in H end
  end
with ssrnat2coqnat_goal :=
  rewrite -?plusE -?minusE -?multE;
  match goal with
    | |- is_true (_ < _)%nat => apply/ltP
    | |- is_true (_ <= _)%nat => apply/leP
    | |- is_true (_ && _) => apply/andP; split; ssromega
    | |- is_true (?x != _) => match type of x with nat => apply/eqP end
    | |- is_true (_ != ?x) => match type of x with nat => apply/eqP end
    | |- is_true (?x == _) => match type of x with nat => apply/eqP end
    | |- is_true (_ == ?x) => match type of x with nat => apply/eqP end
    | |- _ /\ _ => split; ssromega
    | |- _ \/ _ => (left; ssromega) || (right; ssromega)
    | |- _ => idtac
  end.

Goal forall x y : nat, x + 4 - 2 > y + 4 -> (x + 2) + 2 >= y + 6.
Proof.
  intros.
  ssromega.
Qed.


(* どちらも、m < n での場合分けで良い。 *)
Print maxn.            (* = fun m n : nat => if m < n then n else m *)
Print minn.            (* = fun m n : nat => if m < n then m else n *)

Ltac linear_arithmetic' :=
  intros;
  repeat match goal with
         | [ |- context[maxn ?a ?b] ] =>
           rewrite {1}/maxn; case: (leqP b a); intros

         | [ H : context[maxn ?a ?b] |- _ ] =>
           let H' := fresh in
           rewrite {1}/maxn in H; case: (leqP b a) => H'; try rewrite H' in H

         | [ |- context[minn ?a ?b] ] =>
           rewrite {1}/minn; case: (leqP b a); intros

         | [ H : context[minn ?a ?b] |- _ ] =>
           let H' := fresh in
           rewrite {1}/minn in H; case: (leqP b a) => H';
           try (rewrite leqNgt in H'; move/Bool.negb_true_iff in H'; rewrite H' in H)

         | _ => idtac
         end.
(* case H' : (a < b) の H' が展開できないため、それを使うのを避ける。 *)
(* destruct (a < b) eqn:H' としてもよい。 *)
(*
           let H' := fresh in
           rewrite {1}/maxn; destruct (a < b) eqn: H'; intros
*)

Ltac linear_arithmetic :=
  linear_arithmetic';
  try ssromega;
  rewrite //=.

(* sample *)

Goal forall n m, maxn n m = n <-> m <= n.
Proof.
  split.
  - move=> H.
    rewrite {1}/maxn in H.
    case: (leqP m n) => H'.
    + done.
    + rewrite H' in H.
      by ssromega.
  - move=> H.
    rewrite {1}/maxn.
    case: (leqP m n) => H'.
    + done.
    + ssromega.

  Restart.
  
  split.
  - by linear_arithmetic.
  - by linear_arithmetic.
Qed.

Lemma leq_ltF m n : m <= n <-> (n < m) = false.
Proof.
  rewrite leqNgt.
  split.
  - by move/Bool.negb_true_iff.
  - by move=> H; apply/Bool.negb_true_iff.
Qed.

Goal forall n m, minn n m = n <-> n <= m.
Proof.
  split.
  - move=> H.
    rewrite {1}/minn in H.
    case: (leqP m n) => H'.
    + move/leq_ltF in H'.
      rewrite H' in H.
      by ssromega.
    + by ssromega.

  - move=> H.
    rewrite {1}/minn.
    case: (leqP m n) => H'.
    + by ssromega.
    + done.
    
  Restart.
    
  split.
  - by linear_arithmetic.
  - by linear_arithmetic.
Qed.

Goal forall m1 n1 m2 n2, m1 <= m2 -> n1 <= n2 -> maxn m1 n1 <= m2 + n2.
Proof.
  linear_arithmetic'.
  - ssromega.
  - ssromega.

  Restart.
    
  move=> m1 n1 m2 n2.
  rewrite /maxn.
  Check leqP n1 m1.
  case: (leqP n1 m1) => H1 H2 H'.
  - ssromega.
  - ssromega.
Qed.

(* ***** *)

Ltac simplify := intros;
                 try autorewrite with core in *;
                 simpl in *.

Ltac equality := intuition congruence.

Ltac cases E := let Heq := fresh "Heq" in
                destruct E eqn: Heq. (* eqn: のスペースが要る。 *)

(* ***** *)

Require Import Ascii.
Require Import String.
Open Scope string_scope.

Section SSRAscii.

  Definition eqAscii (a b : ascii) : bool :=
    match ascii_dec a b with
    | left _ => true
    | right _ => false
    end.

  Compute eqAscii "a" "a".                  (* true *)
  Compute eqAscii "a" "b".                  (* false *)
  
  Lemma ascii_eqP (a b : ascii) : reflect (a = b) (eqAscii a b).
  Proof.
    rewrite /eqAscii.
    (* reflect (a = b) (if ascii_dec a b then true else false) *)
    apply: (iffP idP); by case: (ascii_dec a b).
  Qed.
  
  Fail Canonical ascii_eqType := [eqType of ascii].

  Definition ascii_eqMixin := @EqMixin ascii eqAscii ascii_eqP.
  Canonical ascii_eqType := @EqType ascii ascii_eqMixin.

  Canonical ascii_eqType' := [eqType of ascii].
End SSRAscii.

Check ascii_eqType : eqType.
Check "a"%char : ascii.
Check "a"%char : ascii_eqType.

Check true : bool.
Check true : bool_eqType.

Check 1 : nat.
Check 1 : nat_eqType.
  
Section SSRString.
  
  Definition eqString (s t : string) : bool :=
    match string_dec s t with
    | left _ => true
    | right _ => false
    end.
  
  Compute eqString "aaaa" "aaaa".             (* true *)
  Compute eqString "aaaa" "aa".               (* false *)
  
  Lemma string_eqP (x y : string) : reflect (x = y) (eqString x y).
  Proof.
    rewrite /eqString.
    apply: (iffP idP); by case: (string_dec x y).
  Qed.        
  
  Definition string_eqMixin := @EqMixin string eqString string_eqP.
  Canonical string_eqType := @EqType string string_eqMixin.

End SSRString.

Check "aaa" = "aaa" : Prop.
Check "aaa" == "aaa" : bool.
Check "aaa" == "aaa" : Prop.

Notation var := string.

(* END *)
