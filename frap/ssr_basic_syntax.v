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

Require Import Ascii.
Require Import String.
Open Scope string_scope.

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

(* frap/FrapWithoutSets.v *)
Ltac linear_arithmetic :=
  intros;
  repeat match goal with
         | [ |- context[maxn ?a ?b] ] => rewrite /maxn; case: (a < b)
         | [ _ : context[maxn ?a ?b] |- _ ] => rewrite /maxn; case: (a < b)
         | [ |- context[minn ?a ?b] ] => rewrite /maxn; case: (a < b)
         | [ _ : context[minn ?a ?b] |- _ ] => rewrite /maxn; case: (a < b)
         end;
  ssromega.

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

Module ArithWithVariables.

  Inductive arith : Set :=
  | Const (n : nat)
  | Var (x : var)
  | Plus (e1 e2 : arith)
  | Times (e1 e2 : arith).

  Example ex1 := Const 42.
  Example ex2 := Plus (Const 1) (Times (Var "x") (Const 3)).

  Fixpoint size (e : arith) : nat :=
    match e with
    | Const _ => 1
    | Var _ => 1
    | Plus e1 e2 => 1 + size e1 + size e2
    | Times e1 e2 => 1 + size e1 + size e2
    end.

  Compute size ex1.
  Compute size ex2.

  Fixpoint depth (e : arith) : nat :=
    match e with
    | Const _ => 1
    | Var _ => 1
    | Plus e1 e2 => 1 + maxn (depth e1) (depth e2)
    | Times e1 e2 => 1 + maxn (depth e1) (depth e2)
    end.

  Compute depth ex1.
  Compute depth ex2.

  Lemma max_le_add m1 n1 m2 n2 : m1 <= m2 -> n1 <= n2 ->
                                 maxn m1 n1 <= m2 + n2.
  Proof.
    rewrite /maxn.
    case H : (m1 < n1) => Hm Hn.
    - rewrite -[n1]add0n. by apply: leq_add.
    - rewrite addnC -[m1]add0n. by apply: leq_add.

    Restart.
    rewrite /maxn.
    case H : (m1 < n1) => Hm Hn.
    - by ssromega.
    - by ssromega.

    Restart.
    linear_arithmetic.
  Qed.
  
  Theorem depth_le_size e : depth e <= size e.
  Proof.
    elim: e => [n | x | e1 He1 e2 He2 | e1 He1 e2 He2] //=;
               rewrite -addnA leq_add2l;
                 by apply: max_le_add.
  Qed.
  
  Fixpoint commuter (e : arith) : arith :=
    match e with
    | Const _ => e
    | Var _ => e
    | Plus e1 e2 => Plus (commuter e2) (commuter e1)
    | Times e1 e2 => Times (commuter e2) (commuter e1)
    end.

  Compute commuter ex1.
  Compute commuter ex2.

End ArithWithVariables.

(* END *)
