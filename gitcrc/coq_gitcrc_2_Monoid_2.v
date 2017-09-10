(**
A Gentle Introduction to Type Classes and Relations in Coq
の Chapter 2 An Introductory Example: Computing x^n
の抜萃をもとに説明のための修正を加えました。

@suharahiromichi
*)

Set Implicit Arguments.

Require Import Arith.                       (* for ring. *)
Require Import ZArith.
Require Import Div2.
Require Import Program.

(** Monoid モノイド
- carrier (台) A
- binary, associative operation 'dot' on A
- neutral element 1 ∈ A for 'dot'
 *)
Class Monoid {A : Type} (dot : A -> A -> A) (one : A) : Type :=
  {
    dot_assoc : forall x y z: A, dot x (dot y z) = dot (dot x y) z;
    one_left  : forall x, dot one x = x;
    one_right : forall x, dot x one = x
  }.

(* ************** *)
(* 自然数 (N,*,1) *)
(* ************** *)
Program Instance Mult : Monoid mult 1.
Obligation 1.                               (* x * (y * z) = x * y * z *)
Proof.
  ring.
Qed.
Obligation 3.                               (* x * 1 = x *)
Proof.
  ring.
Qed.

(* ************ *)
(* 整数 (Z,*,1) *)
(* ************ *)
Open Scope Z_scope.

Program Instance ZMult : Monoid Zmult 1.
Obligation 1.                               (* x * (y * z) = x * y * z *)
Proof.
  ring.
Qed.
Obligation 2.                               (* 1 * x = x *)
Proof.
  now destruct x.
Qed.
Obligation 3.                               (* x * 1 = x *)
Proof.
  ring.
Qed.

(* 2x2 行列 Matrix の定義 *)
Section M2_def.
  
  Variable (A : Type).
  Variable (zero one : A).
  Variable (plus mult minus : A -> A -> A).
  Variable (sym : A -> A).
  
  (*
  (* ring タクティクのために ring_theory を使う場合。 *)
  Variable rth : ring_theory zero one plus mult minus sym (@eq A).
  Add Ring Aring : rth.
   *)
  (* ring タクティクのために semi_ring_theory を使う場合。 *)  
  Variable sth : semi_ring_theory zero one plus mult (@eq A).
  Add Ring Aring : sth.
  
  Notation "0" := zero.
  Notation "1" := one.
  Notation "x + y" := (plus x y).  
  Notation "x * y" := (mult x y).
  
  Structure M2 : Type := {c00 : A;  c01 : A;
                          c10 : A;  c11 : A}.
  
  Definition Id2 : M2 := Build_M2 1 0 0 1.
  
  Definition M2_mult (m m':M2) : M2 :=
    Build_M2 (c00 m * c00 m' + c01 m * c10 m')
             (c00 m * c01 m' + c01 m * c11 m')
             (c10 m * c00 m' + c11 m * c10 m')
             (c10 m * c01 m' + c11 m * c11 m').
 
  Lemma M2_eq_intros : forall a b c d a' b' c' d',
      a=a' -> b=b' -> c=c' -> d=d' ->
      Build_M2 a b c d = Build_M2 a' b' c' d'.
  Proof. 
    intros; now f_equal.
  Qed.
  
  Program Instance M2_Monoid : Monoid M2_mult Id2.
  Obligation 1.
  (*
  M2_mult plus mult x (M2_mult plus mult y z) =
   M2_mult plus mult (M2_mult plus mult x y) z
   *)
  Proof.
    destruct x; destruct y; destruct z; simpl.
    unfold M2_mult; apply M2_eq_intros; simpl; ring.
  Qed.
  Obligation 2.                             (* M2_mult plus mult (Id2 0 1) x = x *)
    destruct x; simpl;
    unfold M2_mult; apply M2_eq_intros; simpl; ring.
  Qed.
  Obligation 3.                             (* M2_mult plus mult x (Id2 0 1) = x *)
    destruct x; simpl;
    unfold M2_mult; apply M2_eq_intros; simpl; ring.
  Qed.
End M2_def.

(* ************* *)
(* 自然数2x2行列 *)
(* ************* *)
Open Scope nat_scope.
Check Nth : semi_ring_theory 0%N 1%N N.add N.mul eq.
(* https://coq.inria.fr/library/Coq.setoid_ring.InitialRing.html で定義 *)
(* ./plugins/setoid_ring/InitialRing.v *)

Instance M2N : Monoid _ _ := M2_Monoid Nth.

(* *********** *)
(* 整数2x2行列 *)
(* *********** *)
Open Scope Z_scope.
Check Zth : ring_theory 0 1 Z.add Z.mul Z.sub Z.opp eq.
(* https://coq.inria.fr/library/Coq.setoid_ring.InitialRing.html で定義 *)
(* ./plugins/setoid_ring/InitialRing.v *)

Lemma Sth : semi_ring_theory 0 1 Z.add Z.mul eq.
Proof.
  split.
  - exact Z.add_0_l.
  - exact Z.add_comm.
  - exact Z.add_assoc.
  - exact Z.mul_1_l.
  - exact Z.mul_0_l.
  - exact Z.mul_comm.
  - exact Z.mul_assoc.
  - exact Z.mul_add_distr_r.
Qed.

Instance M2Z : Monoid _ _ := M2_Monoid Sth.


(***************)
(* ベキ乗の定義 *)
(***************)
Generalizable Variables A dot one.

Fixpoint power `{Monoid A dot one} (a : A) (n : nat) := (* 「`」 でコンテキスト *)
  match n with
    | 0%nat => one
    | S p => dot a (power a p)
  end.

Section binary_power. 
  Context `{M : Monoid A dot one}.          (* コンテキスト *)
  
  Program Fixpoint binary_power_mult (acc : A) (x : A) (n : nat) {measure n} : A :=
    (* Implicit generalization によって、
       (A:Type) (dot:A->A->A) (one:A) (M: @Monoid A dot one)
       が省かれている。 *)
    (* acc * (x ** n) *) 
    let M' := M in
    match n with
      | 0%nat => acc
      | _ => if  Even.even_odd_dec n
             then
               binary_power_mult  acc (dot x x) (div2 n)
             else
               binary_power_mult  (dot acc  x) (dot  x  x) (div2 n)
    end.
  Obligations.
  Next Obligation.                          (* Obligation 1 *)
    set (M' := M); apply lt_div2.
    apply neq_0_lt in H.
    apply H.
    Defined.
  Next Obligation.                          (* Obligation 2 と 3 *)
    set (M' := M); apply lt_div2; auto with arith.
    Defined.
  Check binary_power_mult.                  (* A -> A -> nat -> A *)
(*
  証明を1行にまとめると、以下になる。Next Obligation も要らないので、注意。
  Solve Obligations using program_simpl; set (M' := M); apply lt_div2; auto with arith.
 *)

  Import WfExtensionality.
  Lemma binary_power_mult_equation (acc x:A)(n:nat) :
    binary_power_mult acc x n =
    match n with
      | 0%nat => acc
      | _ => if Even.even_odd_dec n
             then
               binary_power_mult acc (dot x x) (div2 n)
             else
               binary_power_mult (dot acc  x) (dot  x  x) (div2 n)
    end.
  Proof.
    unfold binary_power_mult at 1.
    on_call binary_power_mult_func
            ltac:(fun c => 
                    unfold_sub @binary_power_mult_func c;
                    fold binary_power_mult_func).
    simpl. destruct n; reflexivity.
  Qed.
End binary_power.

Definition binary_power `{Monoid A dot one} x n :=
  binary_power_mult one x n.

(****************)
(* 整数のベキ乗 *)
(****************)
Compute binary_power 2 100.
(* = 1267650600228229401496703205376 : Z *)

(************************)
(* 整数の2x2行列のベキ乗 *)
(************************)
Compute power (Build_M2 1 1 1 0) 40.
Compute binary_power (Build_M2 1 1 1 0) 40.
(* = {|
       c00 := 165580141;
       c01 := 102334155;
       c10 := 102334155;
       c11 := 63245986 |}
     : M2 Z
 *)

Definition fibonacci (n : nat) :=
  c00 (power (Build_M2 1 1 1 0) n).
Compute fibonacci 20.                       (* = 10946 : Z *)

(* ********************************************* *)
(* power と binary_power が等価なことを証明する。 *)
(* ********************************************* *)
Section About_power.
  
  Require Import Arith.
  Context `(M : Monoid A dot one ).
  
  Ltac monoid_rw :=
    rewrite (@one_left A dot one M) || 
            rewrite (@one_right A dot one M)|| 
            rewrite (@dot_assoc A dot one M).

  Ltac monoid_simpl := repeat monoid_rw.

  Local Infix "*" := dot.
  Local Infix "**" := power (at level 30, no associativity).
  (* "+" はnat のplusである。power : A -> nat -> A だから。 *)
  
  Lemma power_x_plus :
    forall x n p, x ** (n + p) =  x ** n *  x ** p.
  Proof.
    induction n as [| p IHp]; simpl.
    intros; monoid_simpl; trivial.
    intro q; rewrite (IHp q); monoid_simpl; trivial. 
  Qed.
  
  Ltac power_simpl := repeat (monoid_rw || rewrite <- power_x_plus).
  
  Lemma power_commute :
    forall x n p, x ** n * x ** p = x ** p * x ** n. 
  Proof.
    intros x n p; power_simpl; rewrite (plus_comm n p); trivial.
  (* plus_comm は、nat のそれ。 *)
  Qed.
  
  Lemma power_commute_with_x :
    forall x n, x * x ** n = x ** n * x.
  Proof.
    induction n; simpl; power_simpl; trivial.
    repeat rewrite <- (@dot_assoc A dot one M); rewrite IHn; trivial.
  Qed.
  
  Lemma power_of_power :
    forall x n p,  (x ** n) ** p = x ** (p * n).
  Proof.
    induction p; simpl; [| rewrite power_x_plus; rewrite IHp]; trivial.
  Qed.
  
  Lemma power_S :
    forall x n, x *  x ** n = x ** S n.
  Proof.
    intros; simpl; auto.
  Qed.
  
  Lemma sqr : forall x, x ** 2 =  x * x.
  Proof.
    simpl; intros; monoid_simpl; trivial.
  Qed.
  
  Ltac factorize := repeat (
                        rewrite <- power_commute_with_x ||
                                rewrite <- power_x_plus ||
                                rewrite <- sqr ||
                                rewrite power_S ||
                                rewrite power_of_power).
  
  Lemma power_of_square :
    forall x n, (x * x) ** n = x ** n * x ** n.
  Proof.
    induction n; simpl; monoid_simpl; trivial.
    repeat rewrite dot_assoc; rewrite IHn; repeat rewrite dot_assoc.
    factorize; simpl; trivial.
  Qed.
  
  Lemma binary_power_mult_ok :
    forall n a x,  binary_power_mult a x n = a * x ** n.
  Proof.
    intro n; pattern n;apply lt_wf_ind.
    clear n; intros n Hn; destruct n.
    intros; simpl; monoid_simpl; trivial.
    intros; rewrite binary_power_mult_equation. 
    destruct (Even.even_odd_dec (S n)).
    rewrite Hn.
    rewrite power_of_square; factorize.
    pattern (S n) at 3; replace (S n) with (div2 (S n) + div2 (S n))%nat; auto.
    generalize (even_double _ e); simpl; auto. 
    apply lt_div2; auto with arith.
    rewrite Hn. 
    rewrite power_of_square; factorize.
    pattern (S n) at 3; replace (S n) with (S (div2 (S n) + div2 (S n)))%nat; auto.
    rewrite <- dot_assoc; factorize;auto.
    generalize (odd_double _ o); intro H; auto.
    apply lt_div2; auto with arith.
  Qed.
  
  Lemma binary_power_ok :
    forall (x:A) (n:nat), binary_power x n = x ** n.
  Proof.
    intros n x; unfold binary_power; rewrite binary_power_mult_ok;
    monoid_simpl; auto.
  Qed.
  About binary_power_ok.
End About_power.

(* ****************************** *)
(** 可換モノイド、アーベルモノイド *)
(* ****************************** *)
(** モノイド M に可換則を追加して得られる。 *)
Class Abelian_Monoid `(M : Monoid ):=
  {
    dot_comm : forall x y, dot x y = dot y x
  }.
Print Abelian_Monoid.

(**
ZMult_Abelian は、
ZMultモノイド（整数積のモノイド）に可換則を追加したもの。
 *)
Instance ZMult_Abelian : Abelian_Monoid ZMult.
Proof.
  split. 
  exact Zmult_comm.
Qed.

(*************************************)
(* (x * y)^n = x^n * y^n を証明する。 *)
(*************************************)
Section Power_of_dot.
  Context `{M : Monoid A} {AM : Abelian_Monoid M}.
 
  Theorem power_of_mult :
    forall n x y, power (dot x y)  n =  dot (power x n) (power y n). 
  Proof.
    induction n; simpl.
    rewrite one_left; auto.
    intros; rewrite IHn; repeat rewrite dot_assoc.
    rewrite <- (dot_assoc x y (power x n)); rewrite (dot_comm y (power x n)).
    repeat rewrite dot_assoc; trivial.
  Qed.
End Power_of_dot.

(* END *)
