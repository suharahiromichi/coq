(**
A Gentle Introduction to Type Classes and Relations in Coq
の
Chapter 2 An Introductory Example: Computing xn
の抜萃。
@suharahiromichi
*)

(**
配布ファイル typeclassesTut を make したのち、
そのディレクトリの本ファイルを置いて実行する。
なお、typeclassesTut を make には、
cp V8.3/Matrics.v Mat.v して、Section名をMatに修正する。
Makefileの _CoqProject のエントリを消す。
*)

(*
A variation of Monoid.v, using Program Fixpoint instead of Function *)

(**
これは、typeclassesTut/Monoid_prog.v をもとにしている。
Program Fixpoint を使い、Contextコマンドを使っている。*)

Set Implicit Arguments.

Require Import ZArith.
Require Import Div2.
Require Import Program.
(* typeclassesTut/V8.3/Matrics.v をrenameする。Section名も。 *)
Require Import Mat.

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
Print Monoid.
About one_left.
About one_right.

Require Import ZArith.
Open Scope Z_scope.

(**
ZMultは、モノイド (Z,*,1) である。
- 台は、Z (Implicit)
- 二項演算は、Zmult
- 単位元は、1
*)
(* Compute binary_power 2 100. で使われる。 *)
Instance ZMult : Monoid Zmult 1.
Proof.
  split; intros; ring.
Qed.
Check ZMult : Monoid Z.mul 1.

(* おまけ。 *)
Instance Mult : Monoid mult 1%nat.
Proof.
  split; intros.
  now rewrite mult_assoc.
  now rewrite mult_1_l.
  now rewrite mult_1_r.
Qed.
Check Mult :  Monoid mult 1%nat.

(*
Fixpoint power {A : Type} {dot : A -> A -> A} {one : A} {M : Monoid dot one}
         (a : A)(n : nat) :=
  match n with
    | 0%nat => one
    | S p => dot a (power a p)
  end.
Compute power 2 10.
Reset power.
*)

Generalizable Variables A dot one.
(**
Coq Reference Manual から
2.7.20 Implicit generalization

Implicit generalization is an automatic elaboration of a statement with free variables
into a closed statement where these variables are quantified explicitly. Implicit
generalization is done inside binders starting with a ` and terms delimited by `{} and
`(), always introducing maximally inserted implicit arguments for the generalized
variables. Inside implicit generalization delimiters, free variables in the current
context are automatically quantified using a product or a lambda abstraction to generate a
closed term. In the following statement for example, the variables n and m are
autamatically generalized and become explicit arguments of the lemma as we are using `():
*)
(* `{} は、引数を{}で囲むのときと同様に implicit argument になる。 *)

Fixpoint power `{M : Monoid A dot one} (a : A) (n : nat) :=
  match n with
    | 0%nat => one
    | S p => dot a (power a p)
  end.

Section binary_power. 
  Context `{M : Monoid A dot one}.
(**
Coq Reference Manual から
19.4  Sections and contexts

To ease the parametrization of developments by type classes, we provide a new way to
introduce variables into section contexts, compatible with the implicit argument
mechanism. The new command works similarly to the Variables vernacular (see 1.3.1), except
it accepts any binding context as argument.
*)  
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
    set (M' := M); apply lt_div2; auto with arith.
    Defined.
  Next Obligation.                          (* Obligation 2 と 3 *)
    set (M' := M); apply lt_div2; auto with arith.
    Defined.
  Check binary_power_mult.
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
            ltac : (fun c => 
                      unfold_sub @binary_power_mult_func c;
                    fold binary_power_mult_func).
    simpl. destruct n; reflexivity.
  Qed.
End binary_power.

Definition binary_power `{M : Monoid A dot one} x n :=
  binary_power_mult one x n.

(************************************)
(* First example : モノイド (Z,*,1) *)
(************************************)
(* ZMult をここで使う。 *)
Compute binary_power 2 100.
(* = 1267650600228229401496703205376 : Z *)

Goal forall n : Z, 1 * (n * 1) = n.
Proof.
  intro n.
  rewrite one_left.
  rewrite one_right.
  trivial.
Save XX.                                    (* Lemma XXX : ... Qed. とおなじ。 *)

(***********************************)
(* Second example : 2 x 2 Matrices *)
(***********************************)
(* M2 と M2_mult と Id2 と M2_eq_intros は、Mat.v で定義 *)
Section M2_def.
  Variables (A : Type)
            (zero one : A) 
            (plus : A -> A -> A)            (* (plus mult minus : A->A->A) *)
            (mult : A -> A -> A)
            (minus : A -> A -> A)
            (sym : A -> A).
  Notation "0" := zero.
  Notation "1" := one.
  Notation "x + y" := (plus x y).  
  Notation "x * y" := (mult x y).
  Variable rt : ring_theory  zero one plus mult minus sym (@eq A).
  Add Ring Aring : rt.

(**
M2_Monoidは、以下のモノイドである。
- 台は M2 Z、Z の 2×2の行列
- 二項演算は、 
c00 := plus (mult (c00 m) (c00 m')) (mult (c01 m) (c10 m'));
c01 := plus (mult (c00 m) (c01 m')) (mult (c01 m) (c11 m'));
c10 := plus (mult (c10 m) (c00 m')) (mult (c11 m) (c10 m'));
c11 := plus (mult (c10 m) (c01 m')) (mult (c11 m) (c11 m'))
- 単位元は、
c00 := one; c01 := zero; c10 := zero; c11 := one
*)

  Check M2_mult : forall A : Type, (A -> A -> A) -> (A -> A -> A) -> M2 A -> M2 A -> M2 A.
  (* (plus : A -> A -> A) (mult : A -> A -> A) *)
  Check M2_mult plus mult : M2 A -> M2 A -> M2 A. (* dot *)
  
  Check Id2     : forall A : Type, A -> A -> M2 A. (* (zero : A) (one : A) *)
  Check Id2 0 1 : M2 A.                            (* one *)
  
  Global Instance M2_Monoid : Monoid (M2_mult plus mult) (Id2 0 1).
  Proof.
    split.
    destruct x; destruct y; destruct z; simpl.
    unfold M2_mult; apply M2_eq_intros; simpl; ring.
    destruct x; simpl;
    unfold M2_mult; apply M2_eq_intros; simpl; ring.
    destruct x; simpl; unfold M2_mult; apply M2_eq_intros; simpl; ring. 
  Qed.
End M2_def.

Check M2_mult Z.add Z.mul : M2 Z -> M2 Z -> M2 Z. (* dot *)
Check Id2 0 1 : M2 Z.                             (* one *)
Check M2_Monoid.
Check Zth : ring_theory 0 1 Z.add Z.mul Z.sub Z.opp eq.

Instance M2Z : Monoid _ _ := M2_Monoid Zth.
Check M2Z : Monoid (M2_mult Z.add Z.mul) (Id2 0 1).
Check ZMult : Monoid Z.mul 1.                (* 比較 *)

Compute power (Build_M2 1 1 1 0) 40.         (* M2Z をつかう。 *)
(*
行列の掛け算を40回繰り返す。
[1 1]  [1 1]  [1 1] ..... [1 1]  
[1 0]  [1 0]  [1 0]       [1 0]
c00 := 165580141;
c01 := 102334155;
c10 := 102334155;
c11 := 63245986
*)

Definition fibonacci (n:nat) :=
  c00 (power (Build_M2  1 1 1 0) n).
Compute fibonacci 20.
Compute (c00 (power (Build_M2  1 1 1 0) 20)).

(** 一般的事項を証明する。 *)
(* Generic study of power functions *)
(** 最終的に、power と binary_power が等価なことを証明する。 *)
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
About binary_power_ok.

Implicit Arguments binary_power_ok [A dot one M].
About binary_power_ok.

Check binary_power_ok 2 20.

Let Mfib := Build_M2 1 1 1 0.
Check binary_power_ok Mfib 56.

Check binary_power_ok (Build_M2 1 1 1 0) 40.
Eval vm_compute in power 2 5.

(** 可換モノイド、アーベルモノイド *)
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

(**
おまけとして (x * y)^n = x^n * y^n を証明する。
*)
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

Check power_of_mult 3 4 5.
(* : power (4 * 5) 3 = power 4 3 * power 5 3 *)

Check power (Build_M2  1 1 1 0) 3.
Compute power (Build_M2 1 1 1 0) 3.
Check power_of_mult 3 (Build_M2  1 1 1 0) (Build_M2  1 1 1 0).
(* dot が ?204 のままなのは、なぜだろう。 *)

(* END *)
