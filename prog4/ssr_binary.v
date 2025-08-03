(**
整数版のビット計算
 *)

From mathcomp Require Import all_ssreflect.
From mathcomp Require Import all_algebra.
From mathcomp Require Import ssrZ zify ring lra.
(* opam install coq-equations *)
From Equations Require Import Equations.
Import Arith.                               (* Nat.land_spec *)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GRing.Theory.                        (* ssralg.v *)
Import Num.Def Num.Theory.                  (* ssrnum.v *)
Import intZmod.

Open Scope ring_scope.

Section a.

  (**
## 整数版のビット計算
   *)
  Equations lnot (x : int) : int :=
    lnot (Posz n) := Negz n;
    lnot (Negz n) := Posz n.

  Equations land (x y : int) : int :=
  land (Posz m) (Posz n) := Posz (Nat.land m n);  (* x & y *)
  land (Posz m) (Negz n) := Posz (Nat.ldiff m n); (* x & ~ ~y *)
  land (Negz m) (Posz n) := Posz (Nat.ldiff n m); (* ~ ~x & y *)
  land (Negz m) (Negz n) := Negz (Nat.lor m n).   (*  ~(~x | ~y) *)
  
  Equations lor (x y : int) : int :=
    lor (Posz m) (Posz n) := Posz (Nat.lor m n);   (* x | y *)
    lor (Posz m) (Negz n) := Negz (Nat.ldiff n m); (* ~(~x & ~ y) *)
    lor (Negz m) (Posz n) := Negz (Nat.ldiff m n); (* ~(~ x & ~y) *)
    lor (Negz m) (Negz n) := Negz (Nat.land m n).  (* ~(~x & ~y) *)
  (* simp lor で以下のrewrite ができる。 *)
  Check lor_equation_1 : forall m n : nat, lor m n = Nat.lor m n.
  Check lor_equation_2 : forall m n : nat, lor m (Negz n) = Negz (Nat.ldiff n m).
  Check lor_equation_3 : forall m n : nat, lor (Negz m) n = Negz (Nat.ldiff m n).
  Check lor_equation_4 : forall m n : nat, lor (Negz m) (Negz n) = Negz (Nat.land m n).

  Equations ldiff (x y : int) : int :=
    ldiff (Posz m) (Posz n) := Posz (Nat.ldiff m n); (* x & ~ y *)
    ldiff (Posz m) (Negz n) := Posz (Nat.land m n); (* x & ~ ~y = x & y *)
    ldiff (Negz m) (Posz n) := Negz (Nat.lor m n);  (* ~x & ~ y = ~(x | y) *)
    ldiff (Negz m) (Negz n) := Posz (Nat.ldiff n m). (* ~x & ~ ~y = ~ x & y *)

  Equations lxor (x y : int) : int :=
    lxor (Posz m) (Posz n) := Posz (Nat.lxor m n); (* x ^ y *)
    lxor (Posz m) (Negz n) := Negz (Nat.lxor m n); (* ~(x ^ ~y) *)
    lxor (Negz m) (Posz n) := Negz (Nat.lxor m n); (* ~(~x ^ y) *)
    lxor (Negz m) (Negz n) := Posz (Nat.lxor m n). (* ~x ^ ~y *)
  
  Equations testbit (x : int) (m : nat) : bool :=
  testbit (Posz n) m := Nat.testbit n m ;
  testbit (Negz n) m := ~~ Nat.testbit n m.
  (* simp testbit で以下のrewrite ができる。 *)
  Check testbit_equation_1: forall n m : nat, testbit n m = Nat.testbit n m.
  Check testbit_equation_2: forall n m : nat, testbit (Negz n) m = ~~ Nat.testbit n m.
  
  (**
## 演算子
   *)
  Notation ".~ x" := (lnot x) (at level 35).
  Notation "x .& y" := (land x y) (at level 50).
  Notation "x .| y" := (lor x y) (at level 50).
  Notation "x .^ y" := (lxor x y) (at level 50).
  Notation "x .[ i ]" := (testbit x i).
  Notation "a ^^ b" := (xorb a b) (at level 50).

  (**
## spec
   *)
  Lemma lnot_spec (x : int) (i : nat) : (.~ x).[i] = ~~ x.[i].
  Proof.
    case: x => n; simp lnot testbit => //=.
    by rewrite negbK.
   Qed.

  (* この証明から 2025/8/23 ProorCafe *)
  Lemma land_spec (x y : int) (i : nat) : (x .& y).[i] = x.[i] && y.[i].
  Proof.
    case: x; case: y => m n;
                        simp testbit land;
                        rewrite ?Nat.land_spec ?Nat.lor_spec ?Nat.ldiff_spec //=.
    - by rewrite andbC.
    - by rewrite negb_or.
  Qed.
  
  Lemma lor_spec (x y : int) (i : nat) : (x .| y).[i] = x.[i] || y.[i].
  Proof.
    case: x; case: y => m n;
                        simp testbit lor;
                        rewrite ?Nat.lor_spec ?Nat.land_spec ?Nat.ldiff_spec //=.
     - by rewrite negb_and negbK orbC.
     - by rewrite negb_and negbK orbC.
     - by rewrite negb_and.
   Qed.
  
  Lemma ldiff_spec (x y : int) (i : nat) : (ldiff x y).[i] = x.[i] && ~~ y.[i].
  Proof.
    case: x; case: y => m n;
                         simp testbit ldiff;
                         rewrite ?Nat.land_spec ?Nat.lor_spec ?Nat.ldiff_spec //=.
    - by rewrite negbK.
    - by rewrite negb_or.
    - by rewrite negbK andbC.
  Qed.
   
  Lemma lxor_spec (x y : int) (i : nat) : (x .^ y).[i] = xorb (x.[i]) (y.[i]).
  Proof.
    case: x; case: y => m n;
                        simp testbit lxor;
                        rewrite Nat.lxor_spec //=.
    - by rewrite Bool.negb_xorb_r.
    - by rewrite Bool.negb_xorb_l.
    - by rewrite -Bool.negb_xorb_l -Bool.negb_xorb_r negbK.
  Qed.

End a.

(* END *)
