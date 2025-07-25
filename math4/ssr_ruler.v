(**
無限長2進数とルーラー関数
*)
From mathcomp Require Import all_ssreflect.
From mathcomp Require Import all_algebra.
From mathcomp Require Import ssrZ zify ring lra.
From Equations Require Import Equations.
Import Arith.                               (* Nat.land_spec *)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GRing.Theory.                        (* ssralg.v *)
Import Num.Def Num.Theory.                  (* ssrnum.v *)
Import intZmod.

Open Scope ring_scope.

(**
# 無限長2進数の世界

2進数でも任意の自然数・整数・有理数を表現できる。
補数表現は、有限の桁数（8ビットで256を法とするなど）に限らない。

…1111111.      = -1    小数点が右端
.1111111…      = 1     小数点が左端
…111.111…      = 0     小数点が途中 (2進実数)

 *)

(**
# 問題 ``x & (- x)`` の意味

結城浩「数学ガールの秘密のノート ビットとバイナリー」
*)

(**
# mathcomp の ssrint
*)

Print int.
(*
Variant int : Set :=
| Posz : nat -> int
| Negz : nat -> int.
*)

Goal forall (m : nat), Negz m = - m.+1%:Z.
Proof.
  done.
Qed.

Goal forall (m : nat), (0 < m)%nat -> Negz m.-1 = - m%:Z.
Proof.
  by case.
Qed.

Compute Posz 2.                             (* = 2%Z *)
Compute Posz 1.                             (* = 1%Z *)
Compute Posz 0.                             (* = 0%Z *)
Compute Negz 0.                             (* = (-1)%Z *)
Compute Negz 1.                             (* = (-2)%Z *)
Compute Negz 2.                             (* = (-3)%Z *)

(**
## oppz (- x)
*)

Section opp_test.
  Variable n : nat.
  Print oppz.
  
  Compute oppz (Posz 0).                    (* = 0%Z *)
  Compute oppz (Posz n.+1).                 (* = Negz n *)
  Compute oppz (Negz n).                    (* = Posz n.+1 *)
End opp_test.

(**
# Standard coq (PeanoNat の bitwise 計算
 *)
Print Nat.testbit.
(*
fix testbit (a n : nat) {struct n} : bool :=
  match n with
  | 0%N => Nat.odd a
  | n0.+1 => testbit (Nat.div2 a) n0
  end
     : nat -> nat -> bool
*)

Check Nat.land_spec
  : forall a b n : nat, Nat.testbit (Nat.land a b) n = Nat.testbit a n && Nat.testbit b n.
Check Nat.lor_spec
  : forall a b n : nat, Nat.testbit (Nat.lor a b) n = Nat.testbit a n || Nat.testbit b n.
Check Nat.lxor_spec
  : forall a b n : nat, Nat.testbit (Nat.lxor a b) n = xorb (Nat.testbit a n) (Nat.testbit b n).
Check Nat.ldiff_spec
  : forall a b n : nat, Nat.testbit (Nat.ldiff a b) n = Nat.testbit a n && ~~ Nat.testbit b n.
Fail Check Nat.lnor.                        (* これは無い。 *)

(**
# 2進整数のbitwise計算
*)

Section bitwise.
(**
## not

自然数の not (ビットワイズの反転) は定義できないが、
整数の not は定義できる。
*)
  Equations lnot (x : int) : int :=
    lnot (Posz n) := Negz n;
    lnot (Negz n) := Posz n.
  
  Compute lnot 2.                           (* = (-3)%Z *)
  Compute lnot 1.                           (* = (-2)%Z *)
  Compute lnot 0.                           (* = (-1)%Z *)
  Compute lnot (-1).                        (* = 0%Z *)
  Compute lnot (-2).                        (* = 1%Z *)
  Compute lnot (-3).                        (* = 2%Z *)
  
  Equations lor (x y : int) : int :=
    lor (Posz m) (Posz n) := Posz (Nat.lor m n);
    lor (Posz m) (Negz n) := Negz (Nat.ldiff n m);
    lor (Negz m) (Posz n) := Negz (Nat.ldiff m n);
    lor (Negz m) (Negz n) := Negz (Nat.land m n).

  (* Leanを参考にして定義する。 *)
  Variable land : int -> int -> int.
  Variable lxor : int -> int -> int.
  Variable ldiff : int -> int -> int.


(**
ただし、testbit 関数を次のように定義できる。
*)
  Equations testbit (x : int) (n : nat) : bool :=
    testbit (Posz n) m := Nat.testbit n m ;
    testbit (Negz n) m := ~~ Nat.testbit n m.
  Check testbit_equation_1: forall n m : nat, testbit n m = Nat.testbit n m.
  Check testbit_equation_2: forall n m : nat, testbit (Negz n) m = ~~ Nat.testbit n m.
  
  Notation ".~ x" := (lnot x) (at level 35).
  Notation "x .& y" := (land x y) (at level 50).
  Notation "x .| y" := (lor x y) (at level 50).
  Notation "x .^ y" := (lxor x y) (at level 30).
  Notation "x .[ i ]" := (testbit x i).
  
  Lemma lor_spec (x y : int) (i : nat) : (x .| y).[i] = x.[i] || y.[i].
  Proof.
    case: x; case: y => m' n';
                        rewrite ?testbit_equation_1 ?testbit_equation_2.
    - by rewrite Nat.lor_spec.
    - rewrite Nat.ldiff_spec.
      by rewrite negb_and negbK orbC.
    - rewrite Nat.ldiff_spec.
      by rewrite negb_and negbK orbC.
    - rewrite Nat.land_spec.
      by rewrite negb_and.
  Qed.
  
  Axiom land_spec  : forall (x y : int) (i : nat), (x .& y).[i] = x.[i] && y.[i].
  Axiom lxor_spec  : forall (x y : int) (i : nat), (x .^ y).[i] = xorb (x.[i]) (y.[i]).
  Axiom ldiff_spec : forall (x y : int) (i : nat), (ldiff x y).[i] = x.[i] && ~~ y.[i].

(**
# 問題をPeanNatの問題にする
 *)

  Definition prog (x : int) := x .& (- x).

  Lemma prog_0 i : (prog 0).[i] = false.
  Proof.
    rewrite land_spec testbit_equation_1.
    now rewrite Nat.bits_0.
  Qed.
  
  Lemma prog_pos n i : (prog (Posz n.+1)).[i] = Nat.testbit n.+1 i && ~~ Nat.testbit n i.
  Proof.
    rewrite land_spec.
    done.
  Qed.

  Lemma prog_neg n i : (prog (Negz n)).[i] = ~~ Nat.testbit n i && Nat.testbit n.+1 i.
  Proof.
    rewrite land_spec.
    done.
  Qed.
  
(**
# ルーラー関数
*)
  Equations log2 (x : int) : nat :=
    log2 (Posz n) := Nat.log2 n;
    log2 (Negz _) := 0.
  Compute log2 0%Z.                         (* = 0%N *)
  
  Definition ruler (n : nat) := log2 (n%:Z .& (- n%:Z)).
  
  Definition ruler' (n : nat) := log2 (n%:Z .^ n.-1%:Z).
  
  Equations ruler_rec (n : nat) : nat by wf n :=
    ruler_rec 0 => 0 ;
    ruler_rec n.+1 with odd n.+1 => {
      | true  => 0 ;
      | false => (ruler_rec n.+1./2).+1
      }.
  Obligation 1.
  apply/ltP.
  rewrite ltn_uphalf_double -muln2.
  by apply: ltn_Pmulr.
  Qed.

  Example test (n : nat) := (ruler n = ruler_rec n).
  Example test' (n : nat) := (ruler' n = ruler_rec n).
  Example test2 (n : nat) := (ruler n = ruler' n).

(*
  Goal test2 0. Proof. done. Qed.
  Goal test2 1. Proof. done. Qed.
  Goal test2 2. Proof. done. Qed.
  Goal test2 3. Proof. done. Qed.
  Goal test2 4. Proof. done. Qed.
  Goal test2 5. Proof. done. Qed.
  Goal test2 6. Proof. done. Qed.
  Goal test2 7. Proof. done. Qed.
  Goal test2 8. Proof. done. Qed.
  
  Compute ruler' 0.
  Compute ruler' 1.
  Compute ruler' 2.
  Compute ruler' 3.
  Compute ruler' 4.
  Compute ruler' 5.  
  Compute ruler' 7.  
  Compute ruler' 8.  
*)  

  Compute ruler_rec 0.
  Compute ruler_rec 1.
  Compute ruler_rec 2.
  Compute ruler_rec 3.
  Compute ruler_rec 4.
  Compute ruler_rec 5.  
  Compute ruler_rec 7.  
  Compute ruler_rec 8.  

End bitwise.
  
(**
# 補足説明

## Standard Coq

- NArith/BinNatDef.v
- ZArith/BinInt.v       ZArith/Zbitwise.v


## Lean

- Mathlib/Data/Num/Bitwise.lean
- Mathlib/Data/Int/Bitwise.lean

Negz にあたるコンストラクタは neg_succ_of_nat という

``-[ ・ +1]`` または ``-[1+ ・ ]`` というノーテーション

*)

(* END *)
