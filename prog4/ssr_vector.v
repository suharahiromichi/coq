(**
依存マッチで証明を進める方法

http://www.a-k-r.org/pub/2025-06-28-akr-proof-summit-2025.pdf
 *)
From mathcomp Require Import all_ssreflect.
Import EqNotations.                         (* rew *)
Require Import JMeq.                        (* JMeq *)
Require Import Coq.Program.Equality.        (* dependent destruction *)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(*
# 説明：

## match 式を生成するtactic
- ○ dependent destruction .......... JMeq による等式の生成 (公理が必要)
  (Lean) cases ..................... HEq (Lean)
- ○ refine (match ....)............. rew を使った等式の生成（連立方程式を生成）
- depelim (Equations パッケージ) ... sigma 型を使った等式の生成

## JMeq を使う。
- JMeq を eq に変換するには、UIP 公理が必要である。

## matchで連立方程式を生成する。
- rew記法を使用する。
- 解が存在する場合
  - deletion
  - injectivity .... no confusion 補題を使用する。
  - solution
*)

(**
# nat についての no confusion 補題 p.43
 *)
Definition Noconf_nat (m n : nat) : Prop :=
  match m, n with
  | 0, 0 => True
  | m'.+1, n'.+1 => m' = n'
  | _, _ => False
  end.

Definition noconf_nat {m n} : Noconf_nat m n -> m = n.
  case: m; case: n => //; by move=> m n <-.
Defined.

Definition noconf_nat_inv {m n} : m = n -> Noconf_nat m n.
  case: m; case: n => //; by move=> m n <-.
Defined.

Definition noconf_natK {m n} (H : m = n) :
  noconf_nat (noconf_nat_inv H) = H.
  case: m H => [|m] H; by subst n.
Defined.
(* end, no confusion *)

(**
# 長さを型に持つリスト: vec 型 p.44
 *)
(*             パラメータ  インデックス *)
Inductive vec (A : Type) : nat -> Type :=
| vnil  : vec A 0
| vcons : A -> forall (n : nat), vec A n -> vec A n.+1.

Check vnil : forall A : Type, vec A 0.
Check vcons : forall A : Type, A -> forall n : nat, vec A n -> vec A n.+1.

(**
# 長さが1 以上のvec はvcons で作られたものである、という定理の証明 p.45
*)
Lemma vec_caseS : forall (A : Type) (n : nat) (v : vec A n.+1) (P : vec A n.+1 -> Type),
    (forall (h : A) (t : vec A n), P (@vcons A h n t)) -> P v.
Proof.
  move=> A n v P H.
  
  (* JMeq を使用する。 *)
  by dependent destruction v.
  Undo 1.
  
  (* 連立方程式の生成 *)
  refine (
      match v as v' in vec _ m return
            forall (Hn : n.+1 = m) (Hv : rew Hn in v = v'), P v with
      | vnil => _
      | vcons x n' t => _
      end erefl erefl).
  (* rew を使った等式を生成する。 *)
  
  (* vnil の場合の証明*)
  - by [].
    
  (* vcons の場合の証明*)
  - move=> Hn.
    (* injectivity でn.+1 = n'.+1 をn = n' にする*)
    rewrite -(noconf_natK Hn).
    (* solution でn = n' のn' を除去する*)
    destruct (noconf_nat_inv Hn).
    simpl.
    move=> ->.
    by apply H.
Defined.

(* END *)
