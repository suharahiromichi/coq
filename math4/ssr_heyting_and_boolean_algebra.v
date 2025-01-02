(**
lean-by-example/LeanByExample/Tutorial/Exercise/HeytingAndBooleanAlgebra.lean
 *)

From mathcomp Require Import all_ssreflect.
From mathcomp Require Import zify ring lra.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Module three.

  Definition Three := 'I_3.

  Definition t0 := @Ordinal 3 0 is_true_true.
  Definition t1 := @Ordinal 3 1 is_true_true.
  Definition t2 := @Ordinal 3 2 is_true_true.

  (* 上限 \/ ∨ ⊔ *)
  Definition sup a b := maxn a b.

  (* 下限 /\ ∧ ⊓ *)
  Definition inf a b := minn a b.

  (* 最大元 T ⊤ *)
  Definition top := t2.
  
  (* 最小元 ⊥ *)
  Definition bot := t0.

  (* 含意 *)
  Definition himp (a b : Three) := if a <= b then top else b.
  
  (* 補元 *)
  Definition compl (a : Three) := if a == bot then top else bot.
  
  (* テスト *)
  
  (* 最大元の条件 *)
  Compute t0 <= top.                        (* true *)
  Compute t1 <= top.                        (* true *)
  Compute t2 <= top.                        (* true *)

  (* 最小元の条件 *)
  Compute bot <= t0.                        (* true *)
  Compute bot <= t1.                        (* true *)
  Compute bot <= t2.                        (* true *)
  
  (* 含意の計算 *)
  Compute himp t0 t1 == top.                (* true *)
  Compute himp t1 t2 == top.                (* true *)
  (* etc. *)
  Compute himp t1 t0 == t0.                 (* true *)
  Compute himp t2 t0 == t0.                 (* true *)
  Compute himp t2 t1 == t1.                 (* true *)
  
  (* 含意の条件 *)
  (** ``· ⊓ b` の右随伴 `b ⇨ ·`` が存在する。 *)
  (* a <= (b -> c)  ==  a /\ b <= c *)
  Compute (top <= himp t0 t1) == (inf top t0 <= t1). (* t0 -> t1 *)
  Compute (top <= himp t1 t2) == (inf top t1 <= t2). (* t1 -> t2 *)
  Compute (t0  <= himp t1 t0) == (inf t0  t1 <= t0). (* t1 -> t0 *)
  Compute (t0  <= himp t2 t0) == (inf t0  t2 <= t0). (* t2 -> t0 *)
  Compute (t1  <= himp t2 t1) == (inf t0  t2 <= t1). (* t2 -> t1 *)    

  (* 補元の計算 *)
  Compute compl t0 == t2.                   (* true *)
  Compute compl t1 == t0.                   (* true *)
  Compute compl t2 == t0.                   (* true *)
  
  (* 補元の条件、a \/ a^c = top は成り立たない。ここでは補元の存在だけを言う。 *)
  Compute himp t0 bot == compl t0.        (* true *)
  Compute himp t1 bot == compl t1.        (* true *)
  Compute himp t2 bot == compl t2.        (* true *)

  (* 証明 *)
  
  (* 便利な補題 *)
  Lemma sup_top (a : Three) : sup top a = top.
  Proof.
    apply: maxn_idPl.
    by case: a.
  Qed.
  
  Lemma sup_bot (a : Three) : sup bot a = a.
  Proof.
    apply: maxn_idPr.
    by case: a.
  Qed.
  
  Lemma inf_top (a : Three) : inf top a = a.
  Proof.
    apply: minn_idPr.
    by case: a.
  Qed.
  
  Lemma inf_bot (a : Three) : inf bot a = bot.
  Proof.
(*
    rewrite /inf.
    by rewrite minnC minn0.
    Restart.
*)
    apply: minn_idPl.
    by case: a.
  Qed.
  
  (* 最大元の条件 *)  
  Goal forall (a : Three), a <= top.
  Proof.
    by case.
  Qed.
  
  (* 最小元の条件 *)  
  Goal forall (a : Three), bot <= a.
  Proof.
    by case.
  Qed.
  
  (* 含意の条件 *)  
  Goal forall (b c : Three), exists a, (a <= himp b c) == (inf a b <= c).
  Proof.
    move=> b c.
    rewrite /himp /compl.
    case H : (b <= c).
    - exists top.
      by rewrite inf_top.
    - exists bot.
      by rewrite inf_bot.
  Qed.
  
  (* 補元の条件 *)
  Goal forall (a : Three), himp a bot == compl a.
  Proof.
    move=> a.
    rewrite /himp /compl.
    Check leqn0 : forall n : nat, (n <= 0) = (n == 0).
    by rewrite leqn0.
  Qed.
  
  (* 補元の不在の証明、ブール束でないことの証明 *)
  (* 1 ⊔ 1ᶜ ≠ ⊤ *)
  Compute sup t1 (compl t1) == t1.          (* true *)
  Goal sup t1 (compl t1) != top.
  Proof.
    done.
  Qed.
  
End three.

Compute three.t0.
Compute three.sup three.t0 three.t1.        (* 1 *)
Compute three.sup three.t0 three.t1 == three.t1. (* true *)


(* END *)
