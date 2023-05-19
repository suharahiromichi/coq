(**
MathComp2 整数とガウス整数の定義

https://perso.crans.org/cohen/JFLA23/lesson2.v
 *)

From elpi Require Import elpi.
From HB Require Import structures.
From mathcomp Require Import all_ssreflect.
From mathcomp Require ssralg ssrnum zmodp. (* all_algebra *)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import ssralg GRing.Theory.
Local Open Scope ring_scope.

(**
# 整数 int
*)
Module InstantiationInteger.

  Variant int : Set := Posz of nat | Negz of nat.
  Local Coercion Posz : nat >-> int.

  Notation "n %:Z" := (Posz n)(at level 2, left associativity, format "n %:Z", only parsing).
  
  Definition natsum_of_int (m : int) : nat + nat :=
    match m with
    | Posz p => inl _ p
    | Negz n => inr _ n
    end.
  
  Definition int_of_natsum (m : nat + nat) :=
    match m with
    | inl p => Posz p
    | inr n => Negz n
    end.

  Lemma natsum_of_intK : cancel natsum_of_int int_of_natsum.
  Proof. by case. Qed.

  HB.instance Definition _ : hasDecEq int := CanEqMixin natsum_of_intK.
  HB.instance Definition _ : hasChoice int := CanChoiceMixin natsum_of_intK.
  HB.instance Definition _ : isCountable int := CanCountMixin natsum_of_intK.

  (* Advanced way of doing it one go:
  HB.instance Definition _ :=
    Countable.copy int (can_type natsum_of_intK).
   *)

  Module intZmod.
    Section intZmod.
      
      HB.howto int zmodType.
      (* HB: solutions (use 'HB.about F.Build' to see the arguments of each factory F):
         - GRing.isZmodule
         - GRing.isNmodule; GRing.Nmodule_isZmodule
       *)
      
      HB.about GRing.isZmodule.Build.
      (* HB: arguments: GRing.isZmodule.Build V [zero] [opp] [add] addrA addrC add0r addNr
        - V : Type
        - zero : GRing.Zmodule.sort V
        - opp : V -> V
        - add : V -> V -> V
        - addrA : associative +%R
        - addrC : commutative +%R
        - add0r : left_id 0 +%R
        - addNr : left_inverse 0 -%R +%R
        *)
      
      Definition addz (m n : int) :=
        match m, n with
        | Posz m', Posz n' => Posz (m' + n')
        | Negz m', Negz n' => Negz (m' + n').+1
        | Posz m', Negz n' => if n' < m' then Posz (m' - n'.+1)
                              else Negz (n' - m')
        | Negz n', Posz m' => if n' < m' then Posz (m' - n'.+1)
                              else Negz (n' - m')
        end.

      Definition oppz m :=
        match m with
        | Posz n => if n is (n'.+1)%N then Negz n' else Posz 0
        | Negz n => Posz (n.+1)%N
        end.
      Lemma addzC : commutative addz. Admitted.
      Lemma add0z : left_id (Posz 0) addz. Admitted.
      Lemma oppzK : involutive oppz. Admitted.
      Lemma addzA : associative addz. Admitted.
      Lemma addNz : left_inverse (Posz 0) oppz addz. Admitted.

      Definition Mixin := GRing.isZmodule.Build int addzA addzC add0z addNz.
    End intZmod.
  End intZmod.

  HB.instance Definition _ := intZmod.Mixin.
  Check (int : zmodType).

  Lemma PoszD : {morph Posz : n m / (n + m)%N >-> n + m}.
  Proof. by []. Qed.

  Module intRing.
    Section intRing.
      
      HB.howto int comRingType.
      (* HB: no solution found at depth 3 looking at depth 4
        HB: solutions (use 'HB.about F.Build' to see the arguments of each factory F):
        - hasDecEq; hasChoice; GRing.isRing; GRing.Ring_hasCommutativeMul
        - hasDecEq; hasChoice; GRing.isZmodule; GRing.Zmodule_isComRing *)

      HB.about GRing.Zmodule_isComRing.Build.
      (* HB: arguments: GRing.Zmodule_isComRing.Build R [one] [mul] mulrA mulrC mul1r mulrDl oner_neq0
         - R : Type
         - one : R
         - mul : R -> R -> R
         - mulrA : associative mul
         - mulrC : commutative mul
         - mul1r : left_id one mul
         - mulrDl : left_distributive mul +%R
         - oner_neq0 : is_true (one != 0) *)

      Definition mulz (m n : int) :=
        match m, n with
        | Posz m', Posz n' => (m' * n')%N%:Z
        | Negz m', Negz n' => (m'.+1%N * n'.+1%N)%N%:Z
        | Posz m', Negz n' => - (m' * (n'.+1%N))%N%:Z
        | Negz n', Posz m' => - (m' * (n'.+1%N))%N%:Z
        end.
      Lemma mulzA : associative mulz. Admitted.
      Lemma mulzC : commutative mulz. Admitted.
      Lemma mul1z : left_id (Posz 1) mulz. Admitted.
      Lemma mulz_addl : left_distributive mulz (+%R). Admitted.
      Lemma onez_neq0 : (Posz 1) != 0. Proof. by []. Qed.

      Definition comMixin := GRing.Zmodule_isComRing.Build int mulzA mulzC mul1z mulz_addl onez_neq0.
    End intRing.
  End intRing.

  HB.instance Definition _ := intRing.comMixin.
  Check (int : ringType).
  Check (fun x : int => x + x).
  Check (@addr0 int).
  Check (int : comRingType).

End InstantiationInteger.

(**
# ガウス整数 GI
*)
Section GaussianIntegers.
(**
- 代数的定義
*)
  From mathcomp Require Import algC ssrint ssrnum.
  Import Num.Theory.

  Definition gaussInteger := [pred x : algC | ('Re x \in Cint) && ('Im x \in Cint)].
  HB.about GRing.isSubringClosed.
  Print GRing.subring_closed.

  Lemma GI_subring : GRing.isSubringClosed _ gaussInteger.
  Proof.
    split; split=> [|x y /andP[? ?] /andP[? ?]|x y /andP[? ?] /andP[? ?]].
    - by rewrite inE (Creal_ReP _ _)// (Creal_ImP _ _)// Cint1 Cint0.
    - by rewrite inE !raddfB /= ?rpredB.
      by rewrite inE ReM ImM rpredB ?rpredD // rpredM.
  Qed.
  HB.instance Definition _ := GI_subring.

(**
- sigma type
*)
  Record GI := GIof { algGI : algC; algGIP : algGI \in gaussInteger }.
  Hint Resolve algGIP.

  HB.instance Definition _ := [isSub for algGI].
  HB.instance Definition _ := [Choice of GI by <:].

  Fail Check (forall x y : GI, x + y = y + x).
  HB.instance Definition _ := [SubChoice_isSubComRing of GI by <:].
  Check (GI : comRingType).
  Check (forall x y : GI, x + y = y + x).

End GaussianIntegers.

(* END *)
