(**
MathComp2 整数とガウス整数の定義

https://perso.crans.org/cohen/JFLA23/lesson2.v
 *)

From elpi Require Import elpi.
From HB Require Import structures.
From mathcomp Require Import all_ssreflect.
From mathcomp Require all_algebra. (* 使うところは個別に Import する必要がある。 *)
From mathcomp Require all_field.   (* 使うところは個別に Import する必要がある。 *)
Require Import Psatz.                       (* lia *)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import ssralg.
Import GRing.Theory.
Local Open Scope ring_scope.

(**
# 整数 int
*)
Module InstantiationInteger.

(* 自然数から整数を作るコンストラクタ Posz と Negz を定義する。
   Posz は自然数から整数へのコアーションにするとともに、``%:Z``という演算子を用意しておく。*)
  Variant int : Set :=
    | Posz of nat
    | Negz of nat.
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

(*
  HB.instance Definition _ : hasDecEq int := CanEqMixin natsum_of_intK.
  HB.instance Definition _ : hasChoice int := CanChoiceMixin natsum_of_intK.
  HB.instance Definition _ : isCountable int := CanCountMixin natsum_of_intK.
*)  
  (* こちらのほうが、よりMathComp2的である。 *)
  HB.instance Definition _ := Equality.copy int (can_type natsum_of_intK). (* MathComp2 *)
  HB.instance Definition _ := Choice.copy int (can_type natsum_of_intK). (* MathComp2 *)
  HB.instance Definition _ := Countable.copy int (can_type natsum_of_intK). (* MathComp2 *)
  
(**
## Z加群
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
      
      (* Negz 0 で -1 を表すようにする。すると、intの表現の一意性が保たれる。 *)
      Check Posz 1.                         (* +1 *)
      Check Posz 0.                         (* 0 *)
      Check Negz 0.                         (* -1 *)
      Check Negz 1.                         (* -2 *)
      (* この定義に基づいて、整数の加算を定義すると、以下 addz と oppz のようになる。 *)
      
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

      Definition Mixin := GRing.isZmodule.Build int addzA addzC add0z addNz. (* MathComp2 *)
    End intZmod.
  End intZmod.

  HB.instance Definition _ := intZmod.Mixin. (* MathComp2 *)
  Check (int : zmodType).

(*
PoszD は、Posz (正整数) の加算 (D) について、
自然数を加算して正整数にすることと、自然数を正整数にして加算することは等しい。
 *)
  Section intZmoduleTheory.
    
    Lemma PoszD : {morph Posz : n m / (n + m)%N >-> n + m}.
    Proof. by []. Qed.
    Check PoszD : forall x y : nat, Posz (x + y) = Posz x + Posz y.
    Check PoszD : forall x y : nat, (x + y)%:Z = x%:Z + y%:Z.
    
  End intZmoduleTheory.  
(**
## 環
 *)
  Module intRing.
    Section intRing.
      
      HB.howto int comRingType.
      (* HB: no solution found at depth 3 looking at depth 4
         HB: solutions (use 'HB.about F.Build' to see the arguments of each factory F):
         - hasDecEq; hasChoice; GRing.isRing; GRing.Ring_hasCommutativeMul
         - hasDecEq; hasChoice; GRing.isZmodule; GRing.Zmodule_isComRing
       *)

      HB.about GRing.Zmodule_isComRing.Build.
      (* HB: arguments: GRing.Zmodule_isComRing.Build R [one] [mul] mulrA mulrC mul1r mulrDl oner_neq0
         - R : Type
         - one : R
         - mul : R -> R -> R
         - mulrA : associative mul
         - mulrC : commutative mul
         - mul1r : left_id one mul
         - mulrDl : left_distributive mul +%R
         - oner_neq0 : is_true (one != 0)
       *)

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
      (* MathComp2 *)
      
    End intRing.
  End intRing.

  HB.instance Definition _ := intRing.comMixin. (* MathComp2 *)
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
## 代数的定義
*)
  Import algC.
  Import ssrint ssrnum fingroup.
  Import Num.Theory.

  Definition gaussInteger := [pred x : algC | ('Re x \in Cint) && ('Im x \in Cint)].
  HB.about GRing.isSubringClosed.           (* MathComp2 *)
  Print GRing.subring_closed.

  Lemma GI_subring : GRing.isSubringClosed _ gaussInteger.
  Proof.
    split; split=> [|x y /andP[? ?] /andP[? ?]|x y /andP[? ?] /andP[? ?]].
    - by rewrite inE (Creal_ReP _ _)// (Creal_ImP _ _)// Cint1 Cint0.
    - by rewrite inE !raddfB /= ?rpredB.
      by rewrite inE ReM ImM rpredB ?rpredD // rpredM.
  Qed.
  HB.instance Definition _ := GI_subring.   (* MathComp2 *)

(**
## sigma type
*)
  Record GI := GIof {
                   algGI : algC;
                   algGIP : algGI \in gaussInteger
                 }.
  Hint Resolve algGIP.

  HB.instance Definition _ := [isSub for algGI].    (* MathComp2 *)
  HB.instance Definition _ := [Choice of GI by <:]. (* MathComp2 *)

  Fail Check (forall x y : GI, x + y = y + x).
  HB.instance Definition _ := [SubChoice_isSubComRing of GI by <:]. (* MathComp2 *)
  Check (GI : comRingType).
  Check (forall x y : GI, x + y = y + x).   (* 可換性が成り立つ。 *)

End GaussianIntegers.

(**
# subType
 *)
From mathcomp Require Import perm.

Check tval       : forall (n : nat) (T : Type), n.-tuple T -> seq T.
Check nat_of_ord : forall n : nat, 'I_n -> nat.
Check pval       : forall T : finType, perm_type T -> {ffun T -> T}.

(* END *)
