(**
Heyting 代数と Bool 代数

# 概要

- Heything 代数のクラスを定義する。
- 3値集合が Heyting代数のインスタンスとして定義する。
- 3値集合が Bool束の公理を満たさないことを示す。

3値集合の要素 {0,1,2} からなる集合を扱う。冪集合でないことに注意してください。


# 参考

lean-by-example/LeanByExample/Tutorial/Exercise/HeytingAndBooleanAlgebra.lean

https://github.com/lean-ja/lean-by-example/blob/0fe4627860ec8bc851905bf600faafebc356e972/LeanByExample/Tutorial/Exercise/HeytingAndBooleanAlgebra.lean
 *)

(*
# 説明

ここでは、補元 compl を ``a -> bot`` で定義する。
order.v では、Heything代数を飛ばしてbool束で定義するので、``top \ a`` で定義する。

本来は真理値表を書くべきだが、bool代数では両者は同じになる：

P -> Q == ~P \/ Q
P -> F == ~P

P \ Q == P /\ ~Q
T \ Q == ~Q

しかしならがら、Heything代数を定義したいので、これから、
tbDistrLatticeType を継承した heytingAlgebraType を定義する。
このとき、compl の定義が、order.v のと別になる。
*)

(**
# 形式証明
*)
From elpi Require Import elpi.
From HB Require Import structures.
From mathcomp Require Import all_ssreflect.
From mathcomp Require Import zify ring lra.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Order.
Import Order.Theory.

(**
## Heyting Lattice の定義
*)
#[key="T"]
HB.mixin Record hasHComplement d (T : Type) of TBDistrLattice d T := {
    himpl  : T -> T -> T;
    hcompl : T -> T;
    himplE : forall (b c : T), exists (a : T), (a <= (himpl b c))%O == (meet a b <= c)%O;
    hcomplE : forall x : T, hcompl x = himpl x bottom
  }.

#[short(type="heytingAlgebraType")]
HB.structure Definition HeytingLattice d := {
    T of hasHComplement d T & TBDistrLattice d T
  }.

Reserved Notation "A --> B" (at level 50, left associativity).
Notation "x --> y" := (himpl x y) : order_scope.

Reserved Notation "~~~ A" (at level 35, right associativity).
Notation "~~~ x" := (hcompl x) : order_scope.

(**
## 3値集合の定義

### 3値集合がOrderであること
*)
Module Three.
Section Three.

  Local Open Scope order_scope.
  
  Definition Three := 'I_3.

  Definition t0 := @Ordinal 3 0 is_true_true.
  Definition t1 := @Ordinal 3 1 is_true_true.
  Definition t2 := @Ordinal 3 2 is_true_true.

  Fact three_display : unit. Proof. exact: tt. Qed.

  HB.instance Definition _ := Choice.copy Three 'I_3. (* これが必要！！ *)
(*
  Section PossiblyTrivial.
    Variable (n : nat).
    
    HB.instance Definition _ := [SubChoice_isSubOrder of 'I_n by <: with three_display].

    Lemma leEord : (le : rel Three) = leq. Proof. by []. Qed.
    Lemma ltEord : (lt : rel Three) = (fun m n => m < n)%N. Proof. by []. Qed.
  End PossiblyTrivial.
*)
  Check leEord : forall n : nat, <=%O = (fun m n0 : 'I_n => (m <= n0)%N).
  Check ltEord : forall n : nat, <%O = (fun m n0 : 'I_n => (m < n0)%N).

  Definition three_leq (x y : Three) := (x <= y)%N.
  Definition three_ltn (x y : Three) := (x < y)%N.
  
  (* minn にすると、Three -> Three -> nat になる。 *)
  (* これは、Three -> Three -> Three でなければならないので自作する。 *)
  Definition three_minn (x y : Three) := if (x < y)%N then x else y.
  
  Definition three_maxn (x y : Three) := if (x < y)%N then y else x.
  
  Lemma ltn_def x y : (x < y)%N = (y != x)%N && (x <= y)%N.
  Proof. by rewrite ltn_neqAle eq_sym. Qed.
  
  Lemma three_meet_def (x y : Three) : three_minn x y = if (x < y)%N then x else y.
  Proof.
    (* by case: x y => [] []. *)
    done.
  Qed.
  
  Lemma three_join_def (x y : Three) : three_maxn x y = if (x < y)%N then y else x.
  Proof.
    (* by case: x y => [] []. Qed.   *)
    done.
  Qed.
  
  Lemma three_anti : antisymmetric three_leq.
  Proof.
    rewrite /antisymmetric.
    move=> x y H.
    apply/eqP.
    by rewrite eq_le.
  Qed.

  HB.instance Definition _ := @isOrder.Build
                                three_display  (* unit *)
                                Three          (* T *)
                                three_leq      (* le *)
                                three_ltn      (* lt *)
                                three_minn     (* meet `&` *)
                                three_maxn     (* join `|` *)
                                ltn_def        (* lt_def *)
                                three_meet_def (* meet_def *)
                                three_join_def (* join_def *)
                                three_anti     (* le_anti *)
                                leq_trans      (* le_trans *)
                                leq_total.     (* le_total *)

(**
### 3値集合がtopとbottom を持つこと
*)
  Section NonTrivial.
(*
  n = 3 とする。

  Variable (n' : nat).
  Let n := n'.+1.                         (* n > 0 とする。 *)
*)
    HB.instance Definition _ := @hasBottom.Build
                                  three_display
                                  Three     (* 'I_n *)
                                  t0        (* ord0 *)
                                  leq0n.    (* le0x *)
    Check @le0x : forall (disp : unit) (L : bLatticeType disp) (x : L), (\bot <= x)%O.
    Check leq0n : forall x, ord0 <= x.

    HB.instance Definition _ := @hasTop.Build
                                  three_display
                                  Three     (* 'I_n *)
                                  t2        (* ord_max *)
                                  (@leq_ord t2). (* (@leq_ord ord_max). (* lex1 *) *)
    Check @lex1 : forall (disp : unit) (L : tLatticeType disp) (x : L), (x <= \top)%O.
    Check @leq_ord ord_max : forall i : 'I_ord_max.+1, i <= ord_max.

(**
### 3値集合がHeyting代数であること
*)
    Lemma botEord : (\bot = t0 :> Three)%O. Proof. by []. Qed. (* ord0 *)
    Lemma topEord : (\top = t2 :> Three)%O. Proof. by []. Qed. (* ord_max *)

    (* 含意 *)
    (* https://en.wikipedia.org/wiki/Heyting_algebra *)
    Definition three_impl (a b : Three) : Three := if (a <= b)%N then \top else b.
  
    (* 補元 *)
    (* https://en.wikipedia.org/wiki/Heyting_algebra *)
    Definition three_neg (a : Three) : Three := if (a == \bot)%N then \top else \bot.
    
    (* 便利な補題 *)
    Lemma sup_top (a : Three) : three_maxn \top a = \top. (* notu *)
    Proof.
      rewrite /three_maxn.
      case: a => i H.
      rewrite /top //=.
      case: ifP => //=.
      lia.
    Qed.
    
    Lemma sup_bot (a : Three) : three_maxn bottom a = a. (* notu *)
    Proof.
      rewrite /three_maxn.
    Admitted.                               (* notu *)
    
    Lemma inf_top (a : Three) : three_minn \top a = a.
    Proof.
      rewrite /three_minn.
      case: a => i H.
      rewrite /top /=.
      case: ifP.
      - lia.
      - move/negbT.
        by rewrite -leqNgt -ltnS.
    Qed.
    
    Lemma infC (a b : Three) :  three_minn a b = three_minn b a :> nat.
    Proof.
      rewrite /three_minn.
      by case: ltngtP => //=.
    Qed.
    
    Lemma inf_bot (a : Three) : three_minn a \bot = \bot.
    Proof.
      rewrite /three_minn.
      rewrite ltnNge.
      by rewrite leq0n.
    Qed.
    
    (* himplE *)
    (* 含意の条件 *)
    Lemma three_himplE (b c : Three) : exists (a : Three),
        (a <= three_impl b c)%N == (three_minn a b <= c)%N.
    Proof.
      rewrite /three_impl.
      case H : (b <= c)%N.
      - exists \top.
        by rewrite inf_top.
      - exists \bot.
        by rewrite infC inf_bot.
    Qed.
    
    (* hcomplE *)
    (* 補元の条件 *)
    Lemma three_negE (a : Three) : three_neg a = three_impl a \bot.
    Proof.
      rewrite /three_impl /three_neg /=.
      Check leqn0 : forall n : nat, (n <= 0)%N = (n == 0).
      by rewrite leqn0.
    Qed.
    
    HB.instance Definition _ := @hasHComplement.Build
                                  _ Three
                                  three_impl   (* himpl *)
                                  three_neg    (* hcompl *)
                                  three_himplE (* himplE *)
                                  three_negE.  (* hcomplE *)
  End NonTrivial.
End Three.

Module Exports.
  HB.reexport Three.
  
  Definition leEord := leEord.
  Definition ltEord := ltEord.
  Definition botEord := botEord.
  Definition topEord := topEord.
End Exports.
End Three.
HB.export Three.Exports.

(**
## 3値集合を使う
*)
Section Test.

  Import Three.
  Local Open Scope order_scope.
  
  (* Three の世界 *)
  Check Three : Type.
  Check t0 : Three.
  Check (t0 <= t2)%N.
  Check (t0 < t2)%N.

  (* Heyting Algebra の世界 *)
  (* Set Printing All. *)
  Check HeytingLattice three_display Three : Type.
  Check (t0 <= t2)%O.
  Check @le three_display Three.            (* <=%O は使えない。 *)
  Check @le three_display Three t0 t2.
  Check (t0 < t2)%O.

  Check t0 : 'I_3.
  Check t0 : Three.

  Check OrdinalOrder.ord_display.
  Check latticeType OrdinalOrder.ord_display.

  Check three_display : unit.
  Check latticeType three_display.
  
  Check tbDistrLatticeType three_display : Type.
  Check heytingAlgebraType three_display : Type. (* #[short(type=heytingAlgebraType")] の効果 *)

  Check 'I_3 : latticeType OrdinalOrder.ord_display.
  Fail Check 'I_3 : heytingAlgebraType three_display.
  
  Check Three : latticeType OrdinalOrder.ord_display.
  Check Three : latticeType three_display.  (* choice.copy で通る *)
  Check Three : distrLatticeType three_display. (* choice.copy で通る *)  
  Check Three : tbDistrLatticeType three_display. (* choice.copy で通る *)  
  Check Three : heytingAlgebraType three_display. (* #[short(type=heytingAlgebraType")] の効果 *)
  
  (* Set Printing All. *)
  Check @meet : forall (d : unit) (s : latticeType d), s -> s -> s.
  Check meet Three.t0 Three.t0 : Three.
  Check Three.t0 `&` Three.t0 : Three.
  Fail Check @meet three_display (_ : latticeType three_display) t0 t0.

  Check @himpl : forall (d : unit) (s : HeytingLattice.type d), s -> s -> s.
  Check @three_impl : Three -> Three -> Three.
  
  Check three_impl t0 t1.
  Check three_neg t0.
  
  Check @himpl three_display Three t0 t2.
  Check @hcompl three_display Three t1.

  Compute three_impl t0 t1 == t2.           (* true *)
  Compute three_neg t0 == t2.               (* true *)
  
  Compute @himpl three_display Three t0 t2 == t2. (* true *)
  Compute @hcompl three_display Three t0 == t2.   (* true *)
  
  Check top : Three.
  Check \top : Three.
  Check \top --> \bot.
  Check ~~~ \top.
  
  Compute t0 `&` t1 == t0.                  (* true *)
  Compute t0 `|` t1 == t1.                  (* true *)
  
  (* 引数がうまく略せないが、定義はできている。 *)
  Check himpl (t0 : Three) t2 == t2. (* true *)
  Compute himpl (t0 : Three) t2 == t2. (* true *)
  Check hcompl (t0 : Three) == t2.   (* true *)
  Compute hcompl (t0 : Three) == t2.   (* true *)

  Compute ((t0 : Three) --> t2) == t2.      (* true *)
  Compute ~~~ (t0 : Three) == t2.           (* true *)
  Compute ~~~ (t1 : Three) == t0.           (* true *)
  Compute ~~~ (t2 : Three) == t0.           (* true *)

  Compute t0 `|` ~~~ (t0 : Three) == t2.    (* true *)
  Compute t1 `|` ~~~ (t1 : Three) == t2.    (* false !!!  bool でないことを示す反例 *)
  Compute t2 `|` ~~~ (t2 : Three) == t2.    (* true *)

  Compute t0 `&` ~~~ (t0 : Three) == t0.    (* true *)
  Compute t1 `&` ~~~ (t1 : Three) == t0.    (* true *)
  Compute t2 `&` ~~~ (t2 : Three) == t0.    (* true *)

  (* 補元の不在の証明、ブール束でないことの証明 *)
  (* 1 ⊔ 1ᶜ ≠ ⊤ *)
  Goal exists (x : Three), x `|` ~~~ x != \top.
  Proof.
    by exists t1.
  Qed.

End Test.

HB.about heytingAlgebraType.
(**
```
HB: heytingAlgebraType is a structure (from "(stdin)", line 23)
HB: heytingAlgebraType characterizing operations and axioms are:
    - hcomplE
    - himplE
    - hcompl
    - himpl
HB: HeytingLattice is a factory for the following mixins:
    - hasChoice
    - hasDecEq
    - isPOrder
    - hasTop
    - POrder_isLattice
    - Lattice_Meet_isDistrLattice
    - hasBottom
    - hasHComplement (* new, not from inheritance *)
HB: HeytingLattice inherits from:
    - eqtype.Equality
    - choice.Choice
    - POrder
    - Lattice
    - DistrLattice
    - TPOrder
    - TLattice
    - BPOrder
    - BLattice
    - BDistrLattice
    - TBPOrder
    - TBLattice
    - TBDistrLattice
HB: HeytingLattice is inherited by:
```
*)

(* END *)
