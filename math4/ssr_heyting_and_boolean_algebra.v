(**
Distr になっているか確認する。distr を継承できているか。
ならば、補元の一意を証明する。

Check Three : tbDistrLatticeType three_display.  (* choice.copy で通る *)  
Check Three : heytingAlgebraType three_display. (* #[short(type="heytingAlgebraType")] で通る。 *)

 *)

(**
lean-by-example/LeanByExample/Tutorial/Exercise/HeytingAndBooleanAlgebra.lean

Threeの場合の sub を定義する。
それが、boolOrderのように公理を満たさないことを示す。どこで。
 *)

(*
補元 compl をLean by example では、``a -> bot`` で定義する。
order.v では、``top \ a`` で定義する。

本来は真理値表を書くべきだが、bool代数では両者は同じになる：

P -> Q == ~P \/ Q
P -> F == ~P

P \ Q == P /\ ~Q
T \ Q == ~Q
*)

(**
これから、
tbDistrLatticeType を継承した heytingType を定義する。
このとき、compl の定義が、order.v のと別になる。
*)

From elpi Require Import elpi.
From HB Require Import structures.
From mathcomp Require Import all_ssreflect.
From mathcomp Require Import zify ring lra.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

HB.about porderType.
HB.about Order.isPOrder. (* new, not from inheritance *)

HB.about latticeType.
HB.about Order.POrder_isLattice. (* new, not from inheritance *)

HB.about distrLatticeType.                  (* 分配束 *)
HB.about Order.Lattice_Meet_isDistrLattice. (* new, not from inheritance *)

HB.about bDistrLatticeType.                 (* bottom がある。 *)

HB.about cbDistrLatticeType.
HB.about Order.hasRelativeComplement. (* new, not from inheritance *)

HB.about tbDistrLatticeType.                (* top と bottom がある。 *)

HB.about ctbDistrLatticeType.               (* 可補束 *)
HB.about Order.hasComplement. (* new, not from inheritance *)

HB.about finPOrderType.
HB.about finLatticeType.
HB.about finDistrLatticeType.               (* 分配束 *)
HB.about finCDistrLatticeType.              (* 可補束 *)

HB.graph "hierarchy.dot".
(* tred hierarchy.dot | dot -T png > hierarchy.png *)

(**
```
porderType
|
latticeType
|\______________________________________
|                       \               \
|                       tLatticeType    bLatticeType
|                       |               |
|                       \~~~~~~~~~~~~~~\|
|                                       tbLatticeType
|                                       |
|                                      (tbDistrLatticeType)
distrLatticeType
|
bDistrLatticeType
|\______________________
|                       \
tbDistrLatticeType      cbDistrLatticeType
|                       /
|/~~~~~~~~~~~~~~~~~~~~~~
|
ctbDistrLatticeType
```
*)

Import Order.
Import Order.Theory.

(**
Heyting Lattice の定義
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

  Definition three_leq (x y : Three) := (x <= y)%N.
  
  Definition three_ltn (x y : Three) := (x < y)%N.
  
  (* minn にすると、Three -> Three -> nat になる。 *)
  (* これは、Three -> Three -> Three でなければならない。 *)
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
                                three_display (* unit *)
                                Three         (* T *)
                                three_leq      (* le *)
                                three_ltn      (* lt *)
                                three_minn     (* meet `&` *)
                                three_maxn     (* join `|` *)
                                ltn_def        (* lt_def *)
                                three_meet_def (* meet_def *)
                                three_join_def  (* join_def *)
                                three_anti      (* le_anti *)
                                leq_trans     (* le_trans *)
                                leq_total.    (* le_total *)

  Section NonTrivial.
(*
    Variable (n' : nat).
    Let n := n'.+1.                         (* n > 0 とする。 *)
*)
    HB.instance Definition _ := @hasBottom.Build
                                  three_display
                                  Three     (* 'I_n *)
                                  t0        (* ord0 *)
                                  leq0n. (* le0x *)
    Check @le0x : forall (disp : unit) (L : bLatticeType disp) (x : L), (\bot <= x)%O.
    Check leq0n : forall x, ord0 <= x.

    HB.instance Definition _ := @hasTop.Build
                                  three_display
                                  Three     (* 'I_n *)
                                  t2        (* ord_max *)
                                  (@leq_ord t2). (* (@leq_ord ord_max). (* lex1 *) *)
    Check @lex1 : forall (disp : unit) (L : tLatticeType disp) (x : L), (x <= \top)%O.
    Check @leq_ord ord_max : forall i : 'I_ord_max.+1, i <= ord_max.

    Lemma botEord : (\bot = t0 :> Three)%O. Proof. by []. Qed. (* ord0 *)
    Lemma topEord : (\top = t2 :> Three)%O. Proof. by []. Qed. (* ord_max *)

    (* 含意 *)
    (* https://en.wikipedia.org/wiki/Heyting_algebra *)
    Definition three_impl (a b : Three) : Three := if (a <= b)%N then t2 else b.
  
    (* 補元 *)
    (* https://en.wikipedia.org/wiki/Heyting_algebra *)
    Definition three_neg (a : Three) : Three := if (a == t0)%N then t2 else t0.
    
    (* 便利な補題 *)
    Lemma sup_top (a : Three) : three_maxn top a = top.
    Proof.
    Admitted.

    Lemma sup_bot (a : Three) : three_maxn bottom a = a.
    Proof.
    Admitted.
    
    Lemma inf_top (a : Three) : three_minn t2 a = a.
    Proof.
      rewrite /three_minn.
      case: a => i H.
      rewrite /t2 /=.
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
(*
      move/esym => H.
      case: a H.
      case: b.
      move=> i Hi j Hj H.
      Set Printing All.
    Admitted.
    Unset Printing All.
*)
    
    Lemma inf_bot (a : Three) : three_minn a t0 = t0.
    Proof.
      rewrite /three_minn.
      rewrite ltnNge.
      by rewrite leq0n.
    Qed.

(*
    Lemma inf_bot (a : Three) : three_minn t0 a = t0.
    Proof.
      Check leqn0 : forall n : nat, (n <= 0)%N = (n == 0).
      rewrite /three_minn.
      case H : (a == t0).
      - move/eqP in H.
        by rewrite H.
      - case: ltnP.
        + by move/lt0n_neq0.
        + rewrite leq_eqVlt => /orP [].
          * move/eqP.
            simpl => H'.
            move/eqP in H.
            case: H'.
          * done.
    Admitted.
*)
    
    (* himplE *)
    (* 含意の条件 *)
    Lemma three_himplE (b c : Three) : exists (a : Three),
        (a <= three_impl b c)%N == (three_minn a b <= c)%N.
    Proof.
      rewrite /three_impl.
      case H : (b <= c)%N.
      - exists t2.
        by rewrite inf_top.
      - exists t0.
        by rewrite infC inf_bot.
    Qed.
    
    (* hcomplE *)
    (* 補元の条件 *)
    Lemma three_negE (a : Three) : three_neg a = three_impl a \bot.
    Proof.
      rewrite /three_impl /three_neg /=.
      Check leqn0 : forall n : nat, (n <= 0)%N = (n == 0).
      by rewrite leqn0.
(*
      rewrite /three_impl /three_neg /top /bottom /=.
      case: ifP.
      - by move/eqP => ->.
      - case/negbT/lt_total/orP => //=.
        by rewrite leNgt => ->.
*)
    Qed.
    
    HB.instance Definition _ := @hasHComplement.Build
                                  _ Three
                                  three_impl (* himpl *)
                                  three_neg  (* hcompl *)
                                  three_himplE (* himplE *)
                                  three_negE. (* hcomplE *)
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
  Check Three : distrLatticeType three_display.  (* choice.copy で通る *)  
  Check Three : tbDistrLatticeType three_display.  (* choice.copy で通る *)  
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
  Check hcompl (t0 : Three) == t2.   (* true *)
  
  Compute himpl (t0 : Three) t2 == t2. (* true *)
  Compute hcompl (t0 : Three) == t2.   (* true *)

  Compute (t0 : Three) --> t2 == t2. (* true *)
  Compute ~~~ (t0 : Three) == t2.   (* true *)
  Compute ~~~ (t1 : Three) == t0.   (* true *)
  Compute ~~~ (t2 : Three) == t0.   (* true *)

  (* bool でないことの判例 *)
  Compute t0 `|` ~~~ (t0 : Three) == t2.    (* true *)
  Compute t1 `|` ~~~ (t1 : Three) == t2.    (* false !!! *)
  Compute t2 `|` ~~~ (t2 : Three) == t2.    (* true *)

  Compute t0 `&` ~~~ (t0 : Three) == t0.    (* true *)
  Compute t1 `&` ~~~ (t1 : Three) == t0.    (* true *)
  Compute t2 `&` ~~~ (t2 : Three) == t0.    (* true *)

  (* 補元の不在の証明、ブール束でないことの証明 *)
  (* 1 ⊔ 1ᶜ ≠ ⊤ *)
  Goal exists (x : Three), x `|` ~~~ x != t2.
  Proof.
    by exists t1.
  Qed.
End Test.

HB.about heytingAlgebraType.

(* ！！！！！！！！！！！！！！！！！！！！！！！！！！！！！！！！！ *)
(* ここで一応完成した！！！ *)
(* ！！！！！！！！！！！！！！！！！！！！！！！！！！！！！！！！！ *)

(* order_scope は常用しないほうが良いようだ。 *)
(* Open Scope order_scope. *)

(**
OrdinalOrder の例
 *)
Module OrdinalOrder.
Section OrdinalOrder.

Fact ord_display : unit. Proof. exact: tt. Qed.

Section PossiblyTrivial.
Variable (n : nat).

HB.instance Definition _ := [SubChoice_isSubOrder of 'I_n by <: with ord_display].

Lemma leEord : (le : rel 'I_n) = leq. Proof. by []. Qed.
Lemma ltEord : (lt : rel 'I_n) = (fun m n => m < n)%N. Proof. by []. Qed.
End PossiblyTrivial.

Section NonTrivial.
Variable (n' : nat).
Let n := n'.+1.                             (* n > 0 とする。 *)

HB.instance Definition _ := @hasBottom.Build
                              _ 'I_n
                              ord0
                              leq0n. (* le0x *)
Check @le0x : forall (disp : unit) (L : bLatticeType disp) (x : L), (\bot <= x)%O.
Check leq0n : forall x, ord0 <= x.

HB.instance Definition _ := @hasTop.Build
                              _ 'I_n
                              ord_max
                              (@leq_ord ord_max). (* lex1 *)
Check @lex1 : forall (disp : unit) (L : tLatticeType disp) (x : L), (x <= \top)%O.
Check @leq_ord ord_max : forall i : 'I_ord_max.+1, i <= ord_max.

Lemma botEord : (\bot = ord0 :> 'I_n)%O. Proof. by []. Qed.
Lemma topEord : (\top = ord_max :> 'I_n)%O. Proof. by []. Qed.
End NonTrivial.

Section Three.
  Local Open Scope order_scope.
  
  Definition Three := 'I_3.

  Definition t0 := @Ordinal 3 0 is_true_true.
  Definition t1 := @Ordinal 3 1 is_true_true.
  Definition t2 := @Ordinal 3 2 is_true_true.

  Check t0 `&` t0 : OrdinalOrder.fintype_ordinal__canonical__Order_Lattice 3.
  Check t0 `&` t0 : OrdinalOrder.fintype_ordinal__canonical__Order_Lattice 3.
  
  Compute \bot == t0.                       (* true *)
  Compute \top == t2.                       (* true *)
  
  Compute t0 `&` t0 == t0.                  (* true *)
  Compute t0 `&` t1 == t0.                  (* true *)
  Compute t0 `&` t2 == t0.                  (* true *)
  Compute t1 `&` t0 == t0.                  (* true *)
  Compute t1 `&` t1 == t1.                  (* true *)
  Compute t1 `&` t2 == t1.                  (* true *)
  Compute t2 `&` t0 == t0.                  (* true *)
  Compute t2 `&` t1 == t1.                  (* true *)
  Compute t2 `&` t2 == t2.                  (* true *)

  Compute t0 `|` t0 == t0.                  (* true *)
  Compute t0 `|` t1 == t1.                  (* true *)
  Compute t0 `|` t2 == t2.                  (* true *)
  Compute t1 `|` t0 == t1.                  (* true *)
  Compute t1 `|` t1 == t1.                  (* true *)
  Compute t1 `|` t2 == t2.                  (* true *)
  Compute t2 `|` t0 == t2.                  (* true *)
  Compute t2 `|` t1 == t2.                  (* true *)
  Compute t2 `|` t2 == t2.                  (* true *)
  
  Compute \bot <= t1.                       (* true *)
  Compute t1 <= \top.                       (* true *)
  
  Compute le t0 t0.                         (* true *)
  Compute lt t0 t1.                         (* true *)


  Check leq_subr : forall m n : nat, (n - m <= n)%N.
  Check ltn_ord: forall [n : nat] (i : 'I_n), (i < n)%N.
  
  (* subo t2 - x = ~ x になるようにする。 *)
  (* subo t2 - t2 = t0 *)
  (* subo t2 - t0 = t2 *)
  Definition subong (x y : Three) : Three :=
    match (\val x), (\val y) with
    | 0, 0 => t0
    | 0, 1 => t2
    | 0, 2 => t2
    | 1, 0 => t0
    | 1, 1 => t0
    | 1, 2 => t0
    | 2, 0 => t0
    | 2, 1 => t0                            (* XXX *)
    | 2, 2 => t0
    | _, _ => t0
    end.

  Definition subo (x y : Three) : Three :=
    match (\val x), (\val y) with
    | 0, 0 => t0
    | 0, 1 => t0
    | 0, 2 => t0
    | 1, 0 => t1
    | 1, 1 => t0
    | 1, 2 => t0
    | 2, 0 => t2
    | 2, 1 => t0                            (* XXX *)
    | 2, 2 => t0
    | _, _ => t0
    end.


  Definition subo_diff (x y : Three) : Three :=
    match (x - y) with
    | 0 => t0
    | 1 => t1
    | 2 => t2
    | _ => t0
    end.
  
  Compute subo \top t0 == t2.               (* true *)
  Compute subo \top t1 == t1.               (* true *)
  Compute subo \top t2 == t0.               (* true *)
  
  Lemma em (x : Three) : (x = t0) \/ (x = t1) \/ (x = t2).
  Proof.
  Admitted.
  
  (* diffKIを満たす。 *)
  Lemma suboKI (x y : Three) : y `&` (subo x y) = \bot.
  Proof.
    apply/eqP.
    case: (em y) => [| []]; case: (em x) => [| []] => -> -> //=.
    Compute t1 `&` subo t2 t1 == t0.
  Admitted.

  (* joinIB を満たす。 *)
  Lemma joinoIB (x y : Three) : (x `&` y) `|` (subo x y) = x.
  Proof.
    apply/eqP.
    case: (em y) => [| []]; case: (em x) => [| []] => -> -> //=.
    Compute (t2 `&` t1) `|` subo t2 t1 == t2.
  Admitted.
  (* t2 - t1 の結果の見直しでは、修正できない。 *)
  (* それでも、subo 全体を見直すと、成立するだろうか？ *)
  (* ハイティング代数は、cbtdistri か？ *)

End Three.



End OrdinalOrder.
End OrdinalOrder.

(**
BoolOrder の例

補元を ``top \ a`` で定義する。
*)
Module BoolOrder.
Section BoolOrder.
Implicit Types (x y : bool).

Fact bool_display : unit. Proof. exact: tt. Qed.

Fact andbE x y : x && y = if (x < y)%N then x else y.
Proof. by case: x y => [] []. Qed.

Fact orbE x y : x || y = if (x < y)%N then y else x.
Proof. by case: x y => [] []. Qed.

Fact ltn_def x y : (x < y)%N = (y != x) && (x <= y)%N.
Proof. by case: x y => [] []. Qed.

Fact anti : antisymmetric (leq : rel bool).
Proof. by move=> x y /anti_leq /(congr1 odd); rewrite !oddb. Qed.

Definition sub x y := x && ~~ y.

Lemma subKI x y : (y && (sub x y)) = false. Proof. by case: x y => [] []. Qed.
Lemma joinIB x y : ((x && y) || (sub x y)) = x. Proof. by case: x y => [] []. Qed.

(* ***** *)
HB.instance Definition _ := @isOrder.Build
                              bool_display bool
                              _             (* le *)
                              _             (* lt *)
                              andb          (* meet `&` *)
                              orb           (* join `|` *)
                              ltn_def       (* lt_def *)
                              andbE         (* meet_def *)
                              orbE          (* join_def *)
                              anti          (* le_anti *)
                              leq_trans     (* le_trans *)
                              leq_total.    (* le_total *)

(* ***** *)
HB.instance Definition _ := @hasBottom.Build
                              _ bool
                              false         (* bottom *)
                              leq0n.        (* le0x *)
Check @le0x : forall (disp : unit) (L : bLatticeType disp)
                     (x : L), (\bot <= x)%O.
Check leq0n : forall n : nat, 0 <= n.

(* ***** *)
HB.instance Definition _ := @hasTop.Build
                              _ bool
                              true          (* top *)
                              leq_b1.       (* lex1 *)
Check @lex1 : forall (disp : unit) (L : tLatticeType disp)
                     (x : L), (x <= \top)%O.
Check leq_b1 : forall b : bool, (b <= 1)%N.

(* ***** *)
HB.instance Definition _ := @hasRelativeComplement.Build
                              _ bool
                              sub           (* diff *)
                              subKI         (* diffKI *)
                              joinIB.

(* y と ``y - x`` は同時にtrueにならない。 *)
Check @diffKI : forall (disp : unit) (L : cbDistrLatticeType disp)
                       (x y : L), (y `&` Order.sub x y)%O = \bot%O.
Check subKI : forall x y, (y && sub x y) = false.

(* ``x & y`  と ``x \ y`` をあわせると x になる。 *)
Check @Order.joinIB : forall (d : unit) (s : cbDistrLatticeType d)
         (x
          y : {|
                Lattice.sort := s;
                Lattice.class :=
                  {|
                    Lattice.choice_hasChoice_mixin := CBDistrLattice.class s;
                    Lattice.eqtype_hasDecEq_mixin := CBDistrLattice.class s;
                    Lattice.Order_isPOrder_mixin := CBDistrLattice.class s;
                    Lattice.Order_POrder_isLattice_mixin := CBDistrLattice.class s
                  |}
              |}),
    (x `&` y `|` Order.sub x y)%O = x.
Check joinIB : forall x y, ((x && y) || sub x y) = x.

(* ***** *)
HB.instance Definition _ := @hasComplement.Build
                              _ bool
                              negb          (* compl *)
                              (fun x => erefl : ~~ x = sub true x). (* complE *)

(* compl は ``top \ a`` に等しい。 *)
Check @complE : forall (disp : unit) (L : ctbDistrLatticeType disp)
                       (x : L), (~` x)%O = Order.sub \top%O x.
Check (fun x => erefl : ~~ x = sub true x) : forall x, ~~ x = sub true x.

(* ***** *)
Reserved Notation "A `\` B" (at level 50, left associativity).
Notation "x `\` y" := (diff x y) : order_scope.

Lemma leEbool : le = (leq : rel bool). Proof. by []. Qed.
Lemma ltEbool x y : (x < y) = (x < y)%N. Proof. by []. Qed.
Lemma andEbool : meet = andb. Proof. by []. Qed.
Lemma orEbool : meet = andb. Proof. by []. Qed.
Lemma subEbool x y : (x `\` y = x && ~~ y)%O. Proof. by []. Qed.

Lemma complEbool : compl = negb. Proof. by []. Qed.


Section Sample.
  Local Open Scope order_scope.

  Compute \top == true.                     (* true *)
  Compute \bot == false.                    (* true *)

  Compute true `&` false.                   (* false *)
  Compute true `|` false.                   (* true *)

  Compute false `\` false.                  (* false *)
  Compute false `\` true.                   (* false *)
  Compute true `\` false.                   (* true *)
  Compute true `\` true.                    (* false *)

  Compute compl true.                       (* false *)
  Compute compl false.                      (* true *)
End Sample.

End BoolOrder.
End BoolOrder.


(**
補元を ``a -> bot`` で定義する。
*)
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
  (* https://en.wikipedia.org/wiki/Heyting_algebra *)
  Definition himp (a b : Three) := if a <= b then top else b.
  
  (* 補元 *)
  (* https://en.wikipedia.org/wiki/Heyting_algebra *)
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
  Goal forall (b c : Three), exists (a : Three), (a <= himp b c) == (inf a b <= c).
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
