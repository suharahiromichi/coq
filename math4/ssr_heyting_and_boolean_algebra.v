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
|                       \               |
|                        ~~~~~~~~~~~~~~\|
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

  Compute \bot == t0.                       (* true *)
  Compute \top == t2.                       (* true *)
  
  Compute t0 `&` t1 == t0.                  (* true *)
  Compute t0 `|` t1 == t1.                  (* true *)

  Compute \bot <= t1.                       (* true *)
  Compute t1 <= \top.                       (* true *)
  
  Compute le t0 t0.                         (* true *)
  Compute lt t0 t1.                         (* true *)

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
