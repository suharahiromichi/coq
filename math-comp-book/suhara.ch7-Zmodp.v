(* 7. Hierarchies *)
(* 7.1 Structure interface *)

(* algebra/zmodp.v  *)

From mathcomp Require Import all_ssreflect.
From mathcomp Require Import fintype finset fingroup ssralg finalg.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope ring_scope.

Section ZpDef.

  Variable p' : nat.
  Local Notation p := p'.+1.
  
  Implicit Types x y z : 'I_p.
  Check 'I_p.

  (* Standard injection; val (inZp i) = i %% p *)
  Definition inZp i := Ordinal (ltn_pmod i (ltn0Sn p')).
  
  Lemma modZp x : x %% p = x.
  Proof. by rewrite modn_small ?ltn_ord. Qed.
  
  Lemma valZpK x : inZp x = x.
  Proof. by apply: val_inj; rewrite /= modZp. Qed.
  
  (* Operations *)
  Definition Zp0 : 'I_p := ord0.
  Definition Zp1 := inZp 1.
  Definition Zp_opp x := inZp (p - x).
  Definition Zp_add x y := inZp (x + y).
  Definition Zp_mul x y := inZp (x * y).
  Definition Zp_inv x := if coprime p x then inZp (egcdn x p).1 else x.

  (* Additive group structure. *)

  Lemma Zp_add0z : left_id Zp0 Zp_add.
  Proof. exact: valZpK. Qed.
  
  Lemma Zp_addNz : left_inverse Zp0 Zp_opp Zp_add.
  Proof.
      by move=> x; apply: val_inj; rewrite /= modnDml subnK ?modnn // ltnW.
  Qed.
  
  Lemma Zp_addA : associative Zp_add.
  Proof.
      by move=> x y z; apply: val_inj; rewrite /= modnDml modnDmr addnA.
  Qed.
  
  Lemma Zp_addC : commutative Zp_add.
  Proof. by move=> x y; apply: val_inj; rewrite /= addnC. Qed.
  
  Definition Zp_zmodMixin := ZmodMixin Zp_addA Zp_addC Zp_add0z Zp_addNz.
  Canonical Zp_zmodType := Eval hnf in ZmodType 'I_p Zp_zmodMixin.
  Canonical Zp_finZmodType := Eval hnf in [finZmodType of 'I_p].
  Canonical Zp_baseFinGroupType := Eval hnf in [baseFinGroupType of 'I_p for +%R].
  Canonical Zp_finGroupType := Eval hnf in [finGroupType of 'I_p for +%R].
  
  (* Ring operations *)
  
  Lemma Zp_mul1z : left_id Zp1 Zp_mul.
  Proof. by move=> x; apply: val_inj; rewrite /= modnMml mul1n modZp. Qed.
  
  Lemma Zp_mulC : commutative Zp_mul.
  Proof. by move=> x y; apply: val_inj; rewrite /= mulnC. Qed.
  
  Lemma Zp_mulz1 : right_id Zp1 Zp_mul.
  Proof. by move=> x; rewrite Zp_mulC Zp_mul1z. Qed.
  
  Lemma Zp_mulA : associative Zp_mul.
  Proof.
      by move=> x y z; apply: val_inj; rewrite /= modnMml modnMmr mulnA.
  Qed.
  
  Lemma Zp_mul_addr : right_distributive Zp_mul Zp_add.
  Proof.
      by move=> x y z; apply: val_inj; rewrite /= modnMmr modnDm mulnDr.
  Qed.
  
  Lemma Zp_mul_addl : left_distributive Zp_mul Zp_add.
  Proof. by move=> x y z; rewrite -!(Zp_mulC z) Zp_mul_addr. Qed.
  
  Lemma Zp_mulVz x : coprime p x -> Zp_mul (Zp_inv x) x = Zp1.
  Proof.
    move=> co_p_x; apply: val_inj; rewrite /Zp_inv co_p_x /= modnMml.
      by rewrite -(chinese_modl co_p_x 1 0) /chinese addn0 mul1n mulnC.
  Qed.
  
  Lemma Zp_mulzV x : coprime p x -> Zp_mul x (Zp_inv x) = Zp1.
  Proof. by move=> Ux; rewrite /= Zp_mulC Zp_mulVz. Qed.
  
  Lemma Zp_intro_unit x y : Zp_mul y x = Zp1 -> coprime p x.
  Proof.
    case=> yx1; have:= coprimen1 p.
      by rewrite -coprime_modr -yx1 coprime_modr coprime_mulr; case/andP.
  Qed.
  
  Lemma Zp_inv_out x : ~~ coprime p x -> Zp_inv x = x.
  Proof. by rewrite /Zp_inv => /negPf->. Qed.
  
  Lemma Zp_mulrn x n : x *+ n = inZp (x * n).
  Proof.
    apply: val_inj => /=; elim: n => [|n IHn]; first by rewrite muln0 modn_small.
      by rewrite !GRing.mulrS /= IHn modnDmr mulnS.
  Qed.
  
  Import GroupScope.
  
  Lemma Zp_mulgC : @commutative 'I_p _ mulg.
  Proof. exact: Zp_addC. Qed.
  
  Lemma Zp_abelian : abelian [set: 'I_p].
  Proof. exact: FinRing.zmod_abelian. Qed.
  
  Lemma Zp_expg x n : x ^+ n = inZp (x * n).
  Proof. exact: Zp_mulrn. Qed.
  
  Lemma Zp1_expgz x : Zp1 ^+ x = x.
  Proof. by rewrite Zp_expg; apply: Zp_mul1z. Qed.
  
  Lemma Zp_cycle : setT = <[Zp1]>.
  Proof. by apply/setP=> x; rewrite -[x]Zp1_expgz inE groupX ?mem_gen ?set11. Qed.
  
  Lemma order_Zp1 : #[Zp1] = p.
  Proof. by rewrite orderE -Zp_cycle cardsT card_ord. Qed.
  
End ZpDef.

Implicit Arguments Zp0 [[p']].
Implicit Arguments Zp1 [[p']].
Implicit Arguments inZp [[p']].

Section ZpRing.
  
  Variable p' : nat.
  Local Notation p := p'.+2.
  
  Check 'I_p.
  Check Zp1 : 'I_p.
  Check 0 : 'I_p.
  
  Lemma Zp_nontrivial : Zp1 != 0 :> 'I_p. Proof. by []. Qed.
  
  Definition Zp_ringMixin :=
    ComRingMixin (@Zp_mulA _) (@Zp_mulC _) (@Zp_mul1z _) (@Zp_mul_addl _)
                 Zp_nontrivial.
  Canonical Zp_ringType := Eval hnf in RingType 'I_p Zp_ringMixin.
  Canonical Zp_finRingType := Eval hnf in [finRingType of 'I_p].
  Canonical Zp_comRingType := Eval hnf in ComRingType 'I_p (@Zp_mulC _).
  Canonical Zp_finComRingType := Eval hnf in [finComRingType of 'I_p].
  
  Definition Zp_unitRingMixin :=
    ComUnitRingMixin (@Zp_mulVz _) (@Zp_intro_unit _) (@Zp_inv_out _).
  Canonical Zp_unitRingType := Eval hnf in UnitRingType 'I_p Zp_unitRingMixin.
  Canonical Zp_finUnitRingType := Eval hnf in [finUnitRingType of 'I_p].
  Canonical Zp_comUnitRingType := Eval hnf in [comUnitRingType of 'I_p].
  Canonical Zp_finComUnitRingType := Eval hnf in [finComUnitRingType of 'I_p].
  
  Lemma Zp_nat n : n%:R = inZp n :> 'I_p.
  Proof. by apply: val_inj; rewrite [n%:R]Zp_mulrn /= modnMml mul1n. Qed.
  
  Lemma natr_Zp (x : 'I_p) : x%:R = x.
  Proof. by rewrite Zp_nat valZpK. Qed.
  
  Lemma natr_negZp (x : 'I_p) : (- x)%:R = - x.
  Proof. by apply: val_inj; rewrite /= Zp_nat /= modn_mod. Qed.
  
  Import GroupScope.
  
  Lemma unit_Zp_mulgC : @commutative {unit 'I_p} _ mulg.
  Proof. by move=> u v; apply: val_inj; rewrite /= GRing.mulrC. Qed.
  
  Lemma unit_Zp_expg (u : {unit 'I_p}) n :
    val (u ^+ n) = inZp (val u ^ n) :> 'I_p.
  Proof.
    apply: val_inj => /=; elim: n => [|n IHn] //.
      by rewrite expgS /= IHn expnS modnMmr.
  Qed.
  
End ZpRing.

Definition Zp_trunc p := p.-2.

Notation "''Z_' p" := 'I_(Zp_trunc p).+2
                         (at level 8, p at level 2, format "''Z_' p") : type_scope.

(* ***** *)
(* Mathcomp Book オリジナル *)
(* ***** *)

Section MCB.
  Variable m n : nat.
  
  Definition Zmn := ('Z_m * 'Z_n)%type.
  Canonical Zmn_eqType := [eqType of Zmn].
  Canonical Zmn_zmodType := [zmodType of Zmn].
  Canonical Zmn_ringType := [ringType of Zmn].


(* have Zp_mulrAC := @mulrAC [ringType of ’Z_p]. *)

End MCB.

(* END *)
