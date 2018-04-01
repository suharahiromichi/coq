(* 7. Hierarchies *)
(* 7.1 Structure interface *)

(* Mathcomp Book Z-module *)
(* algebra/zmodp.v をもとに、修正した。 *)

From mathcomp Require Import all_ssreflect.
From mathcomp Require Import fintype finset fingroup ssralg finalg.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope ring_scope.

Section Ord.

  (* ordinal の定義 *)
  Locate "'I_ _".                           (* ordinal n *)
  Print ordinal.
  (* Inductive ordinal (n : nat) : predArgType :=
    Ordinal : forall m : nat, m < n -> 'I_n *)
  Check @Ordinal : forall n m : nat, m < n -> 'I_n.
  
(*
Ordinal n m H : 'I_n
Ordinal は値コンストラクタであり、'I_n 型の（自然数にすると）m になる値である。
H2_3 は m < n であることの証明。
 *)
  Variable H2_3 : 2 < 3.
  Check @Ordinal 3 2 H2_3 : 'I_3.
End Ord.

Section ZpDef.

  Variable p' : nat.
  Local Notation p := p'.+1.
  
  Implicit Types x y z : 'I_p.
  Check 'I_p : predArgType.
  
  (* dが0より大きいとき、dで割った余りは、dより小さい。 *)
  Check ltn_pmod : forall m d : nat, 0 < d -> m %% d < d.
  
  (* +1 したものは、0より大きい。 *)
  Check ltn0Sn : forall n : nat, 0 < n.+1.
  
  (* Standard injection; val (inZp i) = i %% p *)
  (* 'I_p 型の（自然数にすると）(i %% p) になる値である。 *)
  Definition inZp i := @Ordinal p (i %% p) (ltn_pmod i (ltn0Sn p')).
(* Definition inZp i := Ordinal            (ltn_pmod i (ltn0Sn p')). *)
  Check inZp 0 : 'I_p.
  Check inZp p.-1 : 'I_p.
  Check inZp p : 'I_p.
  Check inZp p.+1 : 'I_p.
  
  (* *************** *)
  (* zmod Operations *)
  (* *************** *)
  
  Definition Zp0 : 'I_p := ord0.
  Definition Zp1 := inZp 1.
  Definition Zp_opp x := inZp (p - x).
  Definition Zp_add x y := inZp (x + y).
  Definition Zp_mul x y := inZp (x * y).
  Definition Zp_inv x := if coprime p x then inZp (egcdn x p).1 else x.
  (* coprime 互いに素。egcdn 拡張GCD。 *)
  
  
  (* Additive group structure. *)

  Lemma modZp x : x %% p = x.
  Proof.
      by rewrite modn_small ?ltn_ord.
  Qed.

  Lemma modZp2 x : x %% p = (x + p) %% p.   (* suhara *)
  Proof.
    rewrite modnDr.
      by rewrite modn_small ?ltn_ord.
  Qed.

  Lemma modZp3 x : forall m n, (x + m * p) %% p = (x + n * p) %% p.   (* suhara *)
  Proof.
    move=> m n.
    rewrite addnC modnMDl.
    rewrite addnC modnMDl.
    done.
  Qed.

  Lemma valZpK x : inZp x = x.
  Proof.
      by apply: val_inj; rewrite /= modZp.
  Qed.
  
  Lemma valZpK2 x : inZp x = inZp (x + p).  (* suhara *)
  Proof.
    apply: val_inj.
    Check val : 'I_p -> nat.                (* これが単射であることをつかう。 *)
    rewrite /= modZp2.
    done.
    Restart.
      by apply: val_inj; rewrite /= modZp2.
  Qed.

  Lemma valZpK3 x : forall m n, inZp (x + m * p) = inZp (x + n * p).  (* suhara *)
  Proof.
    move=> m n.
    apply: val_inj.
    rewrite /=.
    Check modZp3 x m n.
    by rewrite (modZp3 x m n).
  Qed.
  
  Lemma Zp_add0z : left_id Zp0 Zp_add.
  Proof.
    exact: valZpK.
  Qed.
  
  Lemma Zp_addNz : left_inverse Zp0 Zp_opp Zp_add.
  Proof.
      by move=> x; apply: val_inj; rewrite /= modnDml subnK ?modnn // ltnW.
  Qed.
  
  Lemma Zp_addA : associative Zp_add.
  Proof.
      by move=> x y z; apply: val_inj; rewrite /= modnDml modnDmr addnA.
  Qed.
  
  Lemma Zp_addC : commutative Zp_add.
  Proof.
      by move=> x y; apply: val_inj; rewrite /= addnC.
  Qed.
  
  Fail Check inZp 0 + inZp 1.
  
  (* zmod : additive abelian groups , see ssralg *)
  Definition Zp_zmodMixin := ZmodMixin Zp_addA Zp_addC Zp_add0z Zp_addNz. (* ssralg *)
  Canonical Zp_zmodType := Eval hnf in ZmodType 'I_p Zp_zmodMixin. (* ssralg *)
  Canonical Zp_finZmodType := Eval hnf in [finZmodType of 'I_p]. (* finalg *)
  Canonical Zp_baseFinGroupType := Eval hnf in [baseFinGroupType of 'I_p for +%R].
  Canonical Zp_finGroupType := Eval hnf in [finGroupType of 'I_p for +%R].

  (* *************** *)
  (* Ring operations *)
  (* *************** *)
  
  Lemma Zp_mul1z : left_id Zp1 Zp_mul.
  Proof.
      by move=> x; apply: val_inj; rewrite /= modnMml mul1n modZp.
  Qed.
  
  Lemma Zp_mulC : commutative Zp_mul.
  Proof.
      by move=> x y; apply: val_inj; rewrite /= mulnC.
  Qed.
  
  Lemma Zp_mulz1 : right_id Zp1 Zp_mul.
  Proof.
      by move=> x; rewrite Zp_mulC Zp_mul1z.
  Qed.
  
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
  Proof.
      by move=> Ux; rewrite /= Zp_mulC Zp_mulVz.
  Qed.
  
  Lemma Zp_intro_unit x y : Zp_mul y x = Zp1 -> coprime p x.
  Proof.
    case=> yx1; have:= coprimen1 p.
      by rewrite -coprime_modr -yx1 coprime_modr coprime_mulr; case/andP.
  Qed.
  
  Lemma Zp_inv_out x : ~~ coprime p x -> Zp_inv x = x.
  Proof.
      by rewrite /Zp_inv => /negPf->.
  Qed.
  
  Lemma Zp_mulrn x n : x *+ n = inZp (x * n).
  Proof.
    apply: val_inj => /=; elim: n => [|n IHn]; first by rewrite muln0 modn_small.
      by rewrite !GRing.mulrS /= IHn modnDmr mulnS.
  Qed.
  
  Import GroupScope.
  
  Lemma Zp_mulgC : @commutative 'I_p _ mulg.
  Proof.
    exact: Zp_addC.
  Qed.
  
  Lemma Zp_abelian : abelian [set: 'I_p].
  Proof.
    exact: FinRing.zmod_abelian.
  Qed.
  
  Lemma Zp_expg x n : x ^+ n = inZp (x * n).
  Proof.
    exact: Zp_mulrn.
  Qed.
  
  Lemma Zp1_expgz x : Zp1 ^+ x = x.
  Proof.
      by rewrite Zp_expg; apply: Zp_mul1z.
  Qed.
  
  Lemma Zp_cycle : setT = <[Zp1]>.
  Proof.
      by apply/setP=> x; rewrite -[x]Zp1_expgz inE groupX ?mem_gen ?set11.
  Qed.
  
  Lemma order_Zp1 : #[Zp1] = p.
  Proof.
      by rewrite orderE -Zp_cycle cardsT card_ord.
  Qed.
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
  
  Lemma Zp_nontrivial : Zp1 != 0 :> 'I_p.
  Proof.
      by [].
  Qed.
  
  Print GRing.ComRing.RingMixin.
  Definition Zp_ringMixin :=
    ComRingMixin (@Zp_mulA _) (@Zp_mulC _) (@Zp_mul1z _) (@Zp_mul_addl _)
                 Zp_nontrivial.
  Canonical Zp_ringType := Eval hnf in RingType 'I_p Zp_ringMixin.
  Canonical Zp_finRingType := Eval hnf in [finRingType of 'I_p].
  Canonical Zp_comRingType := Eval hnf in ComRingType 'I_p (@Zp_mulC _).
  Canonical Zp_finComRingType := Eval hnf in [finComRingType of 'I_p].
  
  (* inverse の unit をもつ ring *)
  Definition Zp_unitRingMixin :=
    ComUnitRingMixin (@Zp_mulVz _) (@Zp_intro_unit _) (@Zp_inv_out _).
  Canonical Zp_unitRingType := Eval hnf in UnitRingType 'I_p Zp_unitRingMixin.
  Canonical Zp_finUnitRingType := Eval hnf in [finUnitRingType of 'I_p].
  Canonical Zp_comUnitRingType := Eval hnf in [comUnitRingType of 'I_p].
  Canonical Zp_finComUnitRingType := Eval hnf in [finComUnitRingType of 'I_p].
  
  Lemma Zp_nat n : n%:R = inZp n :> 'I_p.
  Proof.
      by apply: val_inj; rewrite [n%:R]Zp_mulrn /= modnMml mul1n.
  Qed.
  
  Lemma natr_Zp (x : 'I_p) : x%:R = x.
  Proof.
      by rewrite Zp_nat valZpK.
  Qed.
  
  Lemma natr_negZp (x : 'I_p) : (- x)%:R = - x.
  Proof.
      by apply: val_inj; rewrite /= Zp_nat /= modn_mod.
  Qed.
  
  Import GroupScope.
  
  Lemma unit_Zp_mulgC : @commutative {unit 'I_p} _ mulg.
  Proof.
      by move=> u v; apply: val_inj; rewrite /= GRing.mulrC.
  Qed.
  
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

Section EQ.
  Variable p' : nat.
  Local Notation p := p'.+1.
  Canonical Zp_eqType := [eqType of 'Z_p].
  
  Goal inZp 1 = inZp 1 :> 'Z_p.
  Proof.
    rewrite /inZp.
    Undo 1.
    by apply/eqP.
  Qed.
End EQ.

(* ***** *)
(* Mathcomp Book Original *)
(* ***** *)

Section MCB.
  Variable m n : nat.
  
  Definition Zmn := ('Z_m * 'Z_n)%type.
  Canonical Zmn_eqType := [eqType of Zmn].
  Canonical Zmn_zmodType := [zmodType of Zmn].
  Canonical Zmn_ringType := [ringType of Zmn].

  Check 0 : 'Z_m.
  Check 0 : 'Z_n.
  Check (0, 0) : Zmn.
  Goal (0, 0) = (0, 0) :> Zmn.
  Proof.
    by apply/eqP.
  Qed.
  
(* have Zp_mulrAC := @mulrAC [ringType of 'Z_p]. *)

End MCB.

(* END *)

Check @Zp0 3 : 'I_4.
Check @inZp 3 0 : 'I_4.                     (* 0 *)

Check @Zp1 3 : 'I_4.
Check @inZp 3 1 : 'I_4.                     (* 1 *)

Check @inZp 3 2 : 'I_4.                     (* 2 *)
Check @inZp 3 3 : 'I_4.                     (* 3 *)
Check @inZp 3 4 : 'I_4.                     (* 0 *)
Check @inZp 3 5 : 'I_4.                     (* 1 *)
Check @inZp 3 6 : 'I_4.                     (* 2 *)
Check @inZp 3 7 : 'I_4.                     (* 3 *)

Goal @inZp 3 0 = @inZp 3 4.
Proof.
  Check 0 : 'I_4.
  Fail Check 4 : 'I_4.
  Check inZp 0 : 'I_4.
  Check inZp 4 : 'I_4.
  
  Set Printing Implicit.                    (* XXXX *)
  Check @valZpK2 3 0.
  apply (@valZpK2 3 0).
Qed.

Locate "_ + _".                             (* Zmodule の add でない。 *)

