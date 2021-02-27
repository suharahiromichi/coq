(**
Coq/SSReflect/MathComp による定理証明

6.1 テーマ1 整数がその加法で可換群になること（テキスト見直し版）
======
2018_04_21 @suharahiromichi
2021_01_30 @suharahiromichi
 *)

From mathcomp Require Import all_ssreflect. (* eqType 他 *)
From mathcomp Require Import ssralg.        (* zmodType の定義 *)
Require Import ZArith.                      (* Standard Coq の整数型 *)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Set Print All.

(**
# 可換群の定義

説明： MathComp の型クラスのインスタンスとしての整数型を定義します。
整数型の定義は、Standard Coq の ZArith を使用します。
MathCompの整数型は、ssrintで定義されていますが、これとは別に定義をするわけです。

補足：
zmodMixion と zmodType の定義のある ssralg はimportしますが、
MathComp の整数型である ssrint は import しません。

型インスタンス           型クラス      説明
Z_eqType                 eqType       決定可能な同値関係を持つ（整数）型
Z_choiceType             choiceType   有限選択公理のある（整数）型
Z_countType              countType    数え上げ可能な（整数）型
Z_modType                zmodType     可換群である（整数）型
Z_ringType               ringType     環である（整数）型（演習問題 6.1）

この階層の順番に定義していくのが自然です。テキストではこの順番になっていないのですが、
CanChoiceMixin と CanCountMixin を使うことで、この順番で証明します。

参考： Mathematical Components (MCB) 7.5 Linking a custom data type to the library

補足： テキスト 176ページの図6.1にあるように、Z_modType を作るためには、
Z_choiceType があればよく、Z_countType は必要ではありません。

補足： テキストでは自然数から整数の対応を部分関数にしていますが、これは関数になるはずです。
そのため、pcancel ではなく cancel が成立するはずなので、そのようにしています。
部分関数 で pcancel のままであっても、
PcanChoiceMixin と PcanCountMixin を使うことで証明できます。

補足： Z-Module Z加群というのは整数環(環Z)上の加法についての群のことです。
可換群とかアーベル群といったほうが、判りやすいかもしれません。
*)

Section ZtoRing.
(**
## 整数型どうしのbool型の同値関係 Zeq_bool が「=」と同値であることを証明する。
*)
  Compute Zeq_bool 0%Z 0%Z.                 (* true *)
  Compute Zeq_bool 0%Z 1%Z.                 (* false *)
  Compute Zeq_bool 1%Z 1%Z.                 (* true *)
  
  Lemma Zeq_boolP : Equality.axiom Zeq_bool.
  Proof.
    move=> x y.
      by apply: (iffP idP); rewrite Zeq_is_eq_bool.
  Qed.

(**
## Z_eqType 決定可能な同値関係を持つ整数型
*)
  Definition Z_eqMixin := EqMixin Zeq_boolP.
  Canonical Z_eqType := EqType Z Z_eqMixin.
  
(**
## 整数が自然数と1対1対応することを証明する。
*)
  Definition Z_pickle (z : Z) : nat :=
    if (0 <=? z)%Z then
      (Z.abs_nat z).*2
    else
      (Z.abs_nat (- z)).*2.+1.
  
  Definition Z_unpickle (n : nat) : Z :=
    if odd n then
      (- (Z.of_nat n.-1./2))%Z
    else
      Z.of_nat n./2.

  Compute Z_pickle 1%Z.                     (* 2 *)
  Compute Z_unpickle 2.                     (* 1%Z *)
  
  Lemma Z_pickleK : cancel Z_pickle Z_unpickle.
  Proof.
    move=> z; rewrite /Z_pickle.
    case: ifP => z0;
    rewrite /Z_unpickle /= odd_double
            doubleK                      (* half_bit_double _ false *)
            Zabs2Nat.id_abs Z.abs_eq ?Z.opp_nonneg_nonpos
            ?Z.opp_involutive //.
    + by apply: Zle_bool_imp_le.
    + move/Z.leb_nle : z0.
        by move/Znot_le_gt /Z.gt_lt /Z.lt_le_incl.
  Qed.

  (* ハンズオン用の証明 *)
  (* Standard Coq の ZArith の下にある定理を使用して証明することの注意してください。 *)
  Lemma Z_pickleK' : cancel Z_pickle Z_unpickle.
  Proof.
    move=> z; rewrite /Z_pickle.
    case: ifP => Hz.
    - rewrite /Z_unpickle /=.
      (* if の true は成り立たないので捨てる。 *)
      rewrite odd_double /=.
      rewrite doubleK.
      
      Locate "_ <=? _".                     (* Z.leb x y : Z_scope *)
      Check Z.of_nat : nat -> Z.
      Check Z.abs_nat : Z -> nat.
      
      (* Hz : (0 <=? z)%Z *)
      (* Z.of_nat (Z.abs_nat z) = z *)
      
      (* z が0以上の場合、
         整数zの絶対値を自然数で得たものを整数に変換したものは、
         もとの自然数zに等しい。 *)
      rewrite Zabs2Nat.id_abs.
      rewrite Z.abs_eq.
      + done.
      + by apply: Zle_bool_imp_le.
        
    - rewrite /Z_unpickle /=.
      (* if の false は成り立たないので捨てる。 *)
      rewrite odd_double /=.
      rewrite doubleK.
      
      (* Hz : (0 <=? z)%Z = false *)
      (* (- Z.of_nat (Z.abs_nat (- z)))%Z = z *)
      
      (* z が0以上ではない場合、
         整数(- z)の絶対値を自然数で得たものを整数に変換したものの(-)は、
         もとの自然数zに等しい。 *)
      rewrite Zabs2Nat.id_abs Z.abs_eq.
      + rewrite Z.opp_involutive.
        done.
      + rewrite Z.opp_nonneg_nonpos.
        move: Hz.
        move/Z.leb_nle.
        move/Znot_le_gt.
        move/Z.gt_lt.
        move/Z.lt_le_incl.
        done.
  Qed.
  
(**
## Z_choiceType   有限選択公理のある整数型
*)
  Definition Z_choiceMixin := CanChoiceMixin Z_pickleK.
  Canonical Z_choiceType := ChoiceType Z Z_choiceMixin.
  
(**
## Z_countType    数え上げ可能な整数型
*)
  Definition Z_countMixin := CanCountMixin Z_pickleK.
  Canonical Z_countType := CountType Z Z_countMixin.
  
(**
## Z_zmodType     可換群である整数型
*)
(**
必要な補題は Coq.ZArith.BinInt. で証明されたものを使う。
*)
  Check Z.add_assoc : forall n m p : Z, (n + (m + p))%Z = (n + m + p)%Z.
  Check Z.add_comm : forall n m : Z, (n + m)%Z = (m + n)%Z.
  Check Z.add_0_l : forall n : Z, (0 + n)%Z = n.
  Check Z.add_opp_diag_l : forall n : Z, (- n + n)%Z = 0%Z.
  
  Definition Z_modMixin := ZmodMixin Z.add_assoc Z.add_comm Z.add_0_l Z.add_opp_diag_l.
  Canonical Z_modType := ZmodType Z Z_modMixin.
  (* Z_choiceType が必要である。Z_countType は必要ない。 *)
  
  (* 確認 *)
  Check Z_eqType : eqType.
  Check Z_choiceType : choiceType.
  Check Z_countType : countType.
  Check Z_modType : zmodType.

End ZtoRing.

(**
Z_ringType の定義は演習 6.1 を参照してください；

https://gitlab.com/proofcafe/csm/-/blob/master/csm_ex_6_1.v
*)

(**
# Ringの演算子 「*+」 を使えるようにする。
*)

Open Scope ring_scope.

Section TEST.
(**
## 演算子の定義
*)
(**
### 演算子 「==」 の定義。bool値の同値関係
*)
  Locate "_ == _".                          (* eq_op *)
  Check nat_eqType : eqType.
  (* Check @eq_op : forall T : eqType, sort T -> sort T -> bool. *)
  Check @eq_op : forall T : eqType, T -> T -> bool.
  Check @eq_op nat_eqType : nat -> nat -> bool.
  
(**
### 演算子 「*+」 の定義。整数と自然数の掛け算
*)
  Locate "_ *+ _".               (* GRing.natmul x n   : ring_scope *)
  Check Z_modType : zmodType.
  Compute GRing.Zmodule.sort Z_modType.     (* Z *)
  
(**
整数を自然数回足し算する。整数×自然数 の演算子である。
*)
  Compute 3%Z *+ 2%N.                       (* 6%Z *)
  Compute (- 3)%Z *+ 2%N.                   (* (- 6)%Z *)
  
  Check @GRing.natmul : forall V : zmodType, (* sort のコアーションを明示しない。 *)
      V -> nat -> V.
  Check @GRing.natmul Z_modType :           (* 型の引数を与える。 *)
    Z_modType -> nat -> Z_modType.
  
  Check @GRing.natmul : forall V : zmodType, (* sort のコアーションを明示する。 *)
      GRing.Zmodule.sort V -> nat -> GRing.Zmodule.sort V.
  Check @GRing.natmul Z_modType :           (* 型の引数を与える。 *)
    GRing.Zmodule.sort Z_modType -> nat -> GRing.Zmodule.sort Z_modType.
  Check @GRing.natmul Z_modType :           (* sort Z_modType = Z を反映する。 *)
    Z -> nat -> Z.
  
(**
## Canonical Z_modType の必要性の説明
*)

  (* ○ : Canonical Z_modType でなくてもよい。 *)
  (* × : Canonical Z_modType でないとエラーになる。 *)
  
(**
### x を Z 型で定義する。
 *)
  Variable x : Z.
  
  Check @GRing.natmul Z_modType x 2 : Z_modType. (* ○ *)
  Check GRing.natmul x 2.                        (* × *)
  Check x *+ 2.                                  (* × *)
  
  (** Z_modType から、コアーションで sort Z_modType を計算して Z を求めることはできる。 *)
  Print Graph.                              (* コアーションの表示 *)
  (** [GRing.Zmodule.sort : GRing.Zmodule.type >-> Sortclass] *)
  (** しかし、x の型 Z から、Z_modType を見つけて補うことはできない。なので、*)
  Print Canonical Projections.              (* カノニカルの表示 *)
  (** [Z <- GRing.Zmodule.sort ( Z_modType )] *)
  (** Z_modType が、 Z のカノニカルであるこを宣言しておく。 *)
  
  (* カノニカル [Z <- GRing.Zmodule.sort Z_modType] を使う。 *)
  Check GRing.mulr2n x : x *+ 2 = x + x.            (* × *)
  Check @GRing.mulr2n Z_modType x : x *+ 2 = x + x. (* × *)
  
(**
### x を Z_modType 型で定義する。
 *)
  Variable x' : Z_modType.
  Check x' *+ 2.                                        (* ○ *)
  Check GRing.mulr2n x' : x' *+ 2 = x' + x'.            (* ○ *)
  Check @GRing.mulr2n Z_modType x' : x' *+ 2 = x' + x'. (* ○ *)
  
(**
### x を (GRing.Zmodule.sort Z_modType) 型で定義する。
 *)
  Variable x'' : GRing.Zmodule.sort Z_modType.
  Compute GRing.Zmodule.sort Z_modType.        (* Z *)
(**
GRing.Zmodule.sort Z_modType を計算すると Z になるが、カノニカル宣言がなくてもよい。
 *)
  Check x'' *+ 2.                                           (* ○ *)
  Check GRing.mulr2n x'' : x'' *+ 2 = x'' + x''.            (* ○ *)
  Check @GRing.mulr2n Z_modType x'' : x'' *+ 2 = x'' + x''. (* ○ *)
End TEST.

(**
# [x *+ 2 = 2 * x] の証明
*)
Goal forall x : Z, x *+ 2 = (2 * x)%Z.
Proof.
  case=> // x; rewrite GRing.mulr2n Z.mul_comm.
    by rewrite -(Zred_factor1 (Z.pos x)).
    by rewrite -(Zred_factor1 (Z.neg x)).
Qed.

(** END *)
