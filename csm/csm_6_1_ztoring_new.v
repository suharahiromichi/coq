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
補足：
zmodMixion と zmodType の定義のある ssralg はimportしますが、
MathComp の整数型である ssrint は import しません。

型インスタンス           型クラス      説明
Z_eqType                 eqType       決定可能な同値関係を持つ（整数）型
Z_choiceType             choiceType   有限選択公理のある（整数）型
Z_countType              countType    数え上げ可能な（整数）型
Z_modType                zmodType     可換群である（整数）型
Z_ringType               ringType     環である（整数）型（演習問題 6.1）

この階層の順番に定義していくのが自然です。
テキストではこの順番になっていないのですが、CanChoiceMixin と CanCountMixin を使います。
（PcanChoiceMixin と PcanCountMixin を使うことも可能です。）

また、テキストでは自然数から整数の対応を部分関数にしていますが、これは関数になるはずです。
そのため、pcancel ではなく cancel が成立するはずなので、そのようにしています。
（部分関数 で pcancel のままであっても、不都合なく証明できます）
*)
Check CountChoiceMixin.

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
  (* 右辺で、カノニカル [Z <- Equality.sort Z_eqType] になる。 *)
  
  Compute Equality.sort Z_eqType.           (* Z *)
  
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
  
(**
## Z_choiceType   有限選択公理のある整数型
*)
  Definition Z_choiceMixin := CanChoiceMixin Z_pickleK.
  (* 右辺で、カノニカル [Z <- Equality.sort Z_eqType] を使う。 *)
  Canonical Z_choiceType :=  ChoiceType Z Z_choiceMixin.
  (* 左辺で、カノニカル [Z <- Choice.sort Z_choiceType] になる。 *)

  Compute Equality.sort Z_eqType.           (* Z *)
  Compute Choice.sort Z_choiceType.         (* Z *)
  
(**
## Z_countType    数え上げ可能な整数型
*)
  Definition Z_countMixin := CanCountMixin Z_pickleK.
  (* 右辺で、カノニカル [Z <- Choice.sort Z_choiceType] を使う。 *)
  Canonical Z_countType := CountType Z Z_countMixin.
  (* 左辺で、カノニカル [Z <- Count.sort Z_countType] になる。 *)
  
  Compute Choice.sort Z_choiceType.         (* Z *)  
  Compute Countable.sort Z_countType.       (* Z *)

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
  
  Definition Z_modMixin :=
    ZmodMixin Z.add_assoc Z.add_comm Z.add_0_l Z.add_opp_diag_l.
  (* 右辺で、カノニカル [Z <- Choice.sort Z_choiceType] を使う。 *)  
  Canonical Z_modType := ZmodType Z Z_modMixin.
  (* 左辺で、カノニカル [Z <- GRing.Zmodule.sort Z_modType] になる。 *)  
  
  Compute Choice.sort Z_choiceType.         (* Z *)
  Compute GRing.Zmodule.sort Z_modType.     (* Z *)

  (* 個別に公理を証明しない、別な方法もある。 *)
  (* Definition Z_modType := ZmodType Z_choiceType Z_modMixin. *)

  (* 確認 *)
  Check Z_eqType : eqType.
  Check Z_choiceType : choiceType.
  Check Z_countType : countType.
  Check Z_modType : zmodType.

End ZtoRing.

(**
# Ringの演算子 「*+」 を使えるようにする。
*)

Open Scope ring_scope.

(**
# Canonical Z_modType の必要性の説明
*)
Section TEST.
  
  Locate "_ == _".                          (* eq_op *)
  Check nat_eqType : eqType.
  (* Check @eq_op : forall T : eqType, sort T -> sort T -> bool. *)
  Check @eq_op : forall T : eqType, T -> T -> bool.
  Check @eq_op nat_eqType : nat -> nat -> bool.
  
  Locate "_ *+ _".               (* GRing.natmul x n   : ring_scope *)
  Check Z_modType : zmodType.
  Compute GRing.Zmodule.sort Z_modType.     (* Z *)
  
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
  
  (* ○ : Canonical Z_modType でなくてもよい。 *)
  (* × : Canonical Z_modType でないとエラーになる。 *)
  
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
  
  Variable x' : Z_modType.
  Check x' *+ 2.                                        (* ○ *)
  Check GRing.mulr2n x' : x' *+ 2 = x' + x'.            (* ○ *)
  Check @GRing.mulr2n Z_modType x' : x' *+ 2 = x' + x'. (* ○ *)
  
  (** GRing.Zmodule.sort Z_modType を計算すると Z になるが、
      カノニカル宣言がなくてもよい。 *)
  Variable x'' : GRing.Zmodule.sort Z_modType.
  Compute GRing.Zmodule.sort Z_modType.        (* Z *)
  Check x'' *+ 2.                                           (* ○ *)
  Check GRing.mulr2n x'' : x'' *+ 2 = x'' + x''.            (* ○ *)
  Check @GRing.mulr2n Z_modType x'' : x'' *+ 2 = x'' + x''. (* ○ *)
End TEST.

(**
# [x *+ 2 = 2 * z] の証明
*)

Goal forall x : Z, x *+ 2 = (2 * x)%Z.
Proof.
  case=> // x; rewrite GRing.mulr2n Z.mul_comm.
    by rewrite -(Zred_factor1 (Z.pos x)).
    by rewrite -(Zred_factor1 (Z.neg x)).
Qed.

(** END *)
