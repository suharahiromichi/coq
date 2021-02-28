(**
Coq/SSReflect/MathComp による定理証明

6.1 テーマ1 整数がその加法で可換群になること
======
2018_04_21 @suharahiromichi
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
Z_zmodType                zmodType     可換群である（整数）型
Z_ringType               ringType     環である（整数）型（演習問題 6.1）

この階層の順番に定義していくのが自然です。

*)
Check CountChoiceMixin.

Section ZtoRing.
(**
## Z_eqType 決定可能な同値関係を持つ整数型
*)
(**
整数型どうしのbool型の同値関係 Zeq_bool
*)
  Compute Zeq_bool 0%Z 0%Z.                 (* true *)
  Compute Zeq_bool 0%Z 1%Z.                 (* false *)
  Compute Zeq_bool 1%Z 1%Z.                 (* true *)
  
(**
Zeq_boolが「=」と同値であることの証明
*)
  Lemma Zeq_boolP : Equality.axiom Zeq_bool.
  Proof.
    move=> x y.
      by apply: (iffP idP); rewrite Zeq_is_eq_bool.
  Qed.

  Definition Z_eqMixin := EqMixin Zeq_boolP.
  Canonical Z_eqType := EqType Z Z_eqMixin.
  (* 右辺で、カノニカル [Z <- Equality.sort Z_eqType] になる。 *)
  
(**
## Z_choiceType   有限選択公理のある整数型
## Z_countType    数え上げ可能な整数型
*)
  Definition Z_pickle (z : Z) : nat :=
    if (0 <=? z)%Z then
      (Z.abs_nat z).*2
    else
      (Z.abs_nat (- z)).*2.+1.
  
  Definition Z_unpickle (n : nat) : option Z :=
    if odd n then
      Some (- (Z.of_nat n.-1./2))%Z
    else
      Some (Z.of_nat n./2).
  
  Lemma Z_pickleK : pcancel Z_pickle Z_unpickle.
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
テキストでは、手記の順番ではなく、
Z_countMixin を定義し、CountChoiceMixin を使って  Z_choiceMixin を定義する。
Z_countType は は、Z_countMixin と Z_choiceType から定義する。
とすこし変則的なものになっています。

これは、choiceMixin で必要な公理（有限選択公理）
Record mixin_of T := Mixin {
  find : pred T -> nat -> option T;
  _ : forall P n x, find P n = Some x -> P x;
  _ : forall P : pred T, (exists x, P x) -> exists n, find P n;
  _ : forall P Q : pred T, P =1 Q -> find P =1 find Q}.
を直接証明するよりも、

countableMixin で必要な公理（数え上げの可能の公理）
Record mixin_of (T : Type) : Type := Mixin {
  pickle : T -> nat;
  unpickle : nat -> option T;
  pickleK : pcancel pickle unpickle}.
を証明するほうが易しく、CountChoiceMixin で choiceMixin を求めることができるからである。
*)
  Definition Z_countMixin := Countable.Mixin Z_pickleK.
  Definition Z_choiceMixin := CountChoiceMixin Z_countMixin.
  
  (* 右辺で、カノニカル [Z <- Equality.sort Z_eqType] を使う。 *)
  Canonical Z_choiceType := ChoiceType Z Z_choiceMixin.
  (* 左辺で、カノニカル [Z <- Choice.sort Z_choiceType] になる。 *)  

  (* テキストにはないが、countable も定義する場合 *)
  Canonical Z_countType := CountType Z_choiceType Z_countMixin.
  
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
  
  Definition Z_zmodMixin :=
    ZmodMixin Z.add_assoc Z.add_comm Z.add_0_l Z.add_opp_diag_l.
  (* 右辺で、カノニカル [Z <- Choice.sort Z_choiceType] を使う。 *)  
  Canonical Z_zmodType := ZmodType Z Z_zmodMixin.
  (* 左辺で、カノニカル [Z <- GRing.Zmodule.sort Z_zmodType] になる。 *)  
  
  (* Definition Z_zmodType := ZmodType Z_choiceType Z_zmodMixin. *)
  (* Definition Z_zmodType := ZmodType Z Z_zmodMixin. *)

  (* 確認 *)
  Check Z_eqType : eqType.
  Check Z_choiceType : choiceType.
  Check Z_countType : countType.
  Check Z_zmodType : zmodType.

End ZtoRing.

(**
# Ringの演算子 「*+」 を使えるようにする。
*)

Open Scope ring_scope.

(**
# Canonical Z_zmodType の必要性の説明
*)
Section TEST.
  
  Locate "_ == _".                          (* eq_op *)
  Check nat_eqType : eqType.
  (* Check @eq_op : forall T : eqType, sort T -> sort T -> bool. *)
  Check @eq_op : forall T : eqType, T -> T -> bool.
  Check @eq_op nat_eqType : nat -> nat -> bool.
  
  Locate "_ *+ _".               (* GRing.natmul x n   : ring_scope *)
  Check Z_zmodType : zmodType.
  Compute GRing.Zmodule.sort Z_zmodType.     (* Z *)
  
  Check @GRing.natmul : forall V : zmodType, (* sort のコアーションを明示しない。 *)
      V -> nat -> V.
  Check @GRing.natmul Z_zmodType :           (* 型の引数を与える。 *)
    Z_zmodType -> nat -> Z_zmodType.
  
  Check @GRing.natmul : forall V : zmodType, (* sort のコアーションを明示する。 *)
      GRing.Zmodule.sort V -> nat -> GRing.Zmodule.sort V.
  Check @GRing.natmul Z_zmodType :           (* 型の引数を与える。 *)
    GRing.Zmodule.sort Z_zmodType -> nat -> GRing.Zmodule.sort Z_zmodType.
  Check @GRing.natmul Z_zmodType :           (* sort Z_zmodType = Z を反映する。 *)
    Z -> nat -> Z.
  
  (* ○ : Canonical Z_zmodType でなくてもよい。 *)
  (* × : Canonical Z_zmodType でないとエラーになる。 *)
  
  Variable x : Z.
  
  Check @GRing.natmul Z_zmodType x 2 : Z_zmodType. (* ○ *)
  Check GRing.natmul x 2.                        (* × *)
  Check x *+ 2.                                  (* × *)
  
  (** Z_zmodType から、コアーションで sort Z_zmodType を計算して Z を求めることはできる。 *)
  Print Graph.                              (* コアーションの表示 *)
  (** [GRing.Zmodule.sort : GRing.Zmodule.type >-> Sortclass] *)
  (** しかし、x の型 Z から、Z_zmodType を見つけて補うことはできない。なので、*)
  Print Canonical Projections.              (* カノニカルの表示 *)
  (** [Z <- GRing.Zmodule.sort ( Z_zmodType )] *)
  (** Z_zmodType が、 Z のカノニカルであるこを宣言しておく。 *)
  
  (* カノニカル [Z <- GRing.Zmodule.sort Z_zmodType] を使う。 *)
  Check GRing.mulr2n x : x *+ 2 = x + x.            (* × *)
  Check @GRing.mulr2n Z_zmodType x : x *+ 2 = x + x. (* × *)
  
  Variable x' : Z_zmodType.
  Check x' *+ 2.                                        (* ○ *)
  Check GRing.mulr2n x' : x' *+ 2 = x' + x'.            (* ○ *)
  Check @GRing.mulr2n Z_zmodType x' : x' *+ 2 = x' + x'. (* ○ *)
  
  (** GRing.Zmodule.sort Z_zmodType を計算すると Z になるが、
      カノニカル宣言がなくてもよい。 *)
  Variable x'' : GRing.Zmodule.sort Z_zmodType.
  Compute GRing.Zmodule.sort Z_zmodType.        (* Z *)
  Check x'' *+ 2.                                           (* ○ *)
  Check GRing.mulr2n x'' : x'' *+ 2 = x'' + x''.            (* ○ *)
  Check @GRing.mulr2n Z_zmodType x'' : x'' *+ 2 = x'' + x''. (* ○ *)
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
