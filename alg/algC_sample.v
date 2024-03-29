(**
field/algC.v の使用例

algC は代数的数の公理的な構造を提供します。
この構築では、次数2の自己同型性を持つ代数的閉体の存在のみを前提としています。
これは、代数学の基本定理の純粋に代数的な内容に相当します。
*)
From HB Require Import structures.
From mathcomp Require Import all_ssreflect.
From mathcomp Require Import all_algebra.
From mathcomp Require Import all_field.

(**
# ssrnum までの構造を使えるようにする。
 *)
Import Num.Def Num.Theory.                  (* ssrnum.v *)
Import GRing.Theory.                        (* ssralg.v *)

(**
MathComp 2.1.0 で、Cnat が nat_num になり、補題の場所が移動したため、仮処置として…
 *)
Import archimedean.Num.Theory.
Import Num.ArchiNumDomain.Exports.

Check 1 : nat.
Fail Check 1 : algC.
(**
# scope を有効にする。
 *)
Open Scope ring_scope.
Check 1 : (_ : closedFieldType).
Check 1 : (_ : numClosedFieldType).
Check 1 : algC.

(**
# algC の数学構造

algC型は、numClosedFieldType型と archiClosedFieldType型のインスタンスである。
archiClosedFieldType は MathComp 2.1.0 で廃止になり、Num.ArchiClosedField.type を使う。

## ssralg で定義される型
 *)
Check algC : nmodType.
Check algC : zmodType.
Check algC : semiRingType.
Check algC : comSemiRingType.
Check algC : ringType.
Check algC : comRingType.                   (* 可換環 *)
Check algC : unitRingType.
Check algC : comUnitRingType.
Check algC : idomainType.                   (* 整域 *)
Check algC : fieldType.
Check algC : decFieldType.
Check algC : closedFieldType.               (* 閉体 *)

(**
## ssrnum で定義される型
 *)
Check algC : porderZmodType.
Fail Check algC : normedZmodType.
Check algC : numDomainType. (* Integral domain with an order and a norm *)
Check algC : archiNumDomainType. (* これは廃止されていない。 *) (* Num.ArchiNumDomain.type *)
Check algC : numFieldType.
Check algC : numClosedFieldType.
Fail Check algC : realDomainType. (* Num domain where all elements are positive or negative *)
Fail Check algC : realFieldType.
Fail Check algC : rcfType.
Check algC : Num.ArchiNumField.type.       (* archiNumFieldType. *)
Check algC : Num.ArchiClosedField.type.    (* archiClosedFieldType. *)
Fail Check algC : Num.ArchiDomain.type.    (* archiDomainType. *)
Fail Check algC : Num.ArchiField.type.     (* archiFieldType. *)
Fail Check algC : archiRcfType.

(* 参考 : アルキメデスの公理 *)
Print Num.archimedean_axiom.
(* fun R : numDomainType => forall x : R, exists ub : nat, normr x < ub%:R *)

(**
以上より、つぎのことが言える。
*)
(* これでは、ほとんど補題は見つからないので、 *)
Search algC.

(* これで探す。 *)
Search numClosedFieldType.

(* これで探す。 *)
(* Search archiClosedFieldType. *)
Search Num.ArchiClosedField.type.

(**
# 環 と nat や int の関係を示す補題

環 (algC) のままでは証明は進まないので、これらの補題を使って nat や int の問題に変形する。
*)
(**
## nat_num と int_num (MathComp 2.0.0 では Cnat と Cint)

どちらも定義は ``[qualify a x | P]`` の形式で、単なる ``P x``。ここで a は演算子の一部。
qualifE で書き換えられる。
 *)
Check qualifE : forall (n : nat) (T : Type) (p : {pred T}) (x : T), (x \in Qualifier n p) = p x.

Section Archi.
  Definition R : archiNumDomainType := algC.
  
  (* nat_num の定義 *)
  Check nat_num : qualifier 1 R. 
  Check [qualify a x : R | Num.nat_num_subdef x] : qualifier 1 R.

  (* 以下は、すべて同じ意味 *)
  Check 1 \is a nat_num.                    (* book *)
  Check 1 \is a [qualify a x : R | Num.nat_num_subdef x].
  Check Num.nat_num_subdef 1.
  
  (* nat_num の補題 *)
  Check nat_num1 R : 1 \is a nat_num.
  Check nat_num0 R : 0 \is a nat_num.
  Check natr_nat R : forall n : nat, n%:R \is a nat_num.
  Check @natrP R : forall x : R, reflect (exists n : nat, x = n%:R) (x \is a nat_num).
  
  Check trunc : R -> nat.                   (* 自然数にする関数 *)
  
  Check @natrE R : forall x : R, (x \is a nat_num) = ((trunc x)%:R == x).
  Check @Qnat_dvd : forall m d : nat, (d %| m)%N -> m%:R / d%:R \is a nat_num.
  Check @natr_ge0 R : forall x : R, x \is a nat_num -> 0 <= x.
  
  Check @Rreal_nat R : {subset nat_num <= Num.real}.
  
  (* nat_int の定義 *)
  Check int_num : qualifier 1 R.
  Check [qualify a x : R | Num.int_num_subdef x] : qualifier 1 R.
  
  Check -1 \is a nat_num.
  Check -1 \is a int_num.
  Check Num.int_num_subdef (-1).
  
  (* int_num の補題 *)
  Check int_num1 R : 1 \is a int_num.
  Check int_num0 R : 0 \is a int_num.
  Check intr_int R : forall m : int, m%:~R \is a int_num.
  Check @intrP R : forall x : R, reflect (exists m : int, x = m%:~R) (x \is a int_num).

  (* suhara *)
  Locate "_ %:R".  (* := (GRing.natmul (GRing.one _) n) : ring_scope (default interpretation) *)
  Locate "_ %:~R". (* := (intmul (GRing.one _) n) : ring_scope (default interpretation) *)
  Check @GRing.natmul R : R -> nat -> R.
  Check @intmul       R : R -> int -> R.
  (* どちらも``1``に数を掛けて R型を返すが、%:R は自然数、%:~R は整数 *)
  (* /suhara *)
  
  Check @intrE R : forall x : R, (x \is a int_num) = (x \is a nat_num) || (- x \is a nat_num).
  Check @Qint_dvdz : forall m d : int, (d %| m)%Z -> m%:~R / d%:~R \is a int_num.
  Check @intrEge0 R : forall x : R, 0 <= x -> (x \is a int_num) = (x \is a nat_num).

  Check @Rreal_int R : {subset int_num <= Num.real}.

  (* 偶数乗なら自然数である。 *)
  Check @natr_exp_even R : forall (x : R) (n : nat), ~~ odd n -> x \is a int_num -> x ^+ n \is a nat_num.
End Archi.

(**
## 0 と 1
*)
Section Num.
  (* Search numDomainType. *)
  Definition R1 : numDomainType := algC.
  
  Check pnatr_eq0 R1 : forall n : nat, (n%:R == 0) = (n == 0%N).
  Check pnatr_eq1 R1 : forall n : nat, (n%:R == 1) = (n == 1%N).

  Check @real_exprn_even_ge0 R1 : forall (n : nat) (x : R1), x \is Num.real -> ~~ odd n -> 0 <= x ^+ n.
End Num.

(**
## 足し算と掛け算
*)
Section SemiRing.
  (* Search numDomainType. *)
  Definition R2 : semiRingType := algC.
  
  Check @natrD R2 : forall m n : nat, (m + n)%:R = m%:R + n%:R.
  Check @natrM R2 : forall m n : nat, (m * n)%:R = m%:R * n%:R.
End SemiRing.

Section ComUnitRing.
  (* Search comUnitRingType. *)
  Definition R3 : comUnitRingType := algC.

  Check @mulr1_eq R3 : forall x y : R3, x * y = 1 -> x^-1 = y.
  Check @divr1_eq R3 : forall x y : R3, x / y = 1 -> x = y.
End ComUnitRing.

(**
# exercise5 でつかう補題

## numClosedFieldType の補題

前述のとおり、algC で成り立つ。
 *)
Section CF.
  (* Search numClosedFieldType. *)
  Definition C : numClosedFieldType := algC.

  Check Re_i C : 'Re 'i = 0.
  Check Im_i C : 'Im 'i = 1.
  
  Check invCi C : 'i^-1 = - 'i.
  Check invr0 C : 0^-1 = 0.                 (* unitRing であるが、念の為 *)
  Check invr1 C : 1^-1 = 1.                 (* unitRing であるが、念の為 *)
  
  Check @Crect C  : forall x :    C, x = 'Re x + 'i * 'Im x.
  Check @algCrect : forall x : algC, x = 'Re x + 'i * 'Im x. (* 参考、algC 専用 *)
  
  Check @mulC_rect C : forall x1 y1 x2 y2 : C,
      (x1 + 'i * y1) * (x2 + 'i * y2) = x1 * x2 - y1 * y2 + 'i * (x1 * y2 + x2 * y1).
  
  Check @Re_rect C : {in Num.real &, forall x y : C, 'Re (x + 'i * y) = x}.
  Check @Im_rect C : {in Num.real &, forall x y : C, 'Im (x + 'i * y) = y}.
  
  Check @Creal_ReP C : forall z : C, reflect ('Re z = z) (z \is Num.real).
  Check @Creal_ImP C : forall z : C, reflect ('Im z = 0) (z \is Num.real).

  Check @ReM C : forall x y : C, 'Re (x * y) = 'Re x * 'Re y - 'Im x * 'Im y.
  Check @ImM C : forall x y : C, 'Im (x * y) = 'Re x * 'Im y + 'Re y * 'Im x.

  Check @Re_conj C : forall z : C, 'Re z^* = 'Re z.
  Check @Im_conj C : forall z : C, 'Im z^* = - 'Im z.
  
  Check @ReMil C : forall x : C, 'Re ('i * x) = - 'Im x.
  Check @ImMil C : forall x : C, 'Im ('i * x) = 'Re x.

  Check @ReMir C : forall x : C, 'Re (x * 'i) = - 'Im x.
  Check @ImMir C : forall x : C, 'Im (x * 'i) = 'Re x.

  Check @normCK C : forall x : C, normr x ^+ 2 = x * x^*.
  Check @normC2_Re_Im C : forall z : C, normr z ^+ 2 = 'Re z ^+ 2 + 'Im z ^+ 2.
End CF.

(**
## 加算減算についての分配則

zmodType 上の関数の分配側であるが、ReやIm、\in に利用できる。
*)
Section ALGC.
  Variable x y : algC.

  Check algC : zmodType.
  Check @Re algC : algC -> algC.
  Check @Re algC : {additive algC -> algC}.
  
  Check @raddfN algC algC (@Re algC) x   : 'Re (- x) = - 'Re x.
  Check @raddfD algC algC (@Re algC) x y : 'Re (x + y) = 'Re x + 'Re y.
  Check @raddfB algC algC (@Re algC) x y : 'Re (x - y) = 'Re x - 'Re y.

  Check @rpredN algC _ x : (- x \in int_num) = (x \in int_num).
  Check @rpredD algC _ x y : x \in int_num -> y \in int_num -> x + y \in int_num.
  Check @rpredB algC _ x y : x \in int_num -> y \in int_num -> x - y \in int_num.
  Check @rpredM algC _ x y : x \in int_num -> y \in int_num -> x * y \in int_num.
  
  Check (mc_2_0.Num_int_num_subdef__canonical__GRing_Mul2Closed
           Algebraics.Implementation_type__canonical__Num_ArchiNumDomain) : opprClosed algC.

(*
  MathComp 2.0.0 のとき：
  
  Check Cint : opprClosed algC.
  Check Cint : addrClosed algC.
  Check Cint : zmodClosed algC.
  Check Cint : GRing.Mul2Closed.type_ algC.

  Check @rpredN algC Cint x   : (- x \in Cint) = (x \in Cint).
  Check @rpredD algC Cint x y : x \in Cint -> y \in Cint -> x + y \in Cint.
  Check @rpredB algC Cint x y : x \in Cint -> y \in Cint -> x - y \in Cint.
  Check @rpredM algC Cint x y : x \in Cint -> y \in Cint -> x * y \in Cint.
*)
End ALGC.

(**
参考のために、オリジナルな定義を示す。
*)
Section Orig.
  Variable U V : zmodType.
  Variable f g : {additive U -> V}.
  
  Check @raddfN U V f : {morph f : x / - x >-> - x}.
  Check @raddfD U V f : {morph f : x y / x + y >-> x + y}.
  Check @raddfB U V f : {morph f : x y / x - y >-> x - y}.

  Variable S1 : opprClosed V.
  Variable S2 : addrClosed V.
  Variable S3 : zmodClosed V.
  Variable R : semiRingType.
  
  Check @rpredN V S1 : {mono -%R : u / u \in S1}.
  Check @rpredD V S2 : {in S2 &, forall u v : V, u + v \in S2}.
  Check @rpredB V S3 : {in S3 &, forall u v : V, u - v \in S3}.
  Check @rpredM R : forall s : mulr2Closed R, GRing.mulr_2closed (R:=R) s.
End Orig.

(**
## algC のみの補題

Serch algC.
 *)
Check @algCrect : forall x : algC, x = 'Re x + 'i * 'Im x. (* 前出 *)

(**
マルチルール。便利そうだが、まだ使わない。
*)
Check (1, 1) : algC * algC.
Check CintrE.                               (* 略 *)
Check CratrE.                               (* 略 *)

(**
# 問11. ガウス整数 a が単元であることと、a が ±1 か ±i であることは、同値である ...
  を解くための補題
*) 

(**
## ノルムが1であることと、±1 または ±i であることは同値 の証明

同値変換でこの形に変換していく。
 *)
Section Ex11.
  Variable a : algC.

  (* gaussNorm (algGI a) == 1. *)

  (* 実部と虚部の2乗和にする。 *)
  Check algCrect : forall x : algC, x = 'Re x + 'i * 'Im x.
  (* goal *) Check 'Re (a) ^+ 2 + 'Im (a) ^+ 2 == 1.
  
  (* 2乗和が1なので、1と0 または 0と1 の加算にする。 *)
  Check normC2_rect : forall C : numClosedFieldType,
      {in Num.real &, forall x y : C, normr (x + 'i * y) ^+ 2 = x ^+ 2 + y ^+ 2}.
  (* goal *) 
  Check ('Re (a) ^+ 2 == 1) && ('Im (a) ^+ 2 == 0)
        ||
        ('Re (a) ^+ 2 == 0) && ('Im (a) ^+ 2 == 1).
  
  (* 2乗を消す。 *)
  Check sqrf_eq0 : forall (R : idomainType) (x : R), (x ^+ 2 == 0) = (x == 0).
  Check sqrf_eq1 : forall (R : idomainType) (x : R), (x ^+ 2 == 1) = (x == 1) || (x == -1).
  (* goal *)   
  Check (('Re (a) == 1) || ('Re (a) == -1)) && ('Im (a) == 0)
        ||
        ('Re (a) == 0) && (('Im (a) == 1) || ('Im (a) == -1)).
  
  (* 選言標準形にする。 *)
  (* goal *)
  Check [|| ('Re (a) == 1) && ('Im (a) == 0),
            ('Re (a) == -1) && ('Im (a) == 0),
            ('Re (a) == 0) && ('Im (a) == 1)
          | ('Re (a) == 0) && ('Im (a) == -1)].
End Ex11.  

(* その他の補題 *)
Check Creal_Re : forall (C : numClosedFieldType) (x : C), 'Re x \is Num.real.
Check Creal_Im : forall (C : numClosedFieldType) (x : C), 'Im x \is Num.real.
Check Cnat_exp_even : forall (x : algC) (n : nat), ~~ odd n -> x \is a int_num -> x ^+ n \is a nat_num.
Check raddfN : forall (U V : zmodType) (f : {additive U -> V}), {morph f : x / - x >-> - x}.
Check Re_i : forall C : numClosedFieldType, 'Re 'i = 0.
Check Im_i : forall C : numClosedFieldType, 'Im 'i = 1.
Check Creal_ReP : forall (C : numClosedFieldType) (z : C), reflect ('Re z = z) (z \is Num.real).
Check Creal_ImP : forall (C : numClosedFieldType) (z : C), reflect ('Im z = 0) (z \is Num.real).


(**
# 予備
 *)
Check Num.IntegralDomain_isNumRing.Build algC.
Check Num.NumField_isImaginary.Build algC.
Check GRing.ClosedField.on algC.
Check isComplex.Build algC.
Check isCountable.Build algC.

Check GRing.isZmodule.Build algC.
Fail Check GRing.isAdditive.Build algC.
Check GRing.Zmodule_isComRing.Build algC.
Check GRing.ComRing_isField.Build algC.
Check Field_isAlgClosed.Build algC.
Check isComplex.Build algC.
Fail Check GRing.isSubringClosed.Build algC.
Fail Check GRing.isSemiringClosed.Build algC.
Fail Check GRing.isZmodClosed.Build algC.
Fail Check GRing.isDivringClosed.Build algC.

(* END *)
