From elpi Require Import elpi.
From HB Require Import structures.
From mathcomp Require Import all_ssreflect.
From mathcomp Require Import all_algebra.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Num.Theory Num.Def.
Import GRing.Theory.
Open Scope ring_scope.

Variables m n p : nat.                      (* 行列の寸法 *)
Variable F : fieldType.
Variable A : 'M[F]_(m, n).

(**
# Rank 階数

## rank に関連する関数
 *)
Locate "\rank A".                 (* := (mxrank A) : nat_scope *)
Check \rank A : nat.              (* 自然数を返す。 *)
Check @mxrank F m n A : nat.

(**
## rank に関連するbool述語
*)
Check row_free A : bool.
Check row_free : forall (F : fieldType) (m n : nat), 'M_(m, n) -> bool.

(* 階数が行数と同じ。 *)
Print row_free. (* = fun F m n A) => \rank A == m *)
(* 階数が列数と同じ。 *)
Print row_full. (* = fun F m n A) => \rank A == n *)

Print col_ebase.
Print row_ebase.
Print col_base.
Print row_base.

(**
## rank に関連する補題
*)
(* 逆行列が存在すること（正則であること）と、row_freeは同値 *)
Check @row_freeP F m n A : reflect (exists B : 'M_(n, m), A *m B = 1%:M) (row_free A).

(* 逆行列が存在すること（正則であること）と、row_fullは同値 *)
Check @row_fullP F m n A : reflect (exists B : 'M_(n, m), B *m A = 1%:M) (row_full A).


(**
# マトリクススペース(%MS)
 *)
Section MS.
  Variable m2 : nat.
  Variable B : 'M[F]_(m2, n).
  
(**
## マトリクススペース(%MS)の関数
*)
(* 小行列、部分行列ではない。 *)
(* Aの行空間がBの行空間に含まれる。 *)
Check submx A B : bool.                     (* <= *)
(* A <= B かつ ~~(B <= A) *)
Check ltmx A B : bool.                      (* < *)
(* A と B の階数が同じで、任意の行列Cに対して、 ((A <= C) = (B <= C)) * ((C <= A) = (C <= B)) *)
Check eqmx A B : Prop.                      (* :=: *)

(* m✖️n行列の行空間の基底。
   n次の正方行列で1%:Mまたは、その余計なところを0にしたもの。 *)
Check genmx A : 'M_n.                       (* << A >> *)
(* 正則行列なら単位行列、さもなければ、階数の部分単位行列PIDにガウスの掃き出し法のL(.1.2)を掛ける。 *)

(* 行列の行空間どうしのの和空間 << col_mx A B>>
   連結した行列に対して、行空間の基底を求める *)
(* A Bの列数は同じ n であること。値はnの正方行列 *)
Check addsmx A B : 'M_n.                    (* + *)

(* 行空間（行ベクトルの張る空間）どうしの交空間 *)
(* A Bの列数は同じ n であること。値はnの正方行列 *)
Check capmx A B : 'M_n.                     (* :&: *)

(* 行空間どうしの差空間 *)
Check diffmx A B : 'M_n.                    (* :\: *)

(**
## マトリクススペース(%MS)の補題
*)
(* 自明なもの。 *)
Check @submx_refl F m n A : (A <= A)%MS.
Check @addsmxSl F m m2 n A B : (A <= A + B)%MS.
Check @addsmxSr F m m2 n A B : (B <= A + B)%MS.
Check @capmxSr F m m2 n A B : (A :&: B <= B)%MS.
Check @capmxSl F m m2 n A B : (A :&: B <= A)%MS.
Check @diffmxSl F m m2 n A B : (A :\: B <= A)%MS.

(* 行列Aの行空間がBの行空間の部分空間なら、Aの階数はBの階数以下である。 *)
Check @mxrankS F m m2 n A B : (A <= B)%MS -> (\rank A <= \rank B)%N.

(* 任意の行列の行空間は、単位行列の行空間に含まれる。 *)
Check @submx1 F m n A : (A <= 1%:M)%MS.
(* 行空間が単位行列の行空間と同じであることと、正則行列であることは同値 *)
Check @sub1mx F m n A : (1%:M <= A)%MS = row_full A.
(* 零行列の行空間と同じであることと、零行列であることは同値 *)
Check @submx0 F m n A : (A <= 0)%MS = (A == 0).
(* 零行列の行空間は、任意の行列区間の行空間を含む。 *)
Check @sub0mx F m _ n A : (0 <= A)%MS.

(* 行列Aの行空間が、行列BとCの行空間の交空間を含むことと、
   行列Aの行空間が行列Cの行空間を含み、かつ、行列Bの行空間が行列Cの行空間を含むことと同じ。 *)
Check @sub_capmx F : forall (m m1 m2 n : nat) (A : 'M_(m, n)) (B : 'M_(m1, n)) (C : 'M_(m2, n)),
    (A <= B :&: C)%MS = (A <= B)%MS && (A <= C)%MS.

End MS.

(**
# Kernel 核

## kernelに関連する関数
*)

Check complmx A : 'M_n.
Print complmx.

(* 行列のカーネル : 'M_(m, n) な行列 A にたいして。``a * M = 0`` なる、横(row)ベクトル a *)
(* kermx 関数は、行列のカーネルをすべて返す。 *)
Check kermx A : 'M_m.
Check @kermx F m n : 'M_(m, n) -> 'M_m.     (* 引数は A *)

Print kermx.                 (* copid_mx mxrank *m invmx col_ebase. *)
(* 上記の mxrank がローカルなので、複雑な式に見える。 *)

(* 途中に出てくる式 *)
Check let LUr := Gaussian_elimination A in
      (copid_mx (\rank A)) *m (invmx (col_ebase A)).

Check cokermx A : 'M_n.
Print cokermx.


(**
## kernelに関連するbool述語
*)
(* 行列のカーネルがすべて0であることと、正則行列であることは同値 *)
Check @kermx_eq0 F n m A : (kermx A == 0) = row_free A.

Check @cokermx_eq0 F n m A : (cokermx A == 0) = row_full A.

(**
## kernelに関連する補題
*)
(* 行列 B と A の積が 0 であることと、Bの行空間がAの核の行空間に含まれることは、同値である *)
Check @sub_kermxP F : forall (p m n : nat) (A : 'M_(m, n)) (B : 'M_(p, m)),
    reflect (B *m A = 0) (B <= kermx A)%MS.

(**
## %MS - scope MS (matrix set space)

マトリクススペース
*)

Locate "A <= B".                            (* := (submx A B) *)
Locate "A < B".                             (* := (ltmx A B) *)
Locate "A <= B <= C".                       (* := (andb (submx A B) (submx B C)) *)
Locate "A == B".                            (* := (andb (submx A B) (submx B A)) *)
Locate "A :=: B".                           (* := (eqmx A B) *)
Locate "<< A >>".                           (* := (genmx A) *)
Locate "\sum_ i B". 
Locate "A + B".                             (* := (addsmx A B) *)
Locate "A :&: B".                           (* := (capmx A B) *)
Locate "\bigcap_ i B".
Locate "A ^C".                              (* := (complmx A) *)
Locate "A :\: B".                           (* := (diffmx A B) *)
Locate "A \in R".                           (* := (submx (mxvec A) R) *)
Locate "A * R".                             (* := (mulsmx R S) *)

(* END *)
