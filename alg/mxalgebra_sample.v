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
 *)
(**
## rank に関連する関数
 *)
(* 階数が行数と同じことを row_free と呼ぶ。 *)
Check row_free : forall (F : fieldType) (m n : nat), 'M_(m, n) -> bool.
Print row_free. (* = fun (F : fieldType) (m n : nat) (A : 'M_(m, n)) => \rank A == m *)

(**
## rank に関連するbool述語
*)

(**
## rank に関連する補題
*)

(* 逆行列が存在すること（正則であること）と、row_freeは同値 *)
Check @row_freeP F m n A : reflect (exists B : 'M_(n, m), A *m B = 1%:M) (row_free A).

(**
# Kernel 核
*)

(**
## kernelに関連する関数
*)
Check @complmx.
Print complmx.

Check kermx : forall (F : fieldType) (m n : nat), 'M_(m, n) -> 'M_m.
Print kermx.

(* 行列のカーネル : 'M_(m, n) な行列 A にたいして。``a * M = 0`` なる、横(row)ベクトル a *)
(* kermx 関数は、行列のカーネルをすべて返す。 *)
Check @kermx F m n : 'M_(m, n) -> 'M_m.     (* 引数は A *)
Check kermx : forall (F : fieldType) (m n : nat) (A : 'M_(m, n)), 'M_m.
Check let LUr := Gaussian_elimination A in
      (copid_mx (\rank A)) *m (invmx (col_ebase A)).

(**
## kernelに関連するbool述語
*)

(**
## kernelに関連する補題
*)

(* 行列のカーネルがすべて0であることと、正則行列であることは同値 *)
Check @kermx_eq0 F n m A : (kermx A == 0) = row_free A.



Search kermx.

Check cokermx.


(* END *)
