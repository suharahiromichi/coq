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
Variable A B C : 'M[F]_(m, n).

(**
# Rank 階数

## rank に関連する関数
 *)
Locate "\rank A".                 (* := (mxrank.body A) : nat_scope *)
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
包含関係など
*)
Check submx A B : bool.
Check ltmx A B : bool.
Check eqmx A B : Prop.
Check genmx A : 'M_n.
Check addsmx A B : 'M_n.

(**
## rank に関連する補題
*)
(* 逆行列が存在すること（正則であること）と、row_freeは同値 *)
Check @row_freeP F m n A : reflect (exists B : 'M_(n, m), A *m B = 1%:M) (row_free A).

(* 逆行列が存在すること（正則であること）と、row_fullは同値 *)
Check @row_fullP F m n A : reflect (exists B : 'M_(n, m), B *m A = 1%:M) (row_full A).

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


(**
## %MS - scope MS (matrix set space)
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
Locate "A :\: B".                           (* := (diffmx.body A B) *)
Locate "A \in R".                           (* := (submx (mxvec A) R) *)
Locate "A * R".                             (* := (mulsmx R S) *)

(* END *)
