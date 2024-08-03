From elpi Require Import elpi.
From HB Require Import structures.
From mathcomp Require Import all_ssreflect.
From mathcomp Require Import all_algebra.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section MatrixDef.

Variable R : Type.
Variables m n : nat.

(**
# マトリクス型の表記（基本）
*)

(**
R型で 寸法m, nのマトリクス型。寸法は自然数で指定する。
 *)
Locate "'M[ _ ]_ ( _ , _ )".           (* := (matrix R m n) : type_scope *)
Check matrix R m n : predArgType.      (* m n は本当に自然数 *)


(**
Ordinal型 ``i < 'I_m`` と ``j < 'I_n`` の直積``(i, j)``から R を返す関数
``(i, j)`` は finType なので、この関数は finfun型 である。
 *)
Check {ffun 'I_m * 'I_n -> R}.

(**
マトリクス型の実体は、この finfun ``(fun i j => E)`` である。これをマトリクス型にする。
*)
Locate "\matrix_ ( i  < m , j < n ) E". (* := (matrix_of_fun matrix_key (fun i j => E)) *)
Locate "\matrix[ k ]_ ( i , j ) E".     (* := (matrix_of_fun k          (fun i j => E)) *)
Check matrix_of_fun : forall (R : Type) (m n : nat), unit -> ('I_m -> 'I_n -> R) -> 'M_(m, n).

(**
# マトリクス型の作り方
*)
(**
Variant matrix (R : Type) (m n : nat) : predArgType :=
        Matrix : {ffun 'I_m * 'I_n -> R} -> 'M_(m, n).
*)

(**
コンストラクタ Matrix は、finfun をとって、マトリクス型を返す。
*)
Check Matrix : forall (R : Type) (m n : nat), (* R型と寸法m, nは与える。 *)
    {ffun 'I_m * 'I_n -> R} ->
    matrix R m n.

(**
マトリクス型からfinfunを返す関数
*)
Check mx_val : forall (R : Type) (m n : nat),
    matrix R m n ->
    {ffun 'I_m * 'I_n -> R}. (* ``i < 'I_m`` と ``j < 'I_n`` から R を返す関数(funfun)を返す。 *)

(**
マトリクス型を funfun をカリー化した関数に変換する関数

これはコアーションとして働くので、マトリクス型にインデックスとしてordinal型の引数を与えることができる。
*)
Check fun_of_matrix : forall (R : Type) (m n : nat),
    matrix R m n -> ('I_m -> 'I_n -> R).

Variable A : 'M[R]_(2, 3).
Check A (Ordinal (_ : 1 < 2)) (Ordinal (_ : 1 < 3)).
Check (fun_of_matrix A) (Ordinal (_ : 1 < 2)) (Ordinal (_ : 1 < 3)).

(**
## funfun をカリー化した関数をマトリクス型に変換する関数
*)
Check matrix_of_fun : forall (R : Type) (m n : nat),
    unit -> ('I_m -> 'I_n -> R) -> matrix R m n.
(**
Definition matrix_of_fun R (m n : nat) (k : unit) (F : 'I_m -> 'I_n -> R) :=
  @Matrix R m n [ffun (l : ('I_m * 'I_n) => F l.1 l.2].
*)

(**
# 重要な補題
*)

(**
## mxE
 *)
Check mxE : forall (R : Type) (m n : nat) (k : unit) (F : 'I_m -> 'I_n -> R),
    (\matrix[k]_(i, j) F i j)%R =2 F.
Check mxE : forall (R : Type) (m n : nat) (k : unit) (F : 'I_m -> 'I_n -> R),
    fun_of_matrix (\matrix[k]_(i, j) F i j) =2 F.
Check mxE : forall (R : Type) (m n : nat) (k : unit) (F : 'I_m -> 'I_n -> R),
    (@fun_of_matrix R m n (@matrix_of_fun.body R m n k F)) =2 F.
(* 両辺は、``'I_m -> 'I_n -> R`` *)

(**
## matrixP.
 *)
Check matrixP : forall (R : Type) (m n : nat) (A B : 'M_(m, n)),
    A =2 B <-> A = B.                       (* 左は、fun_of_matrix のコアーション *)
(* 右はマトリクス型どうし *)

(**
## eq_mx
 *)
Check @eq_mx : forall (R : Type) (m n : nat) (k : unit) (F1 F2 : 'I_m -> 'I_n -> R),
    F1 =2 F2 ->
    (\matrix[k]_(i, j) F1 i j)%R = (\matrix[k]_(i, j) F2 i j)%R.


(**
# マトリクス型の表記（応用）

標準的な教科書では、列ベクトル（縦ベクトル）、行ベクトル（横ベクトル）の順
*)
Locate "'M[ R ]_ ( m , n )".      (* := (matrix R m n) : type_scope *)
Locate "'M[ R ]_ ( n )".          (* := (matrix R n n) : type_scope 正方行列 *)
Locate "'cV[ R ]_ n ".            (* := (matrix R n 1) : type_scope 列ベクトル *)
Locate "'rV[ R ]_ n ".            (* := (matrix R 1 n) : type_scope 行ベクトル *)

Locate "\matrix_ ( i  < m , j < n ) E". (* := (matrix_of_fun matrix_key (fun i j => E)) *)
Locate "\col_ ( i < m ) E". (* := (matrix_of_fun matrix_key (fun i _ => E)) *)
Locate "\row_ ( j < n ) E". (* := (matrix_of_fun matrix_key (fun _ j => E)) *)

Locate "\matrix[ k ]_ ( i , j ) E". (* := (matrix_of_fun k          (fun i j => E)) *)
Locate "\col_ i E".                 (* := (matrix_of_fun matrix_key (fun i _ => E)) *)
Locate "\row_ i E".                 (* := (matrix_of_fun matrix_key (fun _ j => E)) *)

(* E は Row を返す式。matrix型はRowベクトルのベクトルではないが、これは用意されている。 *)
Locate "\matrix_ ( i < m ) E ". (* := (matrix_of_fun matrix_key (fun i j => E GRing.zero j)) *)

End MatrixDef.

(**
#
 *)
Section MatrixStructural.

Variable R : Type.
Variable a : R.
Variable m n : nat.

(**
## 関数
 *)
Check @const_mx R m n a.

Check @map_mx.

Check @map2_mx.

Locate "A ^T".                              (* := (trmx A) *)

(**
## 補題
*)

(**
# 列と行の入れ替え
*)

(**
## 関数
 *)
(* j0列目を列ベクトルとして取り出す。関数は ``fun i => A i j0`` *)
Print col. (* = fun (R : Type) (m n : nat) (j0 : 'I_n) (A : 'M_(m, n)) => (\col_i A i j0)%R *)
(* i0列目を列ベクトルとして取り出す。関数は ``fun j => A i0 j`` *)
Print row. (* = fun (R : Type) (m n : nat) (i0 : 'I_m) (A : 'M_(m, n)) => (\row_j A i0 j)%R *)

(* j0列以外の行列を取り出す。j0を切り取る。 *)
Check col' : forall (R : Type) (m n : nat), 'I_n -> 'M_(m, n) -> 'M_(m, n.-1).
Print col'. (* = fun R m n (j0 : 'I_n) A => (\matrix_(i, j) A i (lift j0 j))%R *)
(* i0行以外の行列を取り出す。i0を切り取る。 *)
Check row' : forall (R : Type) (m n : nat), 'I_m -> 'M_(m, n) -> 'M_(m.-1, n).
Print row'. (* = fun R m n (i0 : 'I_m) A => (\matrix_(i, j) A (lift i0 i) j)%R *)

(* j1列とj2列を入れ替えた行列を取り出す。 *)
Check xcol : forall (R : Type) (m n : nat), 'I_n -> 'I_n -> 'M_(m, n) -> 'M_(m, n).
Print xcol. (* = fun R m n (j1 j2 : 'I_n) => col_perm (perm.tperm j1 j2) *)
(* i1行とi2行を入れ替えた行列を取り出す。 *)
Check xrow : forall (R : Type) (m n : nat), 'I_m -> 'I_m -> 'M_(m, n) -> 'M_(m, n).
Print xrow. (* = fun R m n (i1 i2 : 'I_m) => row_perm (perm.tperm i1 i2) *)

(* 列を置き換え s した行列を取り出す。 *)
Check row_perm : forall (R : Type) (m n : nat), perm.perm_of 'I_m -> 'M_(m, n) -> 'M_(m, n).
Print row_perm. (* = fun R m n (s : perm.perm_of 'I_m) A =>
                   (\matrix[row_perm_key]_(i, j) A (perm.fun_of_perm s i) j)%R *)
(* 行を置き換え s した行列を取り出す。 *)
Check col_perm : forall (R : Type) (m n : nat), perm.perm_of 'I_n -> 'M_(m, n) -> 'M_(m, n).
Print row_perm. (* = fun R m n (s : perm.perm_of 'I_m) (A : 'M_(m, n)) =>
                   (\matrix[row_perm_key]_(i, j) A (perm.fun_of_perm.body s i) j)%R *)

(**
## 補題
*)

End MatrixStructural.

(* END *)
