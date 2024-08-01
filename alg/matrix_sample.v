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
# マトリクス型の表記
*)

(**
R型で 寸法m, nのマトリクス型。寸法は自然数で指定する。
 *)
Locate "'M[ _ ]_ ( _ , _ )".           (* := (matrix R m n) : type_scope *)
Check matrix R m n : predArgType. (* m n は本当に自然数 *)

(**
``i < 'I_m`` と ``j < 'I_n`` の直積``(i, j)``から R を返す関数
``(i, j)`` はfinTypeなので、この関数は finfun である。
 *)
Check {ffun 'I_m * 'I_n -> R}.

(**
マトリクス型の実体は、この finfun である。これをマトリクス型にする表記
*)
Locate "\matrix[ k ]_ ( i , j ) E". (* := (matrix_of_fun.body k (fun i j => E)) *)
Check matrix_of_fun : forall (R : Type) (m n : nat), unit -> ('I_m -> 'I_n -> R) -> 'M_(m, n).


(**
# マトリクス型の作り方
*)

(**
コンストラクタ Matrix は、finfun型をとって、マトリクス型を返す。
*)
Check Matrix : forall (R : Type) (m n : nat), (* R型と寸法m, nは与える。 *)
    {ffun 'I_m * 'I_n -> R} ->
    matrix R m n.
(**
Variant matrix (R : Type) (m n : nat) : predArgType :=
        Matrix : {ffun 'I_m * 'I_n -> R} -> 'M_(m, n).
*)

(**
マトリクス型からfinfunを返す関数
*)
Check mx_val : forall (R : Type) (m n : nat),
    matrix R m n ->
    {ffun 'I_m * 'I_n -> R}. (* ``i < 'I_m`` と ``j < 'I_n`` から R を返す関数(funfun)を返す。 *)

(**
マトリクス型を funfun をカリー化した関数に変換する関数
コアーションとして使われる。
*)
Check fun_of_matrix : forall (R : Type) (m n : nat),
    matrix R m n -> ('I_m -> 'I_n -> R).

(**
 funfun をカリー化した関数をマトリクス型に変換する関数
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
# mxE
 *)
Check mxE : forall (R : Type) (m n : nat) (k : unit) (F : 'I_m -> 'I_n -> R),
    fun_of_matrix (\matrix[k]_(i, j) F i j) =2 F.
(* 両辺は、``'I_m -> 'I_n -> R`` *)

(**
# matrixP.
 *)
Check matrixP : forall (R : Type) (m n : nat) (A B : 'M_(m, n)), A =2 B <-> A = B.

(**
# eq_mx
 *)
Check @eq_mx : forall (R : Type) (m n : nat) (k : unit) (F1 F2 : 'I_m -> 'I_n -> R),
    F1 =2 F2 ->
    (\matrix[k]_(i, j) F1 i j)%R = (\matrix[k]_(i, j) F2 i j)%R.

End MatrixDef.

(* END *)
