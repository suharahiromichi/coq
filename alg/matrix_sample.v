From elpi Require Import elpi.
From HB Require Import structures.
From mathcomp Require Import all_ssreflect.
From mathcomp Require Import all_algebra.
From mathcomp Require Import all_fingroup.  (* perm *)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Open Scope ring_scope.

(**
概要
- マトリクス型の表記（基本）
- マトリクス型の作り方
- 重要な補題
  - mxE
  - matrixP
  - eq_mx
- マトリクス型の応用
  - 表記
  - 補題
- 行列の構造
  - 関数
    - 定数行列
    - 転置行列
  - 補題
    - 転置する前と後
- 列（行）の入れ替え、列（行）の取り出し
  - 関数
  - 補題
- block matrix ブロック行列 区分行列 小行列を繋ぎ合わせる。
  - 関数
  - 補題
- submatrix 部分行列 小行列を取り出す。
  - 関数
  - 補題
- square matrix 正方行列、diagonal matrix 対角行列
  - 関数
  - 補題
- おまけ - 0行、0列とはなにか  
*)

Section MatrixDef.

Variable R : Type.
Variables m n p : nat.

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
Check {ffun 'I_m * 'I_n -> R} : predArgType.

(**
マトリクス型の実体は、この finfun ``(fun i j => E)`` である。これをマトリクス型にする。

k についてはよくわからない。
*)
Locate "\matrix_ ( i  < m , j < n ) E". (* := (matrix_of_fun matrix_key (fun i j => E)) *)
Locate "\matrix[ k ]_ ( i , j ) E".     (* := (matrix_of_fun k          (fun i j => E)) *)
Check matrix_of_fun : forall R m n, unit -> ('I_m -> 'I_n -> R) -> 'M_(m, n).

(**
# マトリクス型の作り方
*)
(**
Variant matrix R m n : predArgType :=
        Matrix : {ffun 'I_m * 'I_n -> R} -> 'M_(m, n).
*)

(**
コンストラクタ Matrix は、finfun をとって、マトリクス型を返す。
*)
Check Matrix : forall R m n, (* R型と寸法m, nは与える。 *)
    {ffun 'I_m * 'I_n -> R} ->
    matrix R m n.

(**
マトリクス型からfinfunを返す関数
*)
Check mx_val : forall R m n,
    matrix R m n ->
    {ffun 'I_m * 'I_n -> R}. (* ``i < 'I_m`` と ``j < 'I_n`` から R を返す関数(funfun)を返す。 *)

(* isNew でサブタイプになっているので、\var が使える。 *)
Check val : matrix R m n -> {ffun 'I_m * 'I_n -> R}.
Goal @mx_val R m n = val. Proof. done. Qed.

(**
マトリクス型を、funfunをカリー化した関数に変換する関数

これはコアーションとして働くので、マトリクス型にインデックスとしてordinal型の引数を与えることができる。
*)
Check fun_of_matrix : forall R m n,
    matrix R m n -> ('I_m -> 'I_n -> R).

Variable A : 'M[R]_(2, 3).
(* Check A (Ordinal (_ : 1 < 2)) (Ordinal (_ : 1 < 3)). *)
(* Check (fun_of_matrix A) (Ordinal (_ : 1 < 2)) (Ordinal (_ : 1 < 3)). *)

(**
## funfunをカリー化した関数を、マトリクス型に変換する関数
*)
Check matrix_of_fun : forall R m n,
    unit -> ('I_m -> 'I_n -> R) -> matrix R m n.
(**
Definition matrix_of_fun R (m n : nat) (k : unit) (F : 'I_m -> 'I_n -> R) :=
  @Matrix R m n [ffun (l : ('I_m * 'I_n) => F l.1 l.2].
*)

(**
# 三つの重要な補題

恣意的な例：
*)
Goal 1%:M = 1%:M :> 'M[nat]_(n, n).
Proof.
  Set Printing Coercions.
  (* 行列の``=``を関数の``=``として、関数値の``=``にする。 *)
  apply/matrixP => i j.
  Check 1%:M i j = 1%:M i j.
  Check fun_of_matrix 1%:M i j = fun_of_matrix 1%:M i j.
  
  (* 行列の要素どうしの``=``にする。fun_of_matrix が消える。 *)
  rewrite mxE.
  Check (i == j)%:R = (i == j)%:R.
  Check (nat_of_bool (i == j))%:R = (nat_of_bool (i == j))%:R.
  Restart.
  
  (* 上記を同時に行う。 *)
  apply/eq_mx => i j.
  done.
  Unset Printing Coercions.
Qed.

(**
## mxE

左から右への書き換えで、fun_of_matrix が消えることに気づいてください。
行列を関数とみなした式から、行列の中身の式に書き換えられる。
 *)
Check mxE : forall R m n (k : unit) (F : 'I_m -> 'I_n -> R),
    (\matrix[k]_(i, j) F i j)%R =2 F.

Check mxE : forall R m n (k : unit) (F : 'I_m -> 'I_n -> R),
    fun_of_matrix (\matrix[k]_(i, j) F i j) =2 F.

Check mxE : forall R m n (k : unit) (F : 'I_m -> 'I_n -> R),
    (@fun_of_matrix R m n (@matrix_of_fun.body R m n k F)) =2 F.
(* 両辺は、``'I_m -> 'I_n -> R`` *)

(**
## matrixP.

行列の``=``を、関数の``=``にする。
 *)
Check matrixP : forall R m n (A B : 'M_(m, n)),
    A =2 B <-> A = B.                       (* 左は、fun_of_matrix のコアーション *)
(* 右はマトリクス型どうし *)

(**
## eq_mx

\matrix[k]_(i, j)(F i j) の F を書き換える。bigop の eq_big と同じ。
 *)
Check @eq_mx : forall R m n (k : unit) (F1 F2 : 'I_m -> 'I_n -> R),
    F1 =2 F2 ->
    (\matrix[k]_(i, j) F1 i j)%R = (\matrix[k]_(i, j) F2 i j)%R.

(**
# マトリクス型の応用
 *)

(**
## 表記

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

(* ``\matrix_ i E`` で、一次元の i と、Eは 行ベクトルを返す関数。
   matrix型はベクトルのベクトルではないが、これは用意されている。 *)
Locate "\matrix_ ( i < m ) E ". (* := (matrix_of_fun matrix_key (fun i j => E GRing.zero j)) *)

(**
## 補題
 *)
(* ``'cV_n = matrix R n 1`` 1 のことろは固定値(0)なので、もうひとつの引数で同じ (``=1``) なら、同じ。  *)
Check colP : forall R m (u v : 'cV_m), u^~ 0%R =1 v^~ 0%R <-> u = v.

(* ``'rV_n = matrix R 1 n`` 1 のことろは固定値(0)なので、もうひとつの引数で同じ (``=1``) なら、同じ。  *)
Check rowP : forall R n (u v : 'rV_n), u 0%R =1 v 0%R <-> u = v.

End MatrixDef.

(**
# 行列の構造
 *)
Section MatrixStructural.

Variable R : Type.
Variable a : R.
Variable m n : nat.

(**
## 関数
 *)
(* 定数行列 *)
Check @const_mx R m n a : 'M_(m, n).        (* Notation はない。 *)
Print const_mx. (* = fun R m n (a : R) => (\matrix[const_mx_key]_(_, _) a)%R  *)

(* 要素のすべてに f を適用する。 *)
Locate "A ^ f".                             (* := map_mx A f *)
Check @map_mx : forall aT rT : Type, (aT -> rT) -> forall m n : nat, 'M_(m, n) -> 'M_(m, n).
Print map_mx.                   (* = fun aT rT (f : aT -> rT) m n A =>
                                   (\matrix[map_mx_key]_(i, j) f (A i j))%R *)

(* ふたつの行列の要素どうしに f を適用する。 *)
Check @map2_mx                              (* Notaion はない。 *)
  : forall R S T : Type, (R -> S -> T) -> forall m n : nat, 'M_(m, n) -> 'M_(m, n) -> 'M_(m, n).
Print map2_mx.             (* = fun R S T (f : R -> S -> T) m n A B =>
                              (\matrix[map2_mx_key]_(i, j) f (A i j) (B i j))%R *)

(* 転置行列 *)
Locate "A ^T".                              (* := (trmx A) *)
Check @trmx : forall R m n, 'M_(m, n) -> 'M_(n, m). (* インデックス i j を入れ替える。 *)
Print trmx. (* = fun R m n (A : 'M_(m, n)) => (\matrix[trmx_key]_(i, j) A j i)%R *)

(**
## 補題
*)

(* 転置する前と後 *)
(* row_perm して転置するのは、転置して col_perm するのと同じ。 *)
(* row_perm などの定義はすぐ後 *)
Check tr_row_perm : forall R m n (s : 'S_m) A, ((row_perm s A)^T)%R = col_perm s A^T.
Check tr_col_perm : forall R m n (s : 'S_n) A, ((col_perm s A)^T)%R = row_perm s A^T.
Check tr_xrow : forall R m n (i1 i2 : 'I_m) A, ((xrow i1 i2 A)^T)%R = xcol i1 i2 A^T.
Check tr_xcol : forall R m n (j1 j2 : 'I_n) A, ((xcol j1 j2 A)^T)%R = xrow j1 j2 A^T.
Check tr_row  : forall R m n (i0 : 'I_m) A, ((row i0 A)^T)%R = col i0 A^T.
Check tr_col  : forall R m n (j0 : 'I_n) A, ((col j0 A)^T)%R = row j0 A^T.
Check tr_row' : forall R m n (i0 : 'I_m) A, ((row' i0 A)^T)%R = col' i0 A^T.
Check tr_col' : forall R m n (j0 : 'I_n) A, ((col' j0 A)^T)%R = row' j0 A^T.

(**
# 列（行）の入れ替え、列（行）の取り出し
*)
(**
## 関数
 *)
(* j0列目を列ベクトルとして取り出す。関数は ``fun i => A i j0`` *)
Print col. (* = fun R m n (j0 : 'I_n) (A : 'M_(m, n)) => (\col_i A i j0)%R *)
(* i0行目を行ベクトルとして取り出す。関数は ``fun j => A i0 j`` *)
Print row. (* = fun R m n (i0 : 'I_m) (A : 'M_(m, n)) => (\row_j A i0 j)%R *)

(* j0列目以外の行列を取り出す。j0を切り取る。 *)
Check col' : forall R m n, 'I_n -> 'M_(m, n) -> 'M_(m, n.-1).
Print col'. (* = fun R m n (j0 : 'I_n) A => (\matrix_(i, j) A i (lift j0 j))%R *)
(* i0行目以外の行列を取り出す。i0を切り取る。 *)
Check row' : forall R m n, 'I_m -> 'M_(m, n) -> 'M_(m.-1, n).
Print row'. (* = fun R m n (i0 : 'I_m) A => (\matrix_(i, j) A (lift i0 i) j)%R *)

(* j1列とj2列を入れ替えた行列を取り出す。 *)
Check xcol : forall R m n, 'I_n -> 'I_n -> 'M_(m, n) -> 'M_(m, n).
Print xcol. (* = fun R m n (j1 j2 : 'I_n) => col_perm (tperm j1 j2) *)
(* i1行とi2行を入れ替えた行列を取り出す。 *)
Check xrow : forall R m n, 'I_m -> 'I_m -> 'M_(m, n) -> 'M_(m, n).
Print xrow. (* = fun R m n (i1 i2 : 'I_m) => row_perm (tperm i1 i2) *)

(* 列を置き換え s した行列を取り出す。 *)
Check col_perm : forall R m n, perm_of 'I_n -> 'M_(m, n) -> 'M_(m, n).
(* 行を置き換え s した行列を取り出す。 *)
Check row_perm : forall R m n, perm_of 'I_m -> 'M_(m, n) -> 'M_(m, n).

(* 幅の同じ行列を連結する。縦（列）方向に連結。 *)
Check @col_mx : forall R m1 m2 n, 'M_(m1, n) -> 'M_(m2, n) -> 'M_(m1 + m2 , n).
(* 高さの同じ行列を連結する。横（行）方向に連結。 *)
Check @row_mx : forall R m n1 n2, 'M_(m, n1) -> 'M_(m, n2) -> 'M_(m, n1 + n2).
(* 高さと幅の同じ行列を連結する。ブロック行列（区分行列）をつくる。 *)
Check @block_mx : forall R m1 m2 n1 n2,
    'M_(m1, n1) -> 'M_(m1, n2) -> 'M_(m2, n1) -> 'M_(m2, n2) -> 'M_(m1 + m2, n1 + n2).

(* 指定要素だけ1の行列。対角ではない。 *)
Section s.
  Variable S : semiRingType.
  Variable i : 'I_m.                  (* 1 である行を指定する i < m *)
  Variable j : 'I_n.                  (* 1 である列を指定する i < n *)
  
  (* delta_mx i j までがマトリクス *)
  Check @delta_mx S m n i j : 'M_(m, n).
  Check delta_mx i j : 'M_(m, n).
End s.

(**
## 補題
*)
(* インデックス1個の ``\matrix_i u i`` の関数 u は、行ベクトルを返すので、
   行列のi0行目を行ベクトルとして取り出したものは、u の i0行目の行ベクトルと同じ。 *)
Check rowK : forall R m n (u_ : 'I_m -> 'rV_n) (i0 : 'I_m),
    row i0 (\matrix_i u_ i) = u_ i0 :> 'rV_n.

(* A の col_perm B の積は、A と B の row_perm の積に等しい。 *)
(* ``+`` について可換であること。証明は、acs_lesson7_proofcafe.v *)
Check mul_col_perm : forall R m n p (s : 'S_n) (A : 'M_(m, n)) (B : 'M_(n, p)),
    (col_perm s A *m B)%R = (A *m row_perm s^-1 B)%R.
Check mul_row_perm : forall R m n p (s : 'S_n) (A : 'M_(m, n)) (B : 'M_(n, p)),
    (A *m row_perm s B)%R = (col_perm s^-1 A *m B)%R.

Section a.
  Variable S : semiRingType.
  Variable p : nat.
  
  Goal forall (s : 'S_n) (A : 'M[S]_(m, n)) (B : 'M_(n, p)),
      (col_perm s A *m B)%R = (A *m row_perm s^-1 B)%R.
  Proof.
    move=> s A B.
    (* 関数値どうしの等式 *)
    apply/matrixP=> i k.
    (* 要素どうしの等式 *)
    rewrite 2!mxE.
    (* 左辺の j に s^-1 をかける。 *)
    Check reindex_perm s.            (* 加法は可換であること。 *)
    rewrite (reindex_perm s^-1) /=.
    (* 関数値どうしの等式 *)
    apply: eq_bigr => j _.
    (* 要素どうしの等式 *)
    rewrite 2!mxE.
    (* 置換 s (s^-1) は元にもどる。 *)
    Check @permKV : forall (T : finType) (s : {perm T}), cancel (s^-1)%g s.
    rewrite permKV.
    done.
  Qed.
End a.

(* i列目を列ベクトルとして取り出す関数は、(i, 0)だけが1の行列（単位列ベクトル）との積に等しい。 *)
Check colE : forall R m n (i : 'I_n) (A : 'M_(m, n)), col i A = (A *m delta_mx i 0)%R :> 'cV_m.
(* j行目を行ベクトルとして取り出す関数は、(0, j)だけが1の行列（単位行ベクトル）との積に等しい。 *)
Check rowE : forall R m n (j : 'I_m) (A : 'M_(m, n)), row j A = (delta_mx 0 j *m A)%R :> 'rV_n.

(* xcol でj1列とj2列を入れ替えた行列は、j1列とj2列を入れ替えた単位行列との積に等しい。 *)
Check xcolE : forall R m n (j1 j2 : 'I_n) (A : 'M_(m, n)), xcol j1 j2 A = (A *m tperm_mx j1 j2)%R.
(* xrow でi1行とi2行を入れ替えた行列は、i1行とi2行を入れ替えた単位行列との積に等しい。 *)
Check xrowE : forall R m n (i1 i2 : 'I_m) (A : 'M_(m, n)), xrow i1 i2 A = (tperm_mx i1 i2 *m A)%R.

(* 行列の任意の列を取り出した列ベクトルが一致であることと、行列が一致であることは、同値。 *)
(* row_matrixP があるのに、col_matrixP がないので、証明してみる。 *)
(* acs_lesson7_proofcafe.v *)
Lemma col_matrixP (A B : 'M_(m, n)) : (forall j : 'I_n, @col R m n j A = col j B) <-> A = B.
Proof.
  split=> [eqAB | -> //]; apply/matrixP=> i j.
  by move/colP/(_ i): (eqAB j); rewrite !mxE.
Qed.
(* 行列の任意の行を取り出した行ベクトルが一致であることと、行列は一致であることは、同値。 *)
Check row_matrixP : forall R m n A B, (forall i : 'I_m, row i A = row i B) <-> A = B.

(* perm しない（単位元 1g による perm) *)
Check col_perm1 : forall R m n A, col_perm 1%g A = A.
Check row_perm1 : forall R m n A, row_perm 1%g A = A.
(* perm t と perm s の合成 *)
Check col_permM : forall R m n (s t : 'S_n) A, col_perm (s * t) A = col_perm s (col_perm t A).
Check row_permM : forall R m n (s t : 'S_m) A, row_perm (s * t) A = row_perm s (row_perm t A).
(* col_perm と row_perm の入れ替えが可能 *)
Check col_row_permC : forall R m n (s : 'S_n) (t : 'S_m) A,
    col_perm s (row_perm t A) = row_perm t (col_perm s A).

(* 横方向に連結した行列の、連結する前の要素にアクセスする。 *)
Check row_mxEl : forall R m n1 n2 A1 A2 (i : 'I_m) (j : 'I_n1), row_mx A1 A2 i (lshift n2 j) = A1 i j.
Check row_mxEr : forall R m n1 n2 A1 A2 (i : 'I_m) (j : 'I_n2), row_mx A1 A2 i (rshift n1 j) = A2 i j.
(* 縦方向に連結した行列の、連結する前の要素にアクセスする。 *)
Check col_mxEu : forall R m1 m2 n A1 A2 (i : 'I_m1) (j : 'I_n), col_mx A1 A2 (lshift m2 i) j = A1 i j.
Check col_mxEd : forall R m1 m2 n A1 A2 (i : 'I_m2) (j : 'I_n), col_mx A1 A2 (rshift m1 i) j = A2 i j.

(* もとの行列のそれぞれの寸法が同じである場合、連結した行列が同じなら、連結する前の行列も同じ。 *)
(* A1とB1、A2とB2の寸法が同じなので、当然成り立つ。 *)
Check eq_row_mx : forall R m n1 n2
                         (A1 : 'M_(m, n1)) (A2 : 'M_(m, n2)) (B1 : 'M_(m, n1)) (B2 : 'M_(m, n2)),
    row_mx A1 A2 = row_mx B1 B2 -> A1 = B1 /\ A2 = B2.
Check eq_col_mx : forall R m1 m2 n
                         (A1 : 'M_(m1, n)) (A2 : 'M_(m2, n)) (B1 : 'M_(m1, n)) (B2 : 'M_(m2, n)),
    col_mx A1 A2 = col_mx B1 B2 -> A1 = B1 /\ A2 = B2.

End MatrixStructural.
(**
# block matrix ブロック行列 区分行列 （4つの小行列を繋ぎ合わせる）
 *)
(**
## 関数
 *)
Check @block_mx : forall (R : Type) (m1 m2 n1 n2 : nat),
    'M_(m1, n1) -> 'M_(m1, n2) -> 'M_(m2, n1) -> 'M_(m2, n2) -> 'M_(m1 + m2, n1 + n2).

(**
## 補題
 *)
(* もとの小行列のそれぞれの寸法が同じである場合、連結した行列が同じなら、連結する前の行列も同じ。 *)
Check eq_block_mx
  : forall (R : Type) (m1 m2 n1 n2 : nat)
           (Aul : 'M_(m1, n1)) (Aur : 'M_(m1, n2)) (Adl : 'M_(m2, n1)) (Adr : 'M_(m2, n2))
           (Bul : 'M_(m1, n1)) (Bur : 'M_(m1, n2)) (Bdl : 'M_(m2, n1)) (Bdr : 'M_(m2, n2)),
    block_mx Aul Aur Adl Adr = block_mx Bul Bur Bdl Bdr ->
    [/\ Aul = Bul, Aur = Bur, Adl = Bdl & Adr = Bdr].

(* （全部同じ）定数行列の場合、サイズは合成される。 *)
Check block_mx_const : forall (R : Type) (m1 m2 n1 n2 : nat) (a : R),
    block_mx (@const_mx R m1 n1 a) (@const_mx R m1 n2 a) (@const_mx R m2 n1 a) (@const_mx R m2 n2 a)
    = @const_mx R (m1 + m2) (n1 + n2) a.

(**
# submatrix 部分行列 （小行列をとりだす）

mxalgebra.v で扱う部分空間ではないことに注意
*)
(**
## 関数

型だけで連想できる。
*)
Check @lsubmx : forall (R : Type) (m n1 n2 : nat), 'M_(m, n1 + n2) -> 'M_(m, n1).
Check @rsubmx : forall (R : Type) (m n1 n2 : nat), 'M_(m, n1 + n2) -> 'M_(m, n2).
Check @usubmx : forall (R : Type) (m1 m2 n : nat), 'M_(m1 + m2, n) -> 'M_(m1, n).
Check @dsubmx : forall (R : Type) (m1 m2 n : nat), 'M_(m1 + m2, n) -> 'M_(m2, n).
Check @ulsubmx : forall (R : Type) (m1 m2 n1 n2 : nat), 'M_(m1 + m2, n1 + n2) -> 'M_(m1, n1).
Check @ursubmx : forall (R : Type) (m1 m2 n1 n2 : nat), 'M_(m1 + m2, n1 + n2) -> 'M_(m1, n2).
Check @dlsubmx : forall (R : Type) (m1 m2 n1 n2 : nat), 'M_(m1 + m2, n1 + n2) -> 'M_(m2, n1).
Check @drsubmx : forall (R : Type) (m1 m2 n1 n2 : nat), 'M_(m1 + m2, n1 + n2) -> 'M_(m2, n2).

Check @submxblock.
Check @submxrow.
Check @submxcol.

(* 関数 f : ``'I_m' -> 'I_m`` と、g : ``'I_n' -> 'I_n`` で部分行列を選ぶ。 *)
Check @mxsub
  : forall (R : Type) (m n m' n' : nat), ('I_m' -> 'I_m) -> ('I_n' -> 'I_n) -> 'M_(m, n) -> 'M_(m', n').
(* とくに難しことはしていない。f, g は単射でなくてもよい。 *)
Print mxsub.                        (* \matrix_(i, j) A (f i) (g j) *)
Check rowsub _.                     (* f のみの Notation *)
Check colsub _.                     (* g のみの Notation *)

(**
## 補題
*)
(* 取り出した小行列をつなぎ合わせる *)
Check submxK : forall (R : Type) (m1 m2 n1 n2 : nat) (A : 'M_(m1 + m2, n1 + n2)),
    block_mx (ulsubmx A) (ursubmx A) (dlsubmx A) (drsubmx A) = A.

(* row_mx で連結したものを、lsubmx で取り出す。lsubmx にn1,n2の指定は不要であることがわかる。 *)
Check row_mxKl : forall (R : Type) (m n1 n2 : nat) (A1 : 'M_(m, n1)) (A2 : 'M_(m, n2)),
    lsubmx (row_mx A1 A2) = A1.

(**
# square matrix 正方行列、diagonal matrix 対角行列
 *)
Section Diagonal.

Variable R : semiRingType.
Variables m n : nat.

(**
## 関数
*)

(* 行ベクトルを対角行列にする。 *)
Check @diag_mx R n : 'rV_n -> 'M_n.

(* 指定要素だけ1の行列。対角ではない。 *)
Check @delta_mx R m n : 'I_m -> 'I_n -> 'M_(m, n).
Print delta_mx.

(* 部分単位行列。r未満の対角要素だけが 1 の行列、正方行列でなくてもよい。 *)
Check @pid_mx R m n : nat -> 'M_(m, n).
Print pid_mx.
(* 正方行列の右(mathcompでは*mの左)に掛けると列のサイズを調整できる。 *)
(* 正方行列の左(mathcompでは*mの右)に掛けると行のサイズを調整できる。 *)
(* サイズの調整とは、列または行をrの個数だけ残して、あとは0を詰める。 *)

(* 1%:M - pid_mx r *)
Check @copid_mx : forall (R : ringType) (n : nat), nat -> 'M_n.
Print copid_mx.

(* 単位行列の行を s で置き換えた行列 *)
Check @perm_mx R n : 'S_n -> 'M_n.
Print perm_mx.

(* 単位行列の i1行目 と i2行目を入れ替えた行列 *)
Check @tperm_mx R n : 'I_n -> 'I_n -> 'M_n.
Print tperm_mx.

(* (0,0)に 1 置いて、正方行列の行と列をひとつづ増やす。 *)
Check @lift0_mx R n : 'M_n -> 'M_(n.+1).
Print lift0_mx.
(* lift0_mx A = / 1 0 \ *)
(*              \ 0 A / *)

End Diagonal.

(* 行列式が環の単位元か否かを判定する。 *)
Check @unitmx : forall (R : comUnitRingType) (n : nat), pred 'M_n.
Print unitmx.                        (* (\det A)%R \is a GRing.unit *)

(**
## 補題
*)
(* 単位行列の行列式は、環の単位元である。 *)
Check unitmx1 : forall (R : comUnitRingType) (n : nat), (1%:M)%R \in unitmx.

(**
# おまけ - 0行、0列とはなにか。

0行とは、行の数が0個（インデックスが0未満）の有限個の行列である。
型として定義できるが、要素が取り出せない。0行n列の行列、m行0列の行列はいずれも要素が取り出せない
*)
Section Zero.

Variable R : semiRingType.
Variable m n : nat.

(**
m行0列の行列と0行n列の行列の積は、m行n列の零行列である。

証明：
任意の i k 要素 に対して、
``\sum_(j : 'I_0) A i j * B j k``
 であり、BigOpの0回は単位元であるから、これは 0である。
*)

Goal forall (A : 'M[R]_(m, 0)) (B : 'M[R]_(0, n)), A *m B = 0.
Proof.
  move=> A B.
  Check A *m B = 0 :> 'M[R]_(m, n).         (* 行列の= *)
  
  apply/matrixP => i k.
  Check fun_of_matrix (A *m B) i k = (GRing.zero : 'M_(m, n)) i k. (* 関数値の= *)
  Check fun_of_matrix (A *m B) i k = fun_of_matrix 0 i k. (* コアーションは fun_of_matrix *)
  Check (A *m B) i k = (const_mx 0) i k. (* const_mx がコアーションではない。これは間違い。 *)
  
  rewrite 2!mxE.
  Check \sum_(j < 0) fun_of_matrix A i j * fun_of_matrix B j k = 0.
  Check \sum_(j : 'I_0) A i j * B j k = 0.  (* 行列の要素どうしの= *)
  
  rewrite big_ord0.
  done.
Qed.

End Zero.

(* END *)
