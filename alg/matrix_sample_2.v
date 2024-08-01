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

Section MatrixRing.

(**
ringType を要素とする行列は ``lmodType R`` である。
*)
  Variable R : ringType.
  
  Check 'M[R]_(m, n) : eqType.
  Check 'M[R]_(m, n) : choiceType.
  Fail Check 'M[R]_(m, n) : countType.
  Check 'M[R]_(m, n) : nmodType.
  Check 'M[R]_(m, n) : zmodType.
  Check 'M[R]_(m, n) : lmodType R.
  Fail Check 'M[R]_(m, n) : semiRingType.

(**
Zmodule が Lmodule である公理
*)
  HB.about GRing.Zmodule_isLmodule.Build.

  (* 一般的な左scale演算子 ``*:`` *)
  Locate "_ *: _". (* := (GRing.scale a m) : ring_scope (default interpretation) *)
  Check GRing.scale : R -> (_ : lmodType R) -> (_ : lmodType R).
  Check GRing.scale : R -> 'M_(m, n) -> 'M_(m, n).
  
  Check scalerA : forall (R : ringType) (V : lmodType R) (x y : R) (v : V),
      x *: (y *: v) = (x * y) *: v.
  Check scale1r : forall (R : ringType) (V : lmodType R) (v : V), 1 *: v = v.
  Check scalerDr : forall (R : ringType) (V : lmodType R) (x : R) (v u : V),
      x *: (v + u) = x *: v + x *: u.
  Check scalerDl : forall (R : ringType) (V : lmodType R) (v : V) (x y : R),
      (x + y) *: v = x *: v + y *: v.
  
  (* 行列の左scale演算子 ``*m:`` *)
  
  Local Notation "x *m: A" := (scalemx x A) (at level 40) : ring_scope.  
  Locate "_ *m: _". (* := (scalemx x A) (at level 40) : ring_scope.   *)
  Check scalemx : forall (R : semiRingType) (m n : nat), R -> 'M_(m, n) -> 'M_(m, n).
  
  Check scalemxA : forall (R : semiRingType) (m n : nat) (x y : R) (A : 'M_(m, n)),
      x *m: (y *m: A) = (x * y) *m: A.
  Check scale1mx : forall (R : semiRingType) (m n : nat) (A : 'M_(m, n)),
      1 *m: A = A.
  Check scalemxDr : forall (R : semiRingType) (m n : nat) (x : R) (A B : 'M_(m, n)),
      x *m: (A + B) = x *m: A + x *m: B.
  Check scalemxDl : forall (R : semiRingType) (m n : nat) (A : 'M_(m, n)) (x y : R),
      (x + y) *m: A = x *m: A + y *m: A.

(**
``+`` と addrC は、nmodType で成り立つので、ringType の行列でも成り立つ。
*)
  Check @GRing.add : forall s : nmodType, s -> s -> s. (* + *)
  Check addrC : forall x : nmodType, commutative GRing.add.
  
  Lemma test1 (A B : 'M[R]_(m, n)) : A + B = B + A.
  Proof.
    rewrite addrC.
    done.
  Qed.

(**
``%M`` スカラ行列を作る。
*)
  Locate "_ %:M". (* := (scalar_mx a) : ring_scope (default interpretation) *)
  Check scalar_mx : R -> 'M_m.              (* 正方行列 *)
  Check scalar_mx : R -> 'M_(m, m).         (* 正方行列 *)
  
(**
``*`` は半環でないといけないので行列には使えない。``*m`` を使う。
*)
  Check @GRing.scale : forall (R : ringType) (s : lmodType R), R -> s -> s.        (* *: *)
  Check @GRing.mul : forall s : semiRingType,                  s -> s -> s.        (* * *)
  Check @scalemx : forall (R : ringType) (m n : nat), R -> 'M_(m, n) -> 'M_(m, n). (* *m: *)
  Check mulmx :                               'M_(m, n) -> 'M_(n, p) -> 'M_(m, p). (* *m *)

  
  (* 行列に左からスカラを掛けるのば、スカラ行列に行列を掛けることに等しい。 *)
  Lemma test2 (a : R) (A : 'M[R]_(m, n)) : a *: A = a%:M *m A.
  Proof.
    rewrite mul_scalar_mx.
    done.
  Qed.
  
(**
正方行列、ベクトル
*)
  Goal 'M[R]_(m, m) = 'M[R]_m. Proof. done. Qed. (* 正方行列 *)
  Goal 'M[R]_(1, m) = 'rV[R]_m. Proof. done. Qed. (* row 行ベクトル *)
  Goal 'M[R]_(n, 1) = 'cV[R]_n. Proof. done. Qed. (* column 列ベクトル *)

  Section TEST.
    Variable A : 'M[R]_(m, n).
    Variable B : 'M[R]_(n, p).
    Check mulmx : 'M[R]_(m, n) -> 'M[R]_(n, p) -> 'M_(m, p).
    Check A *m B : 'M_(m, p).

    (* 行ベクトルを左から掛ける。 *)
    Variable P : 'rV[R]_m.                  (* 'M[R]_(1, m). *)
    Check mulmx : 'rV[R]_m -> 'M[R]_(m, n) -> 'rV[R]_n.
    Check P *m A : 'rV[R]_n.
    
    (* 列ベクトルを右から掛ける。 *)
    Variable Q : 'cV[R]_n.                  (* 'M[R]_(n, 1). *)
    Check mulmx : 'M[R]_(m, n) -> 'cV[R]_n -> 'cV[R]_m.
    Check A *m Q : 'cV_m.

    (* 行ベクトルを使うほうが多いので、固有ベクトルは教科書とは違う表現になっている。 *)
    Check @eigenvalueP
      : forall (F : fieldType) (n : nat) (g : 'M[F]_n) (a : F),
        reflect (exists2 v : 'rV[F]_n, (v *m g = a *: v) & (v != 0)) (eigenvalue g a).
    (*                                                   ↑ exists2 に対応するAND *)
  End TEST.

(**
行列の作り方
*)  
  Search matrix_of_fun.
  
  Check mxE : forall (R : Type) (m n : nat) (k : unit) (F : 'I_m -> 'I_n -> R),
      \matrix[k]_(i, j) F i j =2 F.
  Check @eq_mx : forall (R : Type) (m n : nat) (k : unit) (F1 F2 : 'I_m -> 'I_n -> R),
      F1 =2 F2 -> \matrix[k]_(i, j) F1 i j = \matrix[k]_(i, j) F2 i j.
  
  Check 1 : R.
  Definition all1 : 'M[R]_(m, n) := \matrix_(i < m, j < n) 1.
  Definition all1' : 'M[R]_(m, n) := const_mx 1.
  
  Goal forall i j, (all1 i j) == 1.
  Proof.
    move=> i j.
    rewrite mxE.
    done.
  Qed.

  Goal forall i j, (all1 i j) == (all1' i j).
  Proof.
    move=> i j.
    rewrite !mxE.
    done.
  Qed.

  Goal forall i j, (all1^T j i) == (all1'^T j i).
  Proof.
    move=> i j.
    rewrite !mxE.
    done.
  Qed.
  

(**
対角行列
*)
  Check mul_diag_mx : forall (R : semiRingType) (m n : nat) (d : 'rV_m) (A : 'M_(m, n)),
      (diag_mx d) *m A = \matrix_(i, j) (d 0 i * A i j).
  Check mul_mx_diag : forall (R : semiRingType) (m n : nat) (A : 'M_(m, n)) (d : 'rV_n),
      A *m (diag_mx d) = \matrix_(i, j) (A i j * d 0 j).
  Check mulmx_diag : forall (R : semiRingType) (n : nat) (d e : 'rV_n),
      (diag_mx d) *m (diag_mx e) = diag_mx (\row_j (d 0 j * e 0 j)).
    
End MatrixRing.


(* END *)
