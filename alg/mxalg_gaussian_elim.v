From mathcomp Require Import all_ssreflect.
From mathcomp Require Import all_algebra.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Num.Def.
Import Num.Theory.
Import GRing.Theory.

Local Open Scope ring_scope.

Section S.
  Variable F : fieldType.
  Variable m n : nat.
  Variable A : 'M[F]_(m, n).
  
  (**
成り立つひとつの ``('I_m * 'I_n)`` 型の要素をoption型で返す。
   *)
  Check [pick ij | A ij.1 ij.2 != 0].
  Locate "[ pick _ | _ ]".                (* := (pick (fun x => P)) *)
  About pick.                             (* fintype *)
  Print pick. (* = fun (T : finType) (P : pred T) => ohead (enum P) *)
  Check ohead : seq F -> option F.

  (**
``if _ is Some (i, j) then _ else _`` で受けるので、then節で
``i : 'I_m`` と ``j : 'I_n`` が使えるようになる。
   *)
  Section S1.
    Variable A' : 'M[F]_(m.+1, n.+1).
    Variable i : 'I_m.+1.
    Check ord0 : 'I_m.+1.
    Variable j : 'I_n.+1.
    Check ord0 : 'I_n.+1.
    
    (* 0列めとj列めを入れ替える。 ついで、0行めとi行めを入れ替える。 *)
    Check xrow i (ord0 : 'I_m.+1) (xcol j (ord0 : 'I_n.+1) A').
  End S1.
  
  (* 上側の部分行列を取り出す。1行しかない場合、m2 = 0 となる。これは判る。 *)
  Print usubmx.
  Check @usubmx : forall (R : Type) (m1 m2 n : nat), 'M_(m1 + m2, n) -> 'M_(m1, n).
  Check fun (R : Type) (m1 m2 n : nat) (A : 'M_(m1 + m2, n)) =>
          \matrix[usubmx_key]_(i, j) A (lshift m2 i) j.
  Print lshift.
  Check lshift : forall m n : nat, 'I_m -> 'I_(m + n).
  (* 下側の部分行列を取り出す。1行しかない場合、m2 = 0 となるとどうするか。 *)
  Print dsubmx.
  Check @dsubmx : forall (R : Type) (m1 m2 n : nat), 'M_(m1 + m2, n) -> 'M_(m2, n).
  Check fun (R : Type) (m1 m2 n : nat) (A : 'M_(m1 + m2, n)) =>
          \matrix[dsubmx_key]_(i, j) A (rshift m1 i) j.
  Check @dsubmx F 1 0 2 : 'M_(1 + 0, 2) -> 'M_(0, 2).
  
  Check @matrix F 0 2.
  Check {ffun 'I_0 * 'I_2 -> F}.
  Check 'I_0.                               (* 要素がnilの有限型 *)

  Print ursubmx.                            (* 上右 *)
  Check fun (R : Type) (m1 m2 n1 n2 : nat) (A : 'M_(m1 + m2, n1 + n2)) => rsubmx (usubmx A) : 'M_(m1, n2).

  Print dlsubmx.                            (* 下左 *)
  Check fun (R : Type) (m1 m2 n1 n2 : nat) (A : 'M_(m1 + m2, n1 + n2)) => lsubmx (dsubmx A) : 'M_(m2, n1).

  Print drsubmx.                            (* 下右 *)
  Check fun (R : Type) (m1 m2 n1 n2 : nat) (A : 'M_(m1 + m2, n1 + n2)) => rsubmx (dsubmx A) : 'M_(m2, n2).

  Print block_mx.
  Check fun (R : Type) (m1 m2 n1 n2 : nat)
            (Aul : 'M_(m1, n1))
            (Aur : 'M_(m1, n2))
            (Adl : 'M_(m2, n1))
            (Adr : 'M_(m2, n2))
        => (col_mx (row_mx Aul Aur) (row_mx Adl Adr) : 'M_(m1 + m2, n1 + n2)).
  
  Fixpoint Gaussian_elimination_ {F : fieldType} {m n} : 'M[F]_(m, n) -> 'M_m * 'M_n * nat :=
    match m, n with
    | _.+1, _.+1 =>
        fun A : 'M_(1 + _, 1 + _) =>                          (* 寸法 m, n の行列を引数にとり、 *)
          if [pick ij | A ij.1 ij.2 != 0] is Some (i, j) then (* 要素 i, j が非零であるなら、  *)
            let A1 := xrow i 0 (xcol j 0 A) in                (* i行目と0行目、j列目と0列目を入れ替える。 *)
            let a := A i j in                     (* 上左 (A1 0 0) *)
            let u := ursubmx A1 in                (* 上右 *)
            let v := a^-1 *: dlsubmx A1 in        (* 下左 *)
            let A' := (drsubmx A1 - v *m u) in    (* 下右 *)
            (* /a u\ *)
            (* \v A'/ *)
            let: (L, U, r) := Gaussian_elimination_ A' in (* 下左の寸法 m-1 n-1 行列に対して再帰的に *)
            let ll := (block_mx 1    0 v L) in
            (* /1 0\ *)
            (* \v L/ *)
            let uu := (block_mx a%:M u 0 U) in
            (* /a u\ *)
            (* \0 U/ *)
            (xrow i 0 ll,             (* i行目と0行目を入れ替える。 *)
              xcol j 0 uu,            (* j列目と0列目を入れ替える。 *)
              r.+1)                   (* ランクを+1 する。 *)
          else
            (1%:M,
              1%:M,
              0)
    | _, _ => fun _ => (1%:M, 1%:M, 0)
    end.
  Check @Gaussian_elimination_ : forall (F : fieldType) (m n : nat), 'M_(m, n) -> 'M_m * 'M_n * nat.

End S.

(**
- https://en.wikipedia.org/wiki/LU_decomposition の Through recursion
- Packaging Mathematical Structures LUP decomposition
*)

Fixpoint cormen_lup {F : fieldType} {n : nat} : 'M[F]_n -> 'M[F]_n * 'M[F]_n * 'M[F]_n :=
  match n with
  | n0.+1 => fun A : 'M[F]_(1 + n0) =>
               if [pick k | A k 0 != 0] is Some k then (* A k 0 が非零であるなら、  *)
                 let A1 := xrow k 0 A in (* i行n目と0行目を入れ替える。 *)
                 let a := A1 0 0 in        (* 上左 *)
                 let w := ursubmx A1 in    (* 上右 *)
                 let v := dlsubmx A1 in    (* 下左 *)
                 let A' := drsubmx A1 in   (* 下右 *)
                 let P1 := @tperm_mx F n0.+1 k 0 in (* 左から掛けて上記の入れ替えをする単位行列 *)
                 
                 (*          /a | w \ *)
                 (* P1 * A = |      | *)
                 (*          \v | A'/ *)

                 let cv := a^-1 *: v in
                 
                 (*          /1  | 0\   /a | w           \ *)
                 (* P1 * A = |      | * |                | *)
                 (*          \cv | 1/   \0 | A' - cv *m w/ *)
                 
                 let: (L', U', P') := cormen_lup (A' - cv *m w) in

                 (* P' * (A' - cv *m w) = L' *m U' *)
                 
                 let cv' := a^-1 *: P' *m v in
                 let L := block_mx 1    0 v L' in
                 let U := block_mx a%:M w 0 U' in
                 let P := block_mx 1 (0 : 'rV_n0) (0 : 'cV_n0) P' *m P1 in
                 
                 (* /1 | 0 \            /1   | 0 \   /a | w \ *)
                 (* |      | * P1 * A = |        | * |      | *)
                 (* \0 | P'/            \cv' | L'/   \0 | U'/ *)
                 
                 (*    P          * A =      L     *    U *)
                 (L, U, P)
               else
                 (1%:M, 1%:M, 1%:M)
  | _    => fun _ => (1%:M, 1%:M, 1%:M)
  end.

Lemma cormen_lup_correct : forall F n A,
    let: (P, L, U) := @cormen_lup F n A in P *m A = L *m U.
Proof.
Admitted.


(**
Wolfram の場合：

行列のサイズを求める
Dimensions[A]           {3, 4}
Dimensions[{{}}]        {1, 0}  ({0,0}でないので注意)
{i,j} = Dimensions[A]



m行 n列行列          1    2    3    4
                     5    6    7    8
                     9    10   11   12


上左    A[[1;;1, 1;;1]]         1

上右    A[[1;;1, 2;;n]]                 2   3   4

下左    A[[2;;m, 1;;1]]         5
                                9

下右    A[[2;;m, 2;;n]]                 6    7    8
                                        10   11   12


行列の連結
Join[A[[1;;1, 1;;1]], A[[2;;m, 1;;1]]]  左
Join[A[[1;;1, 2;;n]], A[[2;;m, 2;;n]]]  右
Join[Join[A[[1;;1, 1;;1]], A[[2;;m, 1;;1]]],
     Join[A[[1;;1, 2;;n]], A[[2;;m, 2;;n]]], 2]

ConstantArray[1, {1, n - 1}]            1   1   1

ConstantArray[0, {1, n - 1}]            0   0   0 

ConstantArray[0, {m - 1, 1}]            0
                                        0


1行と2行の入れ替え
B=A
B[[1]]=A[[2]]
B[[2]]=A[[1]]


1列と2列の入れ替え
B=A
B[[All, 1]]=A[[All, 2]]
B[[All, 2]]=A[[All, 1]]


最初の非零要素の行
ArrayRules[A][[1]][[1]][[1]]

最初の非零要素の列
ArrayRules[A][[1]][[1]][[2]]


*)

(* END *)
