(**
- Twelfth Lesson Formalising a LUP Decomposition

- Machine-checked computer-aided mathematics

- https://en.wikipedia.org/wiki/LU_decomposition
  Through recursion

- Packaging Mathematical Structures LUP decomposition
 *)

From mathcomp Require Import all_ssreflect.
From mathcomp Require Import all_fingroup.
From mathcomp Require Import all_algebra.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Num.Def.
Import Num.Theory.
Import GRing.Theory.

Local Open Scope ring_scope.

Section CormenLUP.

Variable F : fieldType.

(* Decomposition of the matrix A to P A = L U with *)
(*   - P a permutation matrix                      *)
(*   - L a unipotent lower triangular matrix       *)
(*   - U an upper triangular matrix                *)

Fixpoint cormen_lup {n} :=
  match n return let M := 'M[F]_n.+1 in M -> M * M * M with
  | 0 => fun A => (1, 1, A)
  | _.+1 => fun A =>
    let k := odflt 0 [pick k | A k 0 != 0] in
    let A1 : 'M_(1 + _) := xrow 0 k A in
    let P1 : 'M_(1 + _) := tperm_mx 0 k in
    let Schur := ((A k 0)^-1 *: dlsubmx A1) *m ursubmx A1 in
    let: (P2, L2, U2) := cormen_lup (drsubmx A1 - Schur) in
    let P := block_mx 1 0 0 P2 *m P1 in
    let L := block_mx 1 0 ((A k 0)^-1 *: (P2 *m dlsubmx A1)) L2 in
    let U := block_mx (ulsubmx A1) (ursubmx A1) 0 U2 in
    (P, L, U)
  end.

Fixpoint cormen_lup' {n} :=
  match n return let M := 'M[F]_n.+1 in M -> M * M * M with
  | 0 => fun A => (1, 1, A)
  | _.+1 => fun A =>
    let k := odflt 0 [pick k | A k 0 != 0] in (* A k 0 が非零であるなら、  *)
    let P1 : 'M_(1 + _) := tperm_mx 0 k in (* P1 は 左から掛けて上記の入れ替えをする単位行列。 *)
    let A1 : 'M_(1 + _) := xrow 0 k A in (* k行目と0行目を入れ替えた行列。 *)

    (*               / a | w  \ *)
    (* P1 * A = A1 = |        | *)
    (*               \ v | A' / *)

    (* let a  := A1 0 0 in                  (* A1の上左 スカラ *) *)
    let a  := A k 0 in                      (* オリジナルと同じになる。 *)
    let a' := ulsubmx A1 in                 (* A1の上左 1x1行列。a と同じもの。 *)
    let w  := ursubmx A1 in                 (* A1の上右 *)
    let v  := dlsubmx A1 in                 (* A1の下左 *)
    let A' := drsubmx A1 in                 (* A1の下右 *)
    
    (*           L (下三角行列)      U (上三角行列)       *)
    (*          / 1        | 0 \   / a | w              \ *)
    (* P1 * A = |              | * |                    | *)
    (*          \ (1/a)*v  | 1 /   \ 0 | A' - (1/a)*v*w / *)
    (*                                   ~~~~~~~~~~~~~~ Schur これを再帰的にLUP分割する。 *)
    
    let Schur := A' - (a^-1 *: v) *m w in   (* A' - (1/a)*v*w *)
    let: (P2, L2, U2) := cormen_lup' Schur in
    let P := (block_mx 1  0 0                   P2) *m P1 in
    let L := (block_mx 1  0 (a^-1 *: (P2 *m v)) L2) in
    let U := (block_mx a' w 0                   U2) in
    
    (* P               * A = L                    * U          *)

    (* / 1 | 0  \            / 1           | 0  \   / a | w  \ *)
    (* |        | * P1 * A = |                  | * |        | *)
    (* \ 0 | P2 /            \ (1/a)*P2*v  | L2 /   \ 0 | U2 / *)
    
    (*        / 1 | 0  \   / a | w  \   / a    | w     \ *)
    (* 左辺 = |        | * |        | = |              | *)
    (*        \ 0 | P2 /   \ v | A2 /   \ P2*v | P2*A2 / *)
    
    (*        / a    | w                   \   / a    | w     \ *)
    (* 右辺 = |                            | = |              | *)
    (*        \ P2*v | (1/a)*P2*v*w + L2*U2/   \ P2*v | P2*A2 / *)
    
    (* ただし、再帰的なLUP分割から、P2 * (A2 - (1/a)*v*w) = L2*U2 *)
    (* 変形して、P2*A2 = P2*(1/a)*v*w + L2*U2 *)
    
    (P, L, U)
  end.

Goal forall n (A : 'M_n.+1), cormen_lup A = cormen_lup' A.
Proof.
  done.
Qed.

(**
LUPの P が置換行列である。
 *)

(* 単位行列を置換 s で置き換えて得られた行列。 *)
Check @perm_mx : forall (R : semiRingType) (n : nat), {perm 'I_n} -> 'M_n.

(* ふたつの置換行列の積についての補題。 *)
Check is_perm_mxMr : forall (R : semiRingType) (n : nat) (A B : 'M_n),
    is_perm_mx B -> is_perm_mx (A *m B) = is_perm_mx A.

(* 置換行列と置換の積について、上の補題を具体的にする。 *)
(* 実際は、置換行列が積になっていればいいので、具体的な行列で証明する必要はない。 *)
Section mx_perm.
  Variable n : nat.
  Variable P : 'M[F]_n.+1.
  Variable A : 'M[F]_n.+2.

  (* LUP分解の置換行列 P の左上に 1 を置いた行列。 *)
  Local Definition MA := @block_mx F 1 n.+1 1 n.+1 1 0 0 P.

  Check [pick k | A k 0 != 0] : option 'I_n.+2. (* A_k_0 が非零の k を取り出す。 *)
  Check odflt 0 [pick k | A k 0 != 0] : 'I_n.+2. (* Option T を T にする。 *)

  (* (0 : 'I_n.+2) を (2 : 'I_n.+2) に置換する関数 *)
  Check @tperm 'I_n.+2 0 2 : perm_type 'I_n.+2.
  (* 上記の関数に 1 を与える。 *)
  Check @tperm 'I_n.+2 0 2 1 : 'I_n.+2.
  
  (* A_k_0 が非零の k に対して、0番目とk番目を置換する。 *)
  Local Definition PB := tperm 0 (odflt 0 [pick k | A k 0 != 0]).
  Check perm_mx PB.                       (* 置換PBを行列MAにする。 *)
  
  Lemma is_perm_MA_PB : is_perm_mx (MA *m perm_mx PB) = is_perm_mx MA.
  Proof.
    rewrite (@is_perm_mxMr F n.+2
               MA                           (* 第1引数 *)
               (perm_mx PB)
               (perm_mx_is_perm F PB)).     (* 第2引数 *)
    (* is_perm_mxMr の第2引数は、-> の左であることに注意 *)
    done.
  Qed.
End mx_perm.

(* Pは置換行列である。 *)
Print is_perm_mx.
Lemma cormen_lup_perm n (A : 'M_n.+1) : is_perm_mx (cormen_lup A).1.1. (* P *)
Proof.
  elim: n => [|n IHn] /= in A *.
  - exact: is_perm_mx1.

  (* 外側のlet を ``let '(P2, L2, U2) := cormen_lup A' in`` にする。 *)
  - set A' := _ - _.
    move/(_ A') : IHn.                  (* move: (IHn A'). と同じ。 *)
    (* IHn をジェレラライズして、それを A' に適用する。 *)
    case: (cormen_lup A') => [[P L U]] {A'} /=. (* cormen_lup A' を P L U に分割する。 *)
    
    (* 置換を簡単にする。 *)
    rewrite (is_perm_mxMr _ (perm_mx_is_perm _ _)).
    Undo 1.
    rewrite /tperm_mx is_perm_MA_PB.
    
    (* is_perm_mx を exist に変えて、s を代入する。 *)
    Check @is_perm_mxP F n.+1 P
      : reflect (exists s : {perm 'I_n.+1}, P = perm_mx s) (is_perm_mx P).
    rewrite /MA.
    case/is_perm_mxP => s ->.
    
    (* lift0_mx は block_mx 1 0 0 とおなじ。 *)
    Check lift0_mx_is_perm F s : is_perm_mx (lift0_mx (perm_mx s)).
    Check lift0_mx_is_perm F s : is_perm_mx (block_mx 1 0 0 (perm_mx s)).
    rewrite lift0_mx_is_perm.
    done.
Qed.

(* P * A = L * U が成り立つ。 *)
Lemma cormen_lup_correct n (A : 'M_n.+1) :
  let: (P, L, U) := cormen_lup A in P * A = L * U.
Proof.
  elim: n => [|n IHn] /= in A *.
  - by rewrite !mul1r.
  - set k := odflt 0 [pick k | A k 0 != 0 ] : 'I_n.+2. (* odflt _ _ *)
    set A1 : 'M_(1 + n.+1) := xrow 0 k A.   (* xrow _ _ _ *)
    set A' := drsubmx A1 - (A k 0)^-1 *: dlsubmx A1 *m ursubmx A1. (* _ - _ *)
    move/(_ A'): IHn.
    case: cormen_lup => [[P' L' U']] IHn.
    rewrite -mulrA -!mulmxE -xrowE -/A1 /= -[n.+2]/(1 + n.+1)%N -{1}(submxK A1).
    rewrite !mulmx_block !mul0mx !mulmx0 !add0r !addr0 !mul1mx -{L' U'}[L' *m _]IHn.
    rewrite -scalemxAl !scalemxAr -!mulmxA addrC -mulrDr {A'}subrK.
    congr (block_mx _ _ (_ *m _) _).
    rewrite [_ *: _]mx11_scalar !mxE lshift0 tpermL {}/A1 {}/k.

    case: pickP => /= [k nzAk0 | no_k].
    (* 前提 forall x : 'I_n.+2, A x 0 != 0 *)
    + by rewrite mulVf ?mulmx1.
      
    (* 前提 (fun k : 'I_n.+2 => A k 0 != 0) =1 xpred0 *)
    + rewrite (_ : dlsubmx _ = 0) ?mul0mx //; apply/colP=> i.
      rewrite !mxE lshift0 (elimNf eqP (no_k (tperm 0 0 (rshift 1 i)))).
                                    (* (no_k _)                          でもよい。 *)
      done.
Qed.

(* L の行列式は 1 *)
Lemma cormen_lup_detL n (A : 'M_n.+1) : \det (cormen_lup A).1.2 = 1. (* L *)
Proof.
  (* elim: n => [|n IHn] /= in A *. *)
  elim: n A => [|n IHn] /= A.
  - by rewrite det1.
  - set A' := _ - _.
    move/(_ A'): IHn.
    case: cormen_lup => [[P L U]] {A'}/= detL.
    by rewrite (@det_lblock _ 1) det1 mul1r.
Qed.

(* L の対角成分は 1 *)
Lemma cormen_lup_lower n A (i j : 'I_n.+1) :
  (i <= j)%N -> (cormen_lup A).1.2 i j = (i == j)%:R. (* L *)
Proof.
  (* elim: n => [|n IHn] /= in A i j *. *)
  elim: n A i j => [|n IHn] /= A i j.
  - by rewrite [i]ord1 [j]ord1 mxE.
  - set A' := _ - _.
    move/(_ A'): IHn.
    case: cormen_lup => [[P L U]] {A'}/= Ll.
    rewrite !mxE split1.
    case: unliftP => [i'|] -> /=.
    + rewrite !mxE split1.
      case: unliftP => [j'|] -> //.
      by apply: Ll.
    + rewrite !mxE split1.
      case: unliftP => [j'|] -> /=.
      * rewrite mxE.
        done.
      * rewrite mxE.
        done.
Qed.

(* U は上三角行列 *)
Lemma cormen_lup_upper n A (i j : 'I_n.+1) :
  (j < i)%N -> (cormen_lup A).2 i j = 0 :> F. (* U *)
Proof.
  (* elim: n => [|n IHn] /= in A i j *. *)
  elim: n A i j => [|n IHn] /= A i j.
  - by rewrite [i]ord1.
  - set A' := _ - _.
    move/(_ A'): IHn; case: cormen_lup => [[P L U]] {A'}/= Uu.
    rewrite !mxE split1; case: unliftP => [i'|] -> //=; rewrite !mxE split1.
    case: unliftP => [j'|] ->.
    + by apply: Uu.
    + by rewrite /= mxE.
Qed.

End CormenLUP.

(* END *)
