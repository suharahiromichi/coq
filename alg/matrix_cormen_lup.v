(**
- Twelfth Lesson Formalising a LUP Decomposition

- Machine-checked computer-aided mathematics

- https://en.wikipedia.org/wiki/LU_decomposition
  Through recursion

- Packaging Mathematical Structures LUP decomposition
 *)

From mathcomp Require Import all_ssreflect.
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
    let A1 : 'M_(1 + _) := xrow 0 k A in (* i行n目と0行目を入れ替える。 *)
    let P1 : 'M_(1 + _) := tperm_mx 0 k in (* P1 は 左から掛けて上記の入れ替えをする単位行列。 *)

    (*               / a | w  \ *)
    (* P1 * A = A1 = |        | *)
    (*               \ v | A' / *)

    let a  := A k 0 in                      (* A1 0 0 = ulsubmx A1 *)
    let a' := ulsubmx A1 in                 (* 上左 a%:M と同じはず。。。 *)
    let w  := ursubmx A1 in                 (* 上右 *)
    let v  := dlsubmx A1 in                 (* 下左 *)
    let A' := drsubmx A1 in                 (* 下右 *)
    let Schur := A' - ((A k 0)^-1 *: v) *m w in (* A' - (1/a)*v*w *)
    
    (*          / 1        | 0 \   / a | w              \ *)
    (* P1 * A = |              | * |                    | *)
    (*          \ (1/a)*v  | 1 /   \ 0 | A' - (1/a)*v*w / *)

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
(*
  elim=> //= n IHn A.
  rewrite -IHn.
  case: cormen_lup => [[L U] P].
  apply/pair_equal_spec.
  split; [apply/pair_equal_spec |].
  split.
  - done.
  - done.
  - done.
*)
Qed.

Lemma cormen_lup_perm n (A : 'M_n.+1) : is_perm_mx (cormen_lup A).1.1.
Proof.
  elim: n => [|n IHn] /= in A *; first exact: is_perm_mx1.
  set A' := _ - _; move/(_ A'): IHn; case: cormen_lup => [[P L U]] {A'}/=.
  rewrite (is_perm_mxMr _ (perm_mx_is_perm _ _)).
  by case/is_perm_mxP => s ->; apply: lift0_mx_is_perm.
Qed.

Lemma cormen_lup_correct n (A : 'M_n.+1) :
  let: (P, L, U) := cormen_lup A in P * A = L * U.
Proof.
elim: n => [|n IHn] /= in A *; first by rewrite !mul1r.
set k := odflt _ _; set A1 : 'M_(1 + _) := xrow _ _ _.
set A' := _ - _; move/(_ A'): IHn; case: cormen_lup => [[P' L' U']] /= IHn.
rewrite -mulrA -!mulmxE -xrowE -/A1 /= -[n.+2]/(1 + n.+1)%N -{1}(submxK A1).
rewrite !mulmx_block !mul0mx !mulmx0 !add0r !addr0 !mul1mx -{L' U'}[L' *m _]IHn.
rewrite -scalemxAl !scalemxAr -!mulmxA addrC -mulrDr {A'}subrK.
congr (block_mx _ _ (_ *m _) _).
rewrite [_ *: _]mx11_scalar !mxE lshift0 tpermL {}/A1 {}/k.
case: pickP => /= [k nzAk0 | no_k]; first by rewrite mulVf ?mulmx1.
rewrite (_ : dlsubmx _ = 0) ?mul0mx //; apply/colP=> i.
by rewrite !mxE lshift0 (elimNf eqP (no_k _)).
Qed.

Lemma cormen_lup_detL n (A : 'M_n.+1) : \det (cormen_lup A).1.2 = 1.
Proof.
elim: n => [|n IHn] /= in A *; first by rewrite det1.
set A' := _ - _; move/(_ A'): IHn; case: cormen_lup => [[P L U]] {A'}/= detL.
by rewrite (@det_lblock _ 1) det1 mul1r.
Qed.

Lemma cormen_lup_lower n A (i j : 'I_n.+1) :
  i <= j -> (cormen_lup A).1.2 i j = (i == j)%:R.
Proof.
elim: n => [|n IHn] /= in A i j *; first by rewrite [i]ord1 [j]ord1 mxE.
set A' := _ - _; move/(_ A'): IHn; case: cormen_lup => [[P L U]] {A'}/= Ll.
rewrite !mxE split1; case: unliftP => [i'|] -> /=; rewrite !mxE split1.
  by case: unliftP => [j'|] -> //; apply: Ll.
by case: unliftP => [j'|] ->; rewrite /= mxE.
Qed.

Lemma cormen_lup_upper n A (i j : 'I_n.+1) :
  j < i -> (cormen_lup A).2 i j = 0 :> F.
Proof.
elim: n => [|n IHn] /= in A i j *; first by rewrite [i]ord1.
set A' := _ - _; move/(_ A'): IHn; case: cormen_lup => [[P L U]] {A'}/= Uu.
rewrite !mxE split1; case: unliftP => [i'|] -> //=; rewrite !mxE split1.
by case: unliftP => [j'|] ->; [apply: Uu | rewrite /= mxE].
Qed.

End CormenLUP.

(* END *)
