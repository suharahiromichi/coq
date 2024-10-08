From mathcomp Require Import all_ssreflect.
From mathcomp Require Import all_algebra.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Num.Def.
Import Num.Theory.
Import GRing.Theory.

Local Open Scope ring_scope.

(**
- https://en.wikipedia.org/wiki/LU_decomposition の Through recursion
- Packaging Mathematical Structures LUP decomposition
*)

Fixpoint cormen_lup {F : fieldType} {n : nat} : 'M[F]_n -> 'M[F]_n * 'M[F]_n * 'M[F]_n :=
  match n with
  | n0.+1 => fun A : 'M[F]_(1 + n0) =>
               if [pick k | A k 0 != 0] is Some k then (* A k 0 が非零であるなら、  *)
                 let A1 := xrow k 0 A in (* i行n目と0行目を入れ替える。 *)
                 let a := A1 0 0 in      (* 上左 *)
                 let w := ursubmx A1 in  (* 上右 *)
                 let v := dlsubmx A1 in  (* 下左 *)
                 let A' := drsubmx A1 in (* 下右 *)
                 
                 (* 行の入れ替え *)
                 (* P1 は 左から掛けて上記の入れ替えをする単位行列。Qともいう。 *)
                 let P1 := tperm_mx k 0 in
                 
                 (*          / a | w  \ *)
                 (* P1 * A = |        | *)
                 (*          \ v | A' / *)
                 
                 (*          / 1        | 0 \   / a | w              \ *)
                 (*        = |              | * |                    | *)
                 (*          \ (1/a)*v  | 1 /   \ 0 | A' - (1/a)*v*w / *)
                 
                 let: (P', L', U') := @cormen_lup F n0 (A' - a^-1 *: v *m w) in
                 let P := (block_mx 1 (0 : 'rV_n0) (0 : 'cV_n0) P') *m P1 in
                 let L := block_mx 1    0 v L' in
                 let U := block_mx a%:M w 0 U' in
                 
                 (* / 1 | 0  \            / 1           | 0  \   / a | w  \ *)
                 (* |        | * P1 * A = |                  | * |        | *)
                 (* \ 0 | P' /            \ (1/a)*P'*v  | L' /   \ 0 | U' / *)
                 
                 (*        / 1 | 0  \   / a | w  \   / a    | w    \ *)
                 (* 左辺 = |        | * |        | = |             | *)
                 (*        \ 0 | P' /   \ v | A' /   \ P'*v | P'*A'/ *)

                 (*        / a    | w    \ *)
                 (* 右辺 = |             | *)
                 (*        \ P'*v | L'*U'/ *)
                 
                 (* ただし、 P'*A' = L'*U' *)
                 
                 (P, L, U)
               else
                 (1%:M, 1%:M, A)
  | _    => fun _ => (1%:M, 1%:M, 1%:M)
  end.

Lemma cormen_lup_correct : forall F n (A : 'M_n),
    let: (P, L, U) := @cormen_lup F n A in P *m A = L *m U.
Proof.
  move=> F.
  elim.
  - move=> A /=.
    admit.
    
  - move=> n IH A.
    case : [pick k | A k 0 != 0 ] => //=.
    move=> a.
    

Admitted.



Lemma cormen_lup_correct {F : fieldType} n (A : 'M[F]_n.+1) :
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


(* END *)





