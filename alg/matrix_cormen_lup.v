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
(*   - L a unipotent lower triangular matrix 冪単三角行列 実際は 単三角行列 *)
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

(* match-return は match の返す型。この場合、関数の型で指定しても同じである。 *)
Fixpoint cormen_lup' {n : nat} : 'M[F]_n.+1 -> 'M[F]_n.+1 * 'M[F]_n.+1 * 'M[F]_n.+1 :=
  match n (* return let M := 'M[F]_n.+1 in M -> M * M * M *) with
  | 0 => fun A => (1, 1, A)
  | _.+1 => fun A =>
              (* odflt は option T 型を T 型にする。ディフォルトはここで用意する。  *)
              (* odflt 0 (Some k) == k, odflt 0 None == 0 *)
    let k := odflt 0 [pick k | A k 0 != 0] in (* A k 0 が非零である k を取り出す。 *)
    let P1 : 'M_(1 + _) := tperm_mx 0 k in (* P1 は 左から掛けて上記の入れ替えをする単位行列。 *)
    let A1 : 'M_(1 + _) := xrow 0 k A in (* k行目と0行目を入れ替えた行列。 *)

    (*               / a | w  \ *)
    (* P1 * A = A1 = |        | *)
    (*               \ v | A' / *)

    (* let a  := A1 0 0 in *)               (* A1の上左 スカラ。A1 は A のk行目と0行目を入れ替えた行列。 *)
    let a  := A k 0 in                      (* A k 0。上記と同じもの。 *)
    let a' := ulsubmx A1 in                 (* A1の上左 1x1行列。a と同じもの。 *)
    let w  := ursubmx A1 in                 (* A1の上右 *)
    let v  := dlsubmx A1 in                 (* A1の下左 *)
    let A' := drsubmx A1 in                 (* A1の下右 *)
    
    (*           L (下三角行列)      U (上三角行列)       *)
    (*                                                    *)
    (*          / 1        | 0 \   / a | w              \ *)
    (* P1 * A = |              | * |                    | *)
    (*          \ (1/a)*v  | 1 /   \ 0 | A' - (1/a)*v*w / *)
    (*                                   ~~~~~~~~~~~~~~ Schur これを再帰的にLUP分割する。シューア *)
    
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
補題：LUPの P が置換行列である。
 *)
(* 準備 *)
(* サイズnの単位行列を置換 s で置き換えて行列を得る関数 *)
Check @perm_mx : forall (R : semiRingType) (n : nat), {perm 'I_n} -> 'M_n.

(* 行列 A は、perm_mx で得られた行列であるという命題 *)
Print is_perm_mx.
Check fun (R : semiRingType) (n : nat) (A : 'M_n) => [exists s : {perm 'I_n}, A == perm_mx s].

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
  
  (* 行列 MA が置換行列なら、PB は置換である。 *)
  (* 行列 MA と、置換PB を行列にしたものの積が置換行列なら、行列MAは置換行列である。逆も成り立つ。 *)
  Lemma is_perm_MA_PB : is_perm_mx (MA *m perm_mx PB) = is_perm_mx MA.
  Proof.
    rewrite (@is_perm_mxMr F n.+2
               MA                           (* 第1引数 *)
               (perm_mx PB)
               (perm_mx_is_perm F PB)).     (* 第2引数 *)
    (* is_perm_mxMr の第2引数は、-> の左であることに注意 *)
    Undo 1.
    rewrite (is_perm_mxMr _ (perm_mx_is_perm _ _)).    
    done.
  Qed.
End mx_perm.

(* 補題：Pは置換行列である。 *)
Lemma cormen_lup_perm n (A : 'M_n.+1) : is_perm_mx (cormen_lup A).1.1. (* P *)
Proof.
  elim: n => [|n IHn] /= in A *.
  Check is_perm_mx 1.                       (* Goal *)
  - exact: is_perm_mx1.

  (* 外側のlet を ``let '(P2, L2, U2) := cormen_lup A' in`` にする。 *)
  - set A' := _ - _.
    Check A' : 'M_n.+1.
    move/(_ A') : IHn.                  (* move: (IHn A'). と同じ。 *)
    (* IHn をジェネラライズして、それを A' に適用する。 *)
    case: (cormen_lup A') => [[P L U]] {A'} /=. (* cormen_lup A' を P L U に分割する。 *)
    
    (* 置換を簡単にする。 *)
    rewrite is_perm_MA_PB.
    Check is_perm_mx P -> is_perm_mx (MA P).
    
    (* is_perm_mx を exist に変えて、s を代入する。 *)
    Check @is_perm_mxP F n.+1 P
      : reflect (exists s : {perm 'I_n.+1}, P = perm_mx s) (is_perm_mx P).
    (* rewrite /MA. *)
    case/is_perm_mxP => s ->.         (* 前提のexistsを場合分する。 *)
    
    (* (0,0) に 1 を置いても、置換行列であることに変わりがない。 *)
    (* lift0_mx は block_mx 1 0 0 とおなじ。 *)
    Check lift0_mx_is_perm F s : is_perm_mx (lift0_mx (perm_mx s)).
    Check lift0_mx_is_perm F s : is_perm_mx (block_mx 1 0 0 (perm_mx s)).
    rewrite lift0_mx_is_perm.
    done.
Qed.

(* 補題：P * A = L * U が成り立つ。 *)
Lemma cormen_lup_correct n (A : 'M_n.+1) :
  let: (P, L, U) := cormen_lup A in P * A = L * U.
Proof.
  elim: n => [|n IHn] /= in A *.
  - by rewrite !mul1r.
  - set k := odflt 0 [pick k | A k 0 != 0 ] : 'I_n.+2. (* 右辺は ``odflt _ _`` とだけでもよい。 *)
    set A1 : 'M_(1 + n.+1) := xrow 0 k A.              (* ``xrow _ _ _`` *)
    set A' := drsubmx A1 - (A k 0)^-1 *: dlsubmx A1 *m ursubmx A1. (* ``_ - _`` *)
    move/(_ A') : IHn.

    case: cormen_lup => [[P' L' U']] IHn. (* cormen_lup A' を計算する。 *)
    
    rewrite -mulrA -!mulmxE -xrowE -/A1 /= -[n.+2]/(1 + n.+1)%N -{1}(submxK A1).
    rewrite !mulmx_block !mul0mx !mulmx0 !add0r !addr0 !mul1mx -{L' U'}[L' *m _]IHn.
    rewrite -scalemxAl !scalemxAr -!mulmxA addrC -mulrDr {A'}subrK.
    congr (block_mx _ _ (_ *m _) _).
    rewrite [_ *: _]mx11_scalar !mxE lshift0 tpermL {}/A1 {}/k.
    
    (* [pick k | A k 0 != 0 ] で場合分けする。 *)
    case: pickP => /= [k nzAk0 | no_k].
    (* A k 0 が非零である k を取り出せた場合。 *)
    (* 前提 : forall x : 'I_n.+2, A x 0 != 0 *)
    (* 右辺の 2項目は単位行列である。 *)
    + by rewrite mulVf ?mulmx1.
      
    (* A k 0 が非零である k を取り出せず、デフォルトの0になった場合。 *)
    (* 前提 : (fun k : 'I_n.+2 => A k 0 != 0) =1 xpred0 *)
    (* ``H : dlsubmx (xrow 0)``_A = 0`` の rewrite をおこない、H を後で証明する。 *)
    (* (xrow 0)``_A は ``xrow 0 0 A`` の意味。わかりにくいと思うが、ring_scope *)
    + rewrite (_ : dlsubmx _ = 0).
      * by rewrite ?mul0mx.

      (* H : dlsubmx (xrow 0)``_A) = 0 の証明 *)
      * apply/colP=> i.
        rewrite !mxE.
        rewrite lshift0.
        rewrite (elimNf eqP (no_k (tperm 0 0 (rshift 1 i)))).
                         (* (no_k _)                          でもよい。 *)
        done.
Qed.

(* 補題：L の行列式は 1 *)
Lemma cormen_lup_detL n (A : 'M_n.+1) : \det (cormen_lup A).1.2 = 1. (* L *)
Proof.
  (* elim: n => [|n IHn] /= in A *. *)
  elim: n A => [|n IHn] /= A.
  - by rewrite det1.
  - set A' := _ - _.
    move/(_ A') : IHn.
    case: cormen_lup => [[P L U]] {A'}/=.   (* {A'}/= は ``simpl in A'`` の意味 *)
    by rewrite (@det_lblock _ 1) det1 mul1r.
Qed.

(* 補題：L の対角成分は 1。単三角行列 *)
Lemma cormen_lup_lower n A (i j : 'I_n.+1) :
  (i <= j)%N -> (cormen_lup A).1.2 i j = (i == j)%:R. (* L *)
Proof.
  (* elim: n => [|n IHn] /= in A i j *. *)
  elim: n A i j => [|n IHn] /= A i j.
  - by rewrite [i]ord1 [j]ord1 mxE.
  - set A' := _ - _.
    move/(_ A') : IHn.
    case: cormen_lup => [[P L U]] {A'}/= Ll.
    (*
      (i <= j)%N ->
      block_mx 1 0
      ((A (odflt 0 [pick k | A k 0 != 0 ]) 0)^-1 *:
      (P *m dlsubmx (xrow 0 (odflt 0 [pick k | A k 0 != 0 ]) A))) L i j = (i == j)%:R
     *)
    rewrite !mxE.
    (* ``split i`` の値、直和のどちらかを取るかの場合分けを行う。*)
    rewrite split1.
    case: unliftP => [i'|] -> /=.
    (*
goal 1 (ID 67243) is:
  (bump 0 i' <= j)%N ->
  row_mx
    ((A (odflt 0 [pick k | A k 0 != 0 ]) 0)^-1 *:
     (P *m dlsubmx (xrow 0 (odflt 0 [pick k | A k 0 != 0 ]) A))) L i' j = ((lift (n:=n.+2))``_i' == j)%:R

goal 2 (ID 67244) is:
 (0 <= j)%N -> (row_mx 1 0)``_j = (0 == j)%:R
     *)
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

(* 補題：U は上三角行列 *)
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

(**
補足説明 Ordinal型の補題

block_mx (row_mx と col_mx) の定義で split を使う。行列を分割するために、
``i : 'I_m+n`` を m を境界にして、 ``'I_m`` と ``'I_n`` のふたつの行列（直積）に変換することを行う。

以下において、そのsplitを定義するまでと、'I_(1 + n) の場合の補題 split1 の説明をする。
 *)

(* bump と lift *)
Print bump.             (* 自然数の補題。h 以上なら +1 する。 *)
(* bump = fun h i : nat => ((h <= i) + i)%N
   : nat -> nat -> nat
 *)
Compute bump 2 1.                           (* 1 *)
Compute bump 2 2.                           (* 3 *)
Print lift.                                 (* h 以上なら +1 する。 *)
(* fun (n : nat) (h : 'I_n) (i : 'I_n.-1) => Ordinal (lift_subproof h i)
     : forall [n : nat], 'I_n -> 'I_n.-1 -> 'I_n
                         h       i
 *)
(* 型から h が取りうる最大は n-1 であり、i が取りうる最大は n-2 である。
   bump の値が取りうる最大は n-1 である (h = i = n-2 の場合、+1 して i = n-1) から、
   帰り値は 'I_n.-1 でよい。 *)

(* split1 補題の中で unlift や unbump を使う。そのためそれらの補題が必要になる。 *)
(* unbump と unlift *)
Print unbump.             (* h を超えるなら -1 する。 *)
(* unbump = fun h i : nat => (i - (h < i))%N
     : nat -> nat -> nat
 *)
Compute unbump 2 2.                   (* 2 *)
Compute unbump 2 3.                   (* 3 *)
Print unlift.                         (* h を超えるなら -1 する。 *)
Check fun (n : nat) (h i : 'I_n) =>
        omap (fun u : {j : 'I_n | j != h} => Ordinal (unlift_subproof u)) (* omap に渡す関数 *)
          (insub i).                        (* subtype kit。自然数iを序数にする。 *)
(*
   : forall [n : nat], 'I_n -> 'I_n -> option 'I_n.-1
                        h      i
 *)
(* h = i の場合 None とする。それ以外の場合は、 *)
(* 型から h が取りうる最大は n-1 であり、i が取りうる最大は n-1 である。
   unbump の値が取りうる最大は n-2 である (h = n-2、i = n-1 の場合、-1 して i = n-2) から、
   帰り値は 'I_n.-1 でよい。 *)

(* lshift と rshift *)
Print lshift.                     (* i の値を変えずに、型を変える。 *)
(* fun (m n : nat) (i : 'I_m) => Ordinal (lshift_subproof n i)
   : forall [m : nat] (n : nat), 'I_m -> 'I_(m + n)
*)
(* 0 をシフトしても 0 である。型は面倒なことになっている。 *)
Check lshift0 : forall m n : nat, @lshift n.+1 m (0 : 'I_n.+1) =
                                    (0 : 'I_ ((fix add (n0 m0 : nat) {struct n0} : nat :=
                                                 match n0 with
                                                 | 0%N => m0
                                                 | p.+1 => (add p m0).+1
                                                 end) n m).+1).

Print rshift.                     (* m + i を返して、型を変える。 *)
(* lshft と型は同じ。 *)
(* fun (m n : nat) (i : 'I_n) => Ordinal (rshift_subproof m i)
     : forall (m : nat) [n : nat], 'I_n -> 'I_(m + n)
*)

(* unsplit *)
(* ``'I_m`` と ``'I_n`` を ``'I_(m + n)`` に変換する。``'I_m`` なら値はそのまま。
 ``'I_n``なら m を加算してシフトする。 *)
(* lshift と rshift のどちらかを行う。どちらかは、引数が直和になっているので決める。 *)
Print unsplit.
(* fun (m n : nat) (jk : 'I_m + 'I_n) => match jk with
                                      | inl j => lshift n j
                                      | inr k => rshift m k
                                      end
     : forall {m n : nat}, 'I_m + 'I_n -> 'I_(m + n)
 *)
(* split *)
(* unsplit の逆、lshift の逆か rshift の逆をやる。 *)
Print split.
(* fun (m n : nat) (i : 'I_(m + n)) =>
   match ltnP i m with
   | LtnNotGeq lt_i_m => inl (Ordinal lt_i_m)
   | GeqNotLtn ge_i_m => inr (Ordinal (split_subproof ge_i_m))
   end
   : forall {m n : nat}, 'I_(m + n) -> 'I_m + 'I_n
*)
(* ltnP を証明で使う場合は ``case: ltnP`` でよいが、関数定義に使う場合は上のようにする。 *)

(* split1 補題 *)
(**
split の値が直和のどちらかで場合分けするとき、
split1 で unlift の出てくる式に書き換えたのち、出てきたunliftを Some か None で場合分けする。

*)

(* Option 型から中身をとりだす。Noneならdefault値を使う。 *)
Check oapp : forall aT rT : Type, (aT -> rT) -> rT -> option aT -> rT.

(**
右辺は、oapp の機能によって、unlift の値が None なら ``inl 0`` を返す。``Some y`` なら ``inr y`` を返す。
よって、h = 0 なので、i = 0 なら ``0 : 'I_1`` を返す。さもなければ ``i-1 :  'I_n`` を返す。
*)
Check split1 : forall (n : nat) (i : 'I_(1 + n)), split i = oapp inr (inl 0) (unlift (n:=n.+1))``_i.
Check split1 : forall (n : nat) (i : 'I_(1 + n)), split i = oapp inr (inl 0) (@unlift n.+1 0 i).
Check split1 : forall (n : nat) (i : 'I_(1 + n)), split i =
                                                    oapp inr (inl 0) (@unlift n.+1 0 i) :> 'I_1 + 'I_n.
(* ``_i は 0 と i を適用するという意味。 *)
Locate "u '``_' i".                         (* := u 0 i *)

(* unliftP 補題 *)
(* ``case: unliftP`` で、unlift が Some i0 を返すか、None を返すかで場合分けするための補題。 *)
Check unliftP : forall (n : nat) (h i : 'I_n), unlift_spec h i (unlift h i).
Print unlift_spec.
(* unlift が Some i0 ただし i0 : 'I_n.+2.-1 を返すか、None を返すかで場合分けする。 *)
(* 前者の場合、i0 の中身の自然数を i' として取り出す。 *)

(* END *)
