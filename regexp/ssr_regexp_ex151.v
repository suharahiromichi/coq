Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq fintype.
Require Import div prime.
Require Import regexp pumping.

(**
https://www.ps.uni-saarland.de/~doczkal/regular/
の Coq development からリンクされる、
ConstructiveRegularLanguages.tgz
を展開して、make する。
*)
(**
以下は、その同じ場所で実行する。
*)

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

(**
Tukuba Coq Users' Grup 「Coqによる定理証明」
坂口さん著「反復定理で遊ぼう」 1.5.1 から。
*)

Check pumping.
(**
(0) i,j,kは自然数、x,y,z,u,v,wは語である。a,b,cは文字である。
(1) Lは与えられた語sが正規表現であるかを判定する。例1.5.1の「lang a b」が Lに代入される。
(2) "++" は語の連結。
(3) 反復補題：Lは正規言語 (reguar L) ->
    (∃k, ∀x,y,z, k≦|y| /\ L(xyz) /\ (∃u,v,w, y = uvw -> v≠ε -> ∀i, L(xu(v^i)wz)))
(4) 反復補題は「正規言語なら」というかたちになっている。逆は成立するとは限らない。
(5) pumpingは(3)の反復補題の対偶である。

 : forall (char : finType) (L : automata.word char -> Prop),
       (forall k : nat,
        exists x y z : seq char,
          k <= size y /\
          L (x ++ y ++ z) /\
          (forall u v w : seq char,
           y = u ++ v ++ w ->
           ~~ nilp v ->
           exists i : nat, L (x ++ u ++ rep v i ++ w ++ z) -> False)) ->
       ~ regular L
*)
(**
反復補題は、
正規言語 -> DFAがある -> 状態は有限である -> 状態を繰り返しても同じところに戻る
ということを言っている。

また、(3)の外側の「->」の右は、「状態を繰り返しても。。」を厳密にいうものである。
DFTが語を受理して状態p0からpeに遷移すること δ'(p0, xyz) = pe を「p0 ---δ'xyz---> pe」と書く。

xyzを受理するDFAを考える。
p0 ------------------------------------δ'xyz---------------------------------> pe

p0 ----δ'x----> px --------------------δ'y-------------------> py ----δ'z----> pe

pxからpyの途中で、p'を2回通過することは必ずある。その前後の語（空でない）をvとする。
y=uvw。
p0 ----δ'x----> px ----δ'u----> p' ----δ'v----> p' ----δ'u---> py ----δ'z----> pe

xu(v^i)wzのように、vの語をi回にすると、p'--->p'をi-1回だけ余計に繰り返すことになる。
                                +---------------+
                                V   i回繰り返す  |
p0 ----δ'x----> px ----δ'u----> p' ----δ'v----> p' ----δ'u---> py ----δ'z----> pe
*)

Variable char : finType.

Lemma nseq_eq_cat (x : char) n xs ys :
  nseq n x = xs ++ ys -> nseq (size xs) x = xs /\ nseq (size ys) x = ys.
Proof.
  elim: n xs ys => //=.
  - by do 2 case=> //=.
  - move=> n IH [] //=.
    + by case=> //= y ys [] H H0; subst y ys; rewrite size_nseq.
    + by move=> a xs ys [] H; subst a; case/IH => {2}<- {2}<-. (* 2番め出現でrewriteする。 *)
Qed.

(** 1.5.1 例: {a^n b^n | n : nat} の言語 *)
Definition lang (a b : char) : word char -> Prop :=
  fun (s : word char) => exists (n : nat), s = nseq n a ++ nseq n b.

(** lang が正規言語でないことを証明する *) (* 一部を冗長に書き直している。 *)
Lemma anbn_non_regular (a b : char) :
  a != b -> ~ regular (lang a b).
Proof.
  move/negbTE => H.
  apply pumping => k.
  exists [::].
  exists (nseq k a).
  exists (nseq k b).
  rewrite size_nseq leqnn /=.
  split; last split.
  - by [].
  - exists k. by [].
  - move=> u v w H0.
    move: H0 (H0).                          (* 前提をふたつにコピーする。 *)
    (* do 2 case/nseq_eq_cat => <-. *)
    case/nseq_eq_cat => <-.
    case/nseq_eq_cat => <-.
    move=> <-.
    move: {u v w} (size u) (size v) (size w) => u v w.
    rewrite !cat_nseq_eq addnA.
    move/(f_equal size); rewrite !size_nseq => -> {k}; case: v => // v _.
    exists 0; case=> /= x H0.
    move: (f_equal (count (fun c => c == a)) H0).
    move: (f_equal (count (fun c => c == b)) H0).
    rewrite !count_cat !non_regular.count_nseq !eqxx eq_sym.
    rewrite H !mul1n !mul0n.
    nat_norm=> <- /eqP; rewrite addnCA -addSn -{1}(add0n (u + w)) eqn_add2r.
    by [].
Qed.

(* END *)
