(**
Coq/SSReflect/MathComp による定理証明

3次対象群
======

2021_03_08 @suharahiromichi
 *)

From mathcomp Require Import all_ssreflect.
From mathcomp Require Import all_fingroup.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Open Scope group_scope.

(**
# はじめに

``perm.v`` の使い方の練習として、
3次対象群にラグランジュの定理が成り立つことを計算してみます。

3次対象群 G は、正三角形の6個の対称移動のことで、
そのうち点対称の3個 N が正規部分群であるので、
ラグランジュの定理から、

```(G : N) = | G | / | N | = 6 / 3 = 2```

が成り立つはずです。これを実際に計算してみましょう。
*)


(**
# 文献

- 学習院大学 中野伸先生の講義ノート

[https://pc1.math.gakushuin.ac.jp/~shin/html-files/Alg1/2017/g07.pdf]


- Affeldt先生のチュートリアル (p.147)

[https://staff.aist.go.jp/reynald.affeldt/ssrcoq/ssrcoq.pdf]


- Affeldt先生のチュートリアル（サンプルコード）

[https://staff.aist.go.jp/reynald.affeldt/ssrcoq/permutation_example.v]
*)



(**
# 3次対象群を作る
*)
Definition ord1 : 'I_3 := @Ordinal 3 1 erefl. (* 1 *)
Definition ord2 : 'I_3 := @Ordinal 3 2 erefl. (* 2 *)

Definition p01 : 'S_3 := tperm ord0 ord1.   (* (01) *)
Definition p02 : 'S_3 := tperm ord0 ord2.   (* (02) *)
Definition p12 : 'S_3 := tperm ord1 ord2.   (* (12) *)
Definition p021 := p01 * p02.               (* (021) *)
Definition p012 := p02 * p01.               (* (012) *)

(**
実際に置換してみる。
*)
Goal p021 ord0 = ord1.                      (* 0 -> 1 *)
Proof. rewrite /ord2 !permE /= /p02 /p01 !permE //. Qed.

Goal p021 ord1 = ord2.                      (* 1 -> 2 *)
Proof. rewrite !permE /= /p02 /p01 !permE //. Qed.

Goal p021 ord2 = ord0.                      (* 2 -> 0 *)
Proof. rewrite !permE /= /p02 /p01 !permE //. Qed.

Ltac same_perm :=
  let x := fresh in
  apply/permP => /= x;
  let x0 := fresh in
  case: (boolP (x == ord0)) => [/eqP -> | x0];
    [by do ! rewrite !permE /= |
     let x1 := fresh in
     case: (boolP (x == @Ordinal 3 1 erefl)) => [/eqP -> | x1];
       [by do ! rewrite !permE /= |
        let x2 := fresh in
        case: (boolP (x == @Ordinal 3 2 erefl)) => [/eqP -> | x2];
          [by do ! rewrite !permE /= |
           (suff : False by done) ;
           case: x x0 x1 x2; case=> //; case=> //; by case]]].


Lemma p021_p021 : p021 * p021 = p012.
Proof. same_perm. Qed.

Lemma p012_p012 : p012 * p012 = p021.
Proof. same_perm. Qed.

Lemma p021_inv : p021 ^-1 = p012.
Proof.
  rewrite /p021.
  rewrite invMg.
  rewrite tpermV.
    by rewrite tpermV.
Qed.

Lemma p021_1 : p021 <> 1.
Proof.
  move=> abs.
  have : p021 ord0 = (1 : 'S_3) ord0 by rewrite abs !permE.
    by rewrite !permE /= /p02 /p01 !permE.
Qed.

Lemma p012_1 : p012 <> 1.
Proof.
  move=> abs.
  have : p012 ord0 = (1 : 'S_3) ord0 by rewrite abs !permE.
    by rewrite !permE /= /p02 /p01 !permE.
Qed.

Lemma p021_neq_p012 : p021 <> p012.
Proof.
  move=> abs.
  have : p021 ord0 = p012 ord0 by rewrite abs.
  rewrite !permE /=.
  rewrite /p01 /p02.
    by rewrite !permE.
Qed.

Lemma p02_neq_p12 : p02 <> p12.
Proof.
  move=> abs.
  have : p02 ord0 = p12 ord0 by rewrite abs !permE.
    by rewrite !permE /=.
Qed.

(**
# 有限集合としての3次対象群
*)
Definition G : {group 'S_3} := [group of << [set x in 'S_3] >>].

Definition N : {group 'S_3} := [group of << [set p021; p012; 1] >>].

Lemma N_subset_G : N \subset G.
Proof.
  rewrite /=.
  apply genS.
  apply/subsetP => /= p.
    by rewrite !inE.
Qed.

Lemma group_set_N : group_set [set p021; p012; 1].
Proof.
  apply/group_setP.
  split.
  - by rewrite !inE eqxx orbT.
  - move=> /= r s Hr Hs.
    rewrite !inE in Hr.
    rewrite !inE in Hs.
    case/orP : Hr.
    + case/orP.
      ++ move/eqP => Hr.
         +++ case/orP : Hs.
             ++++ case/orP.
                  move/eqP=> Hs.
                    by rewrite Hr Hs p021_p021 !inE eqxx orbT.
             ++++ move/eqP => Hs.
                    by rewrite Hr Hs -{1}p021_inv mulgV !inE eqxx orbT.
         +++ move/eqP => Hs.
               by rewrite Hr Hs mulg1 !inE eqxx.
      ++ case/orP : Hs.
         +++ case/orP.
             move/eqP=> Hs /eqP Hr.
               by rewrite Hr Hs -{1}p021_inv mulVg !inE eqxx orbT.
         +++ move/eqP=> Hs /eqP Hr.
               by rewrite Hr Hs p012_p012 !inE eqxx.
    + move/eqP => Hs /eqP Hr.
        by rewrite Hr Hs mulg1 !inE eqxx orbT.
  - case/orP : Hs.
    + case/orP.
      move/eqP=> Hs /eqP Hr.
        by rewrite Hr Hs mul1g !inE eqxx.
    + move/eqP=> Hs /eqP Hr.
        by rewrite Hr Hs mul1g !inE eqxx orbT.
  - move/eqP=> Hs /eqP Hr.
      by rewrite Hr Hs mul1g !inE eqxx orbT.
Qed.

Lemma G__6 : #| G | = 6.
Proof.
  rewrite /=.
  transitivity (#|[set x in 'S_3]|).
  - have : group_set [set x in 'S_3] by apply/group_setT.
      by move/(gen_set_id) => ->.
  - rewrite cardsE.
    transitivity (#|perm_on [set x in 'I_3]|).
    + apply eq_card => /= p.
      rewrite inE.
      apply/esym.
      destruct p.
      rewrite /perm_on.
      rewrite /mem.
      rewrite /=.
      rewrite /in_mem.
      rewrite /=.
      apply/subsetP => j /=.
        by rewrite inE.
    + by rewrite card_perm cardsE card_ord.
Qed.

Lemma N__3 : #| N | = 3.
Proof.
  rewrite /=.
  transitivity (#|[set p021; p012; 1]|).
  - rewrite gen_set_id //.
    exact group_set_N.
  - rewrite cardsU.
    rewrite cards1.
    rewrite cards2.
    set tmp2 := _ :&: _.
    rewrite (_ : tmp2 = set0); last first.
    + rewrite /tmp2.
      apply/eqP/set0Pn.
      case => q /=.
      rewrite !inE.
      rewrite andb_orl.
      case/orP.
      * case/andP.
        move/eqP => ->.
        move/eqP.
          by apply p021_1.
      * case/andP => /eqP ->.
        move/eqP.
          by apply p012_1.
    + rewrite cards0.
      suff -> : p021 != p012.
      * done.
      * apply/eqP.
        by apply p021_neq_p012.
Qed.

Goal #| G : N | = 2.
Proof.
  rewrite -divgS.
  - by rewrite G__6 N__3.
  - by apply: N_subset_G.
Qed.

(**
# N は正規部分群である
*)
Lemma N__G : N <| G.
Proof.
  apply index2_normal.
  - by apply: N_subset_G.
  - move: (LagrangeI G N).
    rewrite G__6.
    suff -> : #|G :&: N| = 3.
    + rewrite (_ : 6 = 3 * 2)%nat //.
      move/eqP.
      rewrite eqn_mul2l /=.
        by move/eqP.
    + set tmp := _ :&: _.
      suff : tmp = N by move=> ->; exact N__3.
      rewrite {}/tmp.
      apply/setIidPr.
      apply sub_gen.
      apply/subsetP => p Hp /=.
        by rewrite inE.
Qed.

(* END *)
