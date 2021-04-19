(**
Coq/SSReflect/MathComp による定理証明

（6.2 節補足）3次対象群
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
そのうち点対称の3個 N が正規部分群になります。

すなわち、NによるGの指数は、

```|G / N| = (G : N) = |G| / |N| = 6 / 3 = 2```

になるはずです。これは G の位数でもあります。
*)

(**
# 文献

[1] 学習院大学 中野伸先生の講義ノート

[https://pc1.math.gakushuin.ac.jp/~shin/html-files/Alg1/2017/g07.pdf]


[2] Affeldt先生のチュートリアル (p.147)

[https://staff.aist.go.jp/reynald.affeldt/ssrcoq/ssrcoq.pdf]


[3] Affeldt先生のチュートリアル（サンプルコード）

[https://staff.aist.go.jp/reynald.affeldt/ssrcoq/permutation_example.v]
*)

(**
# 3次対象群を作る

最初に、サイズ3の順序数、0、1、2を を定義します。
*)
Definition o0 : 'I_3 := ord0.               (* 0 *)
Definition o1 : 'I_3 := @Ordinal 3 1 erefl. (* 1 *)
Definition o2 : 'I_3 := @Ordinal 3 2 erefl. (* 2 *)

(**
線対称にあたる3個の置換：
*)
Definition p01 : 'S_3 := tperm o0 o1.       (* (01) *)
Definition p02 : 'S_3 := tperm o0 o2.       (* (02) *)
Definition p12 : 'S_3 := tperm o1 o2.       (* (12) *)

(**
点対象にあたる2個の置換、および、恒等置換：
*)
Definition p021 : 'S_3 := p01 * p02.        (* (021) *)
Definition p012 : 'S_3 := p02 * p01.        (* (012) *)
Check 1 : 'S_3.

(**
実際に置換してみます。
*)
Goal p021 o0 = o1.                          (* 0 -> 1 *)
Proof. rewrite /o2 !permE /= /p02 /p01 !permE //. Qed.

Goal p021 o1 = o2.                          (* 1 -> 2 *)
Proof. rewrite !permE /= /p02 /p01 !permE //. Qed.

Goal p021 o2 = o0.                          (* 2 -> 0 *)
Proof. rewrite !permE /= /p02 /p01 !permE //. Qed.

(**
文献[3]にあるタクティクで、置換についての簡約をおこないます。
*)
Ltac same_perm :=
  let x := fresh in
  apply/permP => /= x;
  let x0 := fresh in
  case: (boolP (x == o0)) => [/eqP -> | x0];
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
  have : p021 o0 = (1 : 'S_3) o0 by rewrite abs !permE.
    by rewrite !permE /= /p02 /p01 !permE.
Qed.

Lemma p012_1 : p012 <> 1.
Proof.
  move=> abs.
  have : p012 o0 = (1 : 'S_3) o0 by rewrite abs !permE.
    by rewrite !permE /= /p02 /p01 !permE.
Qed.

Lemma p021_neq_p012 : p021 <> p012.
Proof.
  move=> abs.
  have : p021 o0 = p012 o0 by rewrite abs.
  rewrite !permE /=.
  rewrite /p01 /p02.
    by rewrite !permE.
Qed.

Lemma p02_neq_p12 : p02 <> p12.
Proof.
  move=> abs.
  have : p02 o0 = p12 o0 by rewrite abs !permE.
    by rewrite !permE /=.
Qed.

(**
# 有限集合としての3次対象群
*)
Definition SG := [set x in 'S_3].
Definition SN := [set p021; p012; 1].

Definition G : {group 'S_3} := [group of <<SG>>].
(**
``G = {1, (021), (012), (01), (02), (12)}``
*)
Definition N : {group 'S_3} := [group of <<SN>>].
(**
``N = {1, (021), (012)}``
*)

(**
## N は G の部分集合である。 
*)
Lemma SN_subset_SG : SN \subset SG.
Proof.
  apply/subsetP => /= p.
    by rewrite !inE.
Qed.

Lemma N_subset_G : N \subset G.
Proof.
  rewrite /=.
  apply: genS.
    by apply: SN_subset_SG.
Qed.

(**
## SN は 1 をもち 掛け算で閉じている
*)
Lemma group_set_N : group_set SN.
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
             ++++ move/eqP=> Hs /eqP Hr.
                    by rewrite Hr Hs -{1}p021_inv mulVg !inE eqxx orbT.
             ++++ move/eqP=> Hs /eqP Hr.
                    by rewrite Hr Hs p012_p012 !inE eqxx.
         +++ move/eqP => Hs /eqP Hr.
               by rewrite Hr Hs mulg1 !inE eqxx orbT.
    + case/orP : Hs.
      ++ case/orP.
         +++ move/eqP=> Hs /eqP Hr.
               by rewrite Hr Hs mul1g !inE eqxx.
         +++ move/eqP=> Hs /eqP Hr.
               by rewrite Hr Hs mul1g !inE eqxx orbT.
      ++ move/eqP=> Hs /eqP Hr.
           by rewrite Hr Hs mul1g !inE eqxx orbT.
Qed.

(**
# サイズを求める
 *)
(**
## |G|
*)
Lemma G__6 : #|G| = 6.
Proof.
  rewrite /=.
  transitivity (#|[set x in 'S_3]|).
  - have : group_set [set x in 'S_3] by apply/group_setT.
      by move/(gen_set_id) => ->.
  - rewrite cardsE.
    transitivity (#|perm_on [set x in 'I_3]|).
    + apply: eq_card => /= p.
      rewrite inE.
      apply/esym.
      case: p => pval i.
      rewrite /perm_on.
      rewrite /mem.
      rewrite /=.
      rewrite /in_mem.
      rewrite /=.
      apply/subsetP => j /=.
        by rewrite inE.
    + by rewrite card_perm cardsE card_ord.
Qed.

(**
# |N|
*)
Lemma N__3 : #|N| = 3.
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
          by apply: p021_1.
      * case/andP => /eqP ->.
        move/eqP.
          by apply: p012_1.
    + rewrite cards0.
      suff -> : p021 != p012.
      * done.
      * apply/eqP.
        by apply: p021_neq_p012.
Qed.

(**
## |G : N|

G の N による指数を求めます。
*)
Goal #|G : N| = 2.
Proof.
  rewrite -divgS.                           (* fingroup.v *)
  - by rewrite G__6 N__3.
  - by apply: N_subset_G.
Qed.

(**
# N は正規部分群である
*)
Lemma N__G : N <|G.
Proof.
  apply: index2_normal.
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
      apply: sub_gen.
      apply/subsetP => p Hp /=.
        by rewrite inE.
Qed.

(**
剰余群を求める。位数2の巡回群になる。
*)
Lemma p012_p01__p02 : p012 * p01 = p02.     (* (012)(01) = (02) *)
Proof. same_perm. Qed.

Lemma p021_p01__p12 : p021 * p01 = p12.     (* (021)(01) = (12) *)
Proof. same_perm. Qed.

(**
```N \ G = {N, N(01)}```

```= {{1, (021), (012)}, {1, (021), (012)}(01)}```

```= {{1, (012), (021)}, {(01), (02), (12)}}```

```
NN = N              N^0*N^0  = N^0
NN(01) = N(01)      N*N^1    = N^1
N(01)N(01) = N      N^1*N*^1 = N^2 = N^0
```
*)

(**
正規部分群なら、``|G| = |N \ G| * |N| = |G / N| * |N|'' が成り立つので、
``|G / N|`` の要素の数は 2 になります。ここで「*」は自然数の掛け算。
*)
Goal #|G / N| = 2.
Proof.
  rewrite -divg_normal.                     (* quotient.v *)
  - by rewrite G__6 N__3.
  - by apply: N__G.
Qed.

(* END *)
