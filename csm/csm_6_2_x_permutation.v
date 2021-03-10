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
そのうち点対称の3個 N が正規部分群になります。

すなわち

```|G / N| = (G : N) = |G| / |N| = 6 / 3 = 2```

になるはずです。
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
Definition o0 :'I_3 := ord0.                (* 0 *)
Definition o1 : 'I_3 := @Ordinal 3 1 erefl. (* 1 *)
Definition o2 : 'I_3 := @Ordinal 3 2 erefl. (* 2 *)

Definition p01 : 'S_3 := tperm o0 o1.       (* (01) *)
Definition p02 : 'S_3 := tperm o0 o2.       (* (02) *)
Definition p12 : 'S_3 := tperm o1 o2.       (* (12) *)
Definition p021 := p01 * p02.               (* (021) *)
Definition p012 := p02 * p01.               (* (012) *)

(**
実際に置換してみる。
*)
Goal p021 o0 = o1.                          (* 0 -> 1 *)
Proof. rewrite /o2 !permE /= /p02 /p01 !permE //. Qed.

Goal p021 o1 = o2.                          (* 1 -> 2 *)
Proof. rewrite !permE /= /p02 /p01 !permE //. Qed.

Goal p021 o2 = o0.                          (* 2 -> 0 *)
Proof. rewrite !permE /= /p02 /p01 !permE //. Qed.

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

Definition G : {group 'S_3} := [group of << SG >>].
Definition N : {group 'S_3} := [group of << SN >>].

(**
## N は G の部分集合である。 
*)
Goal SN \subset SG.
Proof.
  apply/subsetP => /= p.
    by rewrite !inE.
Qed.

Lemma N_subset_G : N \subset G.
Proof.
  rewrite /=.
  apply genS.
  apply/subsetP => /= p.
    by rewrite !inE.
Qed.

(**
## 剰余類 (01)N は G の部分集合である。
*)
Goal N :* p01 = rcoset N p01.
Proof.
  by rewrite rcosetE.
Qed.

Goal (SG :* p01) \subset SG.
  apply/subsetP => /= p.
    by rewrite !inE.
Qed.  

Goal (N :* 1) \in rcosets N G.
Proof.
  (* rewrite -rcoset1. *)
  rewrite mem_rcosets.
  rewrite /N /SN /G /SG.
  rewrite /mulg /= /set_mulg /=.
Admitted.

Goal (N :* p01) \in rcosets N G.
Proof.
  rewrite mem_rcosets.
  rewrite /N /SN /G /SG.
  rewrite /mulg /= /set_mulg /=.
  Admitted.

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

(**
正規部分群なら、``|G| = |G / N| * |N|'' が成り立つので、
``|G / N|`` の要素の数は 2 になります。
*)
Goal #|G / N| = 2.
Proof.
  rewrite -divg_normal.                     (* quotient.v *)
  - by rewrite G__6 N__3.
  - by apply: N__G.
Qed.

(* END *)
