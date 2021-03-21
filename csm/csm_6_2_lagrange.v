(**
Coq/SSReflect/MathComp による定理証明

6.2 テーマ2 有限群とラグランジュの定理
======
2018_05_02 @suharahiromichi

2021_03_06 @suharahiromichi
 *)

From mathcomp Require Import all_ssreflect.
From mathcomp Require Import fingroup.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section Lagrange.
(**
# 6.2.1 有限群の定義
 *)

  Open Scope group_scope.
  
  (* gT は finGroupType（有限群）型クラスの型インスタンスである。 *)
  Variable gT : finGroupType.
  
(**
## 定理：任意の剰余類の濃度は、もとの集合の濃度に等しい

テキストの順番とは異なりますが、
これは fingroup で証明されている補題を使って証明できるため先に証明します。
``csm_6_2_1_fingroup.v`` も参照してください。

使用するのは、次のふたつの補題です。
*)
(**
### 使用する補題 ``rcosetsP``

この補題の意味は以下です。

任意の集合Aが、
適当なxについて$H x$と等しいこと（適当なxの剰余類であること）と、
Aが$H \backslash G$の要素であることは、必要十分条件である：

$$(\exists x, x \in G \land A = H x) \iff A \in H \backslash G$$
*)
  Section Test.
    Variable A H G : {set gT}.
    
    Check rcosetsP
      : reflect (exists2 x, x \in G & A = H :* x) (A \in rcosets H G).
  End Test.

(**
### 使用する補題 ``card_rcoset``

この補題の意味は以下です。

任意のxの剰余類の濃度は、もとの集合の濃度に等しい：

$$\forall x, |A x| = |A|$$
*)  
  Check card_rcoset
    : forall (gT : finGroupType) (A : {set gT}) (x : gT), #|A :* x| = #|A|.

(**
### 証明したい補題 ``myCard_rcoset``

証明したいのは、以下の命題です。

剰余群に含まれる任意の剰余類の濃度は、もとの集合の濃度に等しい：

Goal: $$ A \in H \backslash G \to |A| = |H| $$

補題：``card_rcoset``は、任意のxに対して剰余類を決めているのに対して、
証明したい命題は、任意の$H \backslash G$の要素で剰余類を選んでいます。
そこに違いがあります。
*)
  Lemma myCard_rcoset (G H : {group gT}) (A : {set gT}) :
    A \in rcosets H G -> #|A| = #|H|.
  Proof.
    move/rcosetsP.
(**
Goal: $$ (\exists x, x \in G \land A = H x) \to |A| = |H| $$ 
*)
    case.
(**
Goal: $$ \forall x, x \in G \to A = H x \to |A| = |H| $$ 
*)
    move=> a asinG ->.
    rewrite card_rcoset.
(**
Goal: $$ |H| = |H| $$ 
*)
    done.

    Restart.
    case/rcosetsP => a ainG ->.
      by apply: card_rcoset.
  Qed.

(**
# 6.2.2 部分群の性質
*)
(**
## 部分群

以下では、$G$を群、$H$をその部分群とします。すなわち、$ H \in G $
*)
  Variable G H : {group gT}.              (* G, H は有限群型の変数 *)
  Hypothesis HG : H \subset G.

(**
## 同値関係の定義

bool型の二項関係（$\sim$）を定義します。

$$ x \sim y \equiv x y^{-1} \in H $$ 
*)  
  Definition R := [rel x y | x * y^-1 \in H].
  Check R : gT -> gT -> bool.               (* simpl_rel gT. *)
(**
テキストと異なりますが、Coq側でも演算子``~``を定義して使うことにします。
*)
  Notation "x ~ y" := (R x y) (at level 40, left associativity).
  
(**
## 同値関係の証明

$\sim$が、同値関係であることを証明します。
同値関係の定義 ``equivalence_rel`` は、 ``ssrbool.v``
で定義されていますので、これを証明します。
*)
  Print equivalence_rel.
  (*
    fun (T : Type) (R : rel T) => forall x y z : T, R z z * (R x y -> R x z = R y z).
   *)
  Set Printing All.
  Print equivalence_rel.
  (*
    fun (T : Type) (R : rel T) =>
    forall x y z : T,
    prod (is_true (R z z)) (forall _ : is_true (R x y), @eq bool (R x z) (R y z))
   *)
  Unset Printing All.
  
(**
``*`` は、prod の意味で、Type型のふたつの直積です。

これに対して、お馴染みの ``/\`` は、andの意味で、Prop型のふたつの直積を示します。

ここでは、両者は同じとといってよいと思います。
それぞれコンストラクタを適用することでゴールをふたつに分解できます。

- prod のコンストラクタは pair
- and のコンストラクタは conj

なお、conj を適用するときに、タクティクsplitを使うこともできます。
 *)

(**  
また、``=`` の両辺がboolであるなら、boolの値がおなじことを示すので、
これは、論理式としての必要十分条件（``<->``) を示します。

``apply/idP/idP`` を実行することで、
ゴールを必要条件と十分条件のふたつに分解できます。
*)
  
  Lemma equiv_rel_R : equivalence_rel R.
  Proof.
    rewrite /equivalence_rel => x y z.
(**
ゴールは、MathComp の表記で次のようになります：

```z ~ z * (x ~ y -> x ~ z = y ~ z)```
 *)
(**
Goal: $$ z \sim z \land (x \sim y\ \to (x\ \sim z \iff y \sim z)) $$

前述のとおり、pairを適用してでゴールを分けます：
*)
    apply: pair => /=.
(**
Goal: $$ z z^{-1} \in H $$
*)
    - by rewrite mulgV group1.
(**
Goal: $$ x y^{-1} \in H -> (x z^{-1} \in H \iff y z^{-1} \in H) $$

``=`` は ``<->`` の意味なので、前述のとおり ``apply/idP/idP`` を実行します。
*)
    - move=> xRinvy.                        (* xRinvy : x * y^-1 \in H *)
      apply/idP/idP.
      (* -> *)
      + move/groupVr in xRinvy.             (* xRinvy : (x * y^-1)^-1 \in H *)

(**
補題（積は閉じている）： groupM : ``x in H -> y in H -> x * y in H`` を使って、
ゴールの前提部の ``x * z^-1 \in H`` を ``(x * y^-1)^-1 * (x * z^-1) \in H``
に書き換えます。
 *)
        Check groupM : forall (gT : finGroupType) (G : {group gT}) x y,
            x \in G -> y \in G -> x * y \in G.
        Check groupM xRinvy : x * z^-1 \in H -> (x * y^-1)^-1 * (x * z^-1) \in H.
        move/(groupM xRinvy).
        Undo 2.
(**
ひとつ前で、xRinvy に groupVr を適用していますから、この2行をまとめて、
テキストのように書くこともできます。
 *)
        move/(groupM (groupVr xRinvy)).
          by rewrite invMg invgK mulgA -(mulgA y) mulVg mulg1.
          
      (* <- *)
(**
問題(1) 逆の証明にトライしてみてください！

ヒント： -> より簡単です。
*)
      + Check (groupM xRinvy) : y * z^-1 \in H -> x * y^-1 * (y * z^-1) \in H.
        admit.                              (* 問題(1) *)
  Admitted.
  
(**
# 6.2.3 剰余類の性質の形式化

``myCard_rcoset`` はすでに最初の節で証明していますので、次の定理の証明をします。
*)
(**
## 定理：

$$H x = \\{y \in G\ |\ x \sim y \\}$$
*)
  Lemma coset_equiv_class (x : gT) (xinG : x \in G) :
    H :* x = [set y in G | x ~ y].
  Proof.
    apply/setP => /= y. (* 任意の要素が同じなら、集合が等しいことつかう。 *)
    rewrite inE.        (* \in に関する簡約を行います。 *)
    apply/idP/idP.
    - case/rcosetP => z zinH -> {y}.
      apply/andP.
      apply: conj.
      + rewrite groupM //. (* groupM : z \in G -> x \in G -> z * x \in G *)
        move/subsetP : HG => HG'.          (* HG' : {subset H <= G} *)
        Check (HG' z zinH) : z \in G.
          by move: (HG' z zinH).
      + by rewrite invMg mulgA mulgV mul1g groupV.
    - case/andP => yinG xinvyinH.
      apply/rcosetP.
(**
ex_intro2 を適用して exists2 を消します。
テキストにあるプレースホルダーを埋めると次のようになります。
*)
      Check (ex_intro2 (fun g => g \in H)
                       (fun a => y = a * x)
                       (y * x^-1)) :
        y * x^-1 \in H ->
        y = y * x^-1 * x ->
        exists2 a : gT, a \in H & y = a * x.
      apply: (ex_intro2 _ _ (y * x^-1)).
      
      + by rewrite -groupV invMg invgK.
      + by rewrite -mulgA mulVg mulg1.
  Qed.
  
(**
## 補題：

$H \backslash G$ は、$G$の$\sim$についての商と等しい。
*)
  Lemma rcosets_equiv_part : rcosets H G = equivalence_partition R G.
  Proof.
    apply/setP => /= X.
    rewrite /rcosets /equivalence_partition.
    apply/idP/idP.
    - case/rcosetsP => x0 x0inG X_Hx.
      apply/imsetP.
      apply: (ex_intro2 _ _ x0).
      + done.
      + Check @coset_equiv_class x0.
          by rewrite -coset_equiv_class.
    - case/imsetP => x1 xinG Hypo.
      apply/imsetP.
      (* プレースホルダーを埋めると次になる。 *)
      Check (ex_intro2 (fun g => g \in G)
                       (fun x => X = rcoset H x)
                       x1) :
        x1 \in G ->
               X = rcoset H x1 ->
               exists2 x : gT, x \in G & X = rcoset H x.
      apply: (ex_intro2 _ _ x1).
      + done.
      + rewrite rcosetE.
        by rewrite coset_equiv_class.
  Qed.
  
(**
## 補題：

$H \backslash G$ は、$G$の$\sim$についての分割である。

商であるということと、分割になっているということは区別されます。
ひとつまえの補題と違って、後者では$\sim$が明示的に現れないことがポイントです。

ラグランジュの定理の証明で実際に使用するのは、この補題です。
*)
  Lemma partition_rcosets : partition (rcosets H G) G.
  Proof.
    rewrite rcosets_equiv_part.
    apply/equivalence_partitionP => x y z xinG yinG zinG.
      by apply : equiv_rel_R.
  Qed.

(**
# 6.2.4 ラグランジュの定理
 *)
(**
## 指数について
  
テキストにもあるように、
一般的な数学の記法では、$(G : H)$ は（$H$による$G$の）右剰余類の個数を表します。
これを（$H$による$G$の）指数ともいいます。

$$(G : H) = |H \backslash G|$$

MathComp では、``#|_ : _|``という2項のNotationです。
これが定義であることを確認します。
*)
  Goal #|G : H| = #|rcosets H G|.
  Proof.
    rewrite /indexg.
    done.
  Qed.

(**
（参考）右剰余類の個数も左剰余類の個数もおなじなので、
fingroup.v にある補題``card_lcosets``で、次が成り立ちます：

$$(G : H) = |G / H| = |H \backslash G|$$
*)  
  Goal #|G : H| = #|lcosets H G|.
  Proof.
    rewrite card_lcosets.
    done.
  Qed.
  
(**
## 使用する補題 ``card_partition``

finset.v で証明されている補題です。P（集合の集合）が D（集合）の分割になっているならば、
Pの全ての要素の濃度の総和は、Dの濃度に等しい。

$$ |D| = \sum_{A \in P}\ |A|$$
*)  
  Check card_partition
    : forall (T : finType) (P : {set {set T}}) (D : {set T}),
      partition P D -> #|D| = \sum_(A in P) #|A|.

(**
これに直前に証明した補題を組み合わせます。

組み合わせると、剰余類の集合の要素の濃度の総和は、群$G$の濃度に等しい、となります。
これは、剰余類の集合の集合は、群$G$の分割であるためですね。

$|G| = \sum_(A \in H \backslash G)\ |A|$
*)
  Check (card_partition partition_rcosets)
    : #|G| = \sum_(A in rcosets H G) #|A|.

(**
## 使用する補題 ``eq_bigr``

myCard_rcoset の $|A| = |H|$ を Σの中に適用して書き換える補題です。

``\sum_`` (Σ) などの ``\bigop[/]_`` の中はλ変数で束縛されていますから、
rewriteでは書き換えできないので、``bigop.v`` で証明された補題を使います。
``eq_bigr`` は、bigopに一般に証明されていますが、``\sum_`` (Σ) ならば次のようになります。

$\sum_{i \in H \backslash G}\ |A| = \sum_{i \in H \backslash G}\ |H|$
*)  
  Check ((eq_bigr (fun _ => #|H|)) (@myCard_rcoset G H))
    : \sum_(i in rcosets H G) #|i| = \sum_(i in rcosets H G) #|H|.
  
(**
## 総和についての補題 ``sum_nat_const``

総和についての補題を紹介します。
テキストでは、補題``big_const``を使って``iter``の式に変換していますが、
そのものずばりの補題があるので、それを使います。
これは、定数の総和をもとめる $\sum_{0 <= i < n} c = c\ n$ の集合版です。

$$\sum_{i \in A} c = |A|\ c$$
 *)
  Check sum_nat_const
    : forall (fT : finType) (A : pred fT) (c : nat), \sum_(i in A) c = (#|A| * c)%N.
  
(**
## 定理の証明

証明したいのは以下です。
$G$を群、$H$をその部分群とするとき、
$G$の濃度は、$H$の濃度と（$H$による$G$の）指数の積に等しい：

$$|G| = |H|\ (G : H)$$

指数の意味は冒頭を参照してください。
*)  
  Theorem myLagrange : #|G| = (#|H| * #|G : H|)%nat.
  Proof.
(**
Goal: $$|G| = |H|\ (G : H)$$
*)
    rewrite (card_partition partition_rcosets).
(**
Goal: $$\sum_{A \in H \backslash G} |A| = |H|\ (G : H)$$
*)
    rewrite ((eq_bigr (fun _ => #|H|)) (@myCard_rcoset G H)).
(**
Goal: $$\sum_{A \in H \backslash G} |H| = |H|\ (G : H)$$
*)
    rewrite sum_nat_const.
(**
Goal: $$|H \backslash G|\ |H| = |H|\ |G : H|$$
*)
    rewrite /indexg.
      by rewrite mulnC.
  Qed.

End Lagrange.

(**
# 問題(1)の答え

```
        move/(groupM xRinvy).
          by rewrite mulgA -(mulgA x) mulVg mulg1.
  Qed.
```
 *)

(* END *)
