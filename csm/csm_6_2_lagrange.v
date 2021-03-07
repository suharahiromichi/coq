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
# 6.2.1 有限群の定義 (see. fingroup.v)

finType型クラスのインスタンス型 T を台とする。

-二項演算 mul T -> T -> T が存在する。
-元 one : T が存在する。
-関数 inv : T -> T が存在する。
-mul は結合律を満たす。
-one は左単位元である。
-inv は対合である（2回適用するともとにもどる）。inv (inv x) = x
-inv と mul はモルフィズムを満たす。inv (mul x y) = mul (inv y) (inv x)

 *)

  Open Scope group_scope.
  
  (* gT は finGroupType（有限群）型クラスの型インスタンスである。 *)
  Variable gT : finGroupType.
  
  Section Test.
    Variable x y z : gT.
    Variable G : {group gT}.
    
    (* 群の公理 *)
    Goal 1 \in G. Proof. by rewrite group1. Qed.
    Goal 1 * x = x. Proof. by rewrite mul1g. Qed.
    Goal x * y * z = x * (y * z). Proof. by rewrite mulgA. Qed.
    Goal x^-1^-1 = x. Proof. by rewrite invgK. Qed.
    Goal (x * y)^-1 = y^-1 * x^-1. Proof. by rewrite invMg. Qed.
    
    (* 群の定理 *)
    Goal x * 1 = x. Proof. by rewrite mulg1. Qed.
    Goal x * x^-1 = 1. Proof. by rewrite mulgV. Qed.
    Goal x^-1 * x = 1. Proof. by rewrite mulVg. Qed.
    Goal x \in G -> x^-1 \in G. Proof. by move/groupVr. Qed.
    Goal x \in G -> y \in G -> x * y \in G. Proof. apply: groupM. Qed.
    
    Check mulgV : forall T : finGroupType, forall x, x * x^-1 = 1.
    Check groupM : forall (gT : finGroupType) (G : {group gT}) (x y : gT),
        x \in G -> y \in G -> x * y \in G.
    Check groupVr : forall (gT : finGroupType) (G : {group gT}) (x : gT),
        x \in G -> x^-1 \in G.
  End Test.
  
(**
## coset と cosets


- rcoset 右剰余類（$\sim$ による同値類） $H\ x$、 ``H :* x``

- rcosets 右剰余群（$\sim$ による商） $H \backslash G$



後で定義する同値関係$\sim$は右合同であるので、
本資料は、特に断りのない限り、右剰余類だけを考えます。
*)

(**
## 定理：任意の剰余類の濃度は、もとの集合の濃度に等しい

テキストの順番とは異なるが、これは fingroup で証明されている補題を使って証明できるため、
先に証明します。
 *)
(**
使用するのは、次のふたつの補題です：
*)
(**
### 使用する補題 ``rcosetsP``

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

任意のxの剰余類の濃度は、もとの集合の濃度に等しい：

$$\forall x, |A x| = |A|$$
*)  
  Check card_rcoset
    : forall (gT : finGroupType) (A : {set gT}) (x : gT), #|A :* x| = #|A|.

(**
### 証明したい補題 ``myCard_rcoset``

証明したいのは、以下の命題です：

剰余類の集合の任意の要素の濃度は、もとの集合の濃度に等しい。

Goal: $$ A \in H \backslash G \to |A| = |H| $$

補題：``card_rcoset``は、任意のxに対して剰余類を決めているのに対して、
ここでは、任意の$H \backslash G$の要素で剰余類を選んでいます。
多分、そこに違いがあるのだろうと思います。
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
テキストにはありませんが、演算子``~``を定義しておきます。
*)
  Notation "x ~ y" := (R x y) (at level 40, left associativity).
  
(**
## 同値関係の証明

$\sim$が、同値関係であることを証明します。
equivalence_rel は ssrbool で定義されています。
*)
(**
   fun (T : Type) (R : rel T) => forall x y z : T, R z z * (R x y -> R x z = R y z)
*)
  Set Printing All.
  Print equivalence_rel.
  (*
    fun (T : Type) (R : rel T) =>
    forall x y z : T,
    prod (is_true (R z z)) (forall _ : is_true (R x y), @eq bool (R x z) (R y z))
   *)
  Unset Printing All.
  
  Lemma equiv_rel_R : equivalence_rel R.
  Proof.
    rewrite /equivalence_rel => x y z.
(**
ゴールは、MathComp の表記で次のようになります：

```z ~ z * (x ~ y -> x ~ z = y ~ z)```

``*`` は、prod の意味で、Type型のふたつの直積です。
（これに対して、お馴染みの ``/\`` は、andの意味で、Prod型のふたつの直積を示します。）
ここではおなじことといってよいと思います。

また、``=``は、boolの値がおなじことを示す``=``で、論理式としての必要十分条件を示します。
以上を論理式として書くと、次の様になります：
 *)
(**
Goal: $$ z \sim z \land (x \sim y\ \to (x\ \sim z \iff y \sim z)) $$
*)
(**
``*`` は直積(prod)の意味であるので、pair を適用することで、
``*`` の左と右のふたつのゴールに分けられます。（``/\`` における split とおなじです。）
*)
    apply: pair => /=.
(**
Goal: $$ z z^{-1} \in H $$
*)
    - by rewrite mulgV group1.
(**
Goal: $$ x y^{-1} \in H -> (x z^{-1} \in H \iff y z^{-1} \in H) $$
*)
    - move=> xRinvy.
      apply/idP/idP.
      + move/groupVr in xRinvy.
        (* [x in H -> y in H -> x * y in H] の [x in H] を指定する必要がある。 *)
        (* 直前の行とまとめて [move/(groupM (groupVr xRinvy))] とできる。 *)

        Check groupM xRinvy : x * z^-1 \in H -> (x * y^-1)^-1 * (x * z^-1) \in H.
        move/(groupM xRinvy).
          by rewrite invMg invgK mulgA -(mulgA y) mulVg mulg1.

      + Check (groupM xRinvy) : y * z^-1 \in H -> x * y^-1 * (y * z^-1) \in H.
        move/(groupM xRinvy).
          by rewrite mulgA -(mulgA x) mulVg mulg1.
  Qed.
  
(**
# 6.2.3 剰余類の性質の形式化
*)
(**
## 定理：

$$H x = \\{y \in G\ |\ x \sim y \\}$$
*)
  Lemma coset_equiv_class (x : gT) (xinG : x \in G) : H :* x = [set y in G | x ~ y].
  Proof.
    apply/setP => /= y.
    rewrite inE.
    apply/idP/idP.
    - case/rcosetP => z zinH -> {y}.
      apply/andP.
      apply: conj.
      + Check groupM.
        rewrite groupM //.
        move/subsetP : HG => HG'.
        Check (HG' z zinH).
          by move: (HG' z zinH).
      + by rewrite invMg mulgA mulgV mul1g groupV.
    - case/andP => yinG xinvyinH.
      apply/rcosetP.
      (* プレースホルダーを埋めると次になる。 *)
      Check (ex_intro2 (fun g => g \in H)
                       (fun a => y = a * x)
                       (y * x^-1)) :
        y * x^-1 \in H -> y = y * x^-1 * x ->
                     ex2 (fun g : gT => g \in H) (fun a : gT => y = a * x).
      (* ゴールは、 exists2 a : gT, a \in H & y = a * x のデシュガ *)
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

MathComp では、``#|_ : _|``というNotationです。
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
*)
  Check partition_rcosets : partition (rcosets H G) G.

(**
組み合わせると、剰余類の集合の要素の濃度の総和は、群$G$の濃度に等しい、となります。
これは、剰余類の集合の集合は、群$G$の分割であるためですね。

$|G| = \sum_(A \in H \backslash G)\ |A|$
*)
  Check (card_partition partition_rcosets)
    : #|G| = \sum_(A in rcosets H G) #|A|.

(**
## 使用する補題 ``eq_bigr``

myCard_rcoset の $|A| = |H|$ を Σの中に適用して書き換える補題です。

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

(* END *)
