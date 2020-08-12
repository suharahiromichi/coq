(**
Coq/SSReflect/MathComp による定理証明

第4章 MathComp ライブラリの基本ファイル

追加 4.A div.v --- 除算のライブラリ

======

2020_8_10 @suharahiromichi
 *)

From mathcomp Require Import all_ssreflect.
Require Import ssromega.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(**
# はじめに

本節はテキストを参照しながら、MathComp のソースコードに沿って説明していきます。
ソースコードが手元にあるならば、それも参照してください。
opamでインストールしている場合は、ソースは、たとえば以下にあります。

~/.opam/4.07.1/lib/coq/user-contrib/mathcomp/ssreflect/div.v
*)

Section Modulo.

(**
## Concrete Mathematics [1] （コンピュータの数学 [2]） 4.6 合同関係 の公式

変数名 m n p q d d1 d2 の使い方は、MathComp の div.v [3] にあわせています。
*)
  
(**
### 合同式の加算

「合同な要素を足しても、合同関係は崩れない。」


なお、引き算の場合については、あとで補足します。
 *)  
  Lemma m_addn m n p q d  :
    m = n %[mod d] -> p = q %[mod d] -> m + p = n + q %[mod d].
  Proof.
    move=> Hmp Hnd.
    Check modnDm
      : forall m n d : nat, m %% d + n %% d = m + n %[mod d].
    rewrite -[LHS]modnDm -[RHS]modnDm.
    congr (_ %% _).
    (* 前提からは、より一般的な定理が導けるわけである。 *)
    (* Goal : m %% d + p %% d = n %% d + q %% d *)
    congr (_ + _).
    - done.
    - done.
  Qed.

(**
### 合同式の乗算

「掛け算もうまくいく。」
 *)  
  Lemma m_muln m n p q d  :
    m = n %[mod d] -> p = q %[mod d] -> m * p = n * q %[mod d].
  Proof.
    move=> Hmp Hnd.
    Search _ ((_ * _) %% _).
    Check modnMm
      : forall m n d : nat, m %% d * (n %% d) = m * n %[mod d].
    rewrite -[LHS]modnMm -[RHS]modnMm.
    congr (_ %% _).
      (* Goal : m %% d * (p %% d) = n %% d * (q %% d) *)
      by congr (_ * _).
  Qed.
  
(**
``p = q`` である特別な場合について証明しておきます。後で使います。
 *)
  Lemma m_muln' m n p d  :
    m = n %[mod d] -> m * p = n * p %[mod d].
  Proof.
    move=> H.
      by apply: m_muln.
  Qed.
  
(**
### 合同式のべき乗

「掛け算の性質を繰り返し適用すると、べき乗することもできる。」
 *)  
  Lemma m_exprn p q m d :
    p = q %[mod d] -> p^m = q^m %[mod d].
  Proof.
    move=> Hpq.
    Search _ (_ ^ _ %% _).
    Check modnXm
      : forall m d p : nat, (p %% d) ^ m = p ^ m %[mod d].
    rewrite -[LHS]modnXm -[RHS]modnXm.
    congr (_ %% _).
      (* Goal : (p %% d) ^ m = (q %% d) ^ m *)
      by congr (_ ^ m).
  Qed.
  
(**
### 合同式の除算（式(4.37)）

p と d が「互いに素の場合には、合同関係のもとでも割り算ができる。」


説明：まず、[1]の式(4.37) の→を証明します。
拡張したGCDを使用するので [3] の chinese_modl 補題の証明、および、
その解説の [4] も参考にしてください。
 *)  
  Lemma m_divn_d_1 m n p d :
    coprime p d -> m * p = n * p %[mod d] -> m = n %[mod d].
  Proof.
    move/eqP.                                 (* gcdn p d = 1 *)
    (* p = 0 と 0 < p に場合分けする。 *)
    case: (posnP p).
    
    (* p = 0 の場合、d = 1 でもある。 *)
    - move=> ->.                            (* p = 0 で書き換える。 *)
      rewrite gcd0n.
      move=> ->.                            (* d = 1 で書き換える。 *)
        by rewrite !modn1.
        
    (* 0 < p の場合 *)
  - move=> p_gt0 Hco.       (* 0 < p 条件と、coprime条件をpopする。 *)
    case: (@egcdnP p d p_gt0).
    rewrite Hco.
    move=> p' d' Hdef _ H.
    (* 不定方程式 ``Hdef : p' * p = d' * d + 1`` を展開した状態である。 *)
    
    (* H の 両辺に p' をかける。 p' が ``1 / p`` のような働きをする。 *)
    Check @m_muln' (m * p) (n * p) p' d
      : m * p = n * p %[mod d] -> m * p * p' = n * p * p' %[mod d].
    move/(@m_muln' (m * p) (n * p) p' d) in H.
    
    (* 不定方程式 ``Hdef`` を H に代入して整理する。  *)
    rewrite -2!mulnA -[p * p']mulnC in H.
    rewrite Hdef in H.
      by rewrite 2!mulnDr 2!muln1 2!mulnA 2!modnMDl in H.
  Qed.
  
(**
[1]の式(4.37) の←は、掛け算の合同の公式から明らかです。
*)
  Lemma m_divn_d' m n p d :
    coprime p d -> (m * p = n * p %[mod d] <-> m = n %[mod d]).
  Proof.
    move=> Hco.
    split.
    - by apply: m_divn_d_1.                 (* -> *)
    - by apply: m_muln'.                    (* <- *)
  Qed.

(**
MathCompらしく、bool値の同値で証明しておきます。
 *)
  Lemma m_divn_d m n p d :
    coprime p d -> (m * p == n * p %[mod d]) = (m == n %[mod d]).
  Proof.
    move=> Hco.
    apply/idP/idP; move/eqP => H; apply/eqP.
    - by apply: (@m_divn_d_1 _ _ p _).      (* -> *)
    - by apply: m_muln'.                    (* <- *)
  Qed.

(**
### 合同式の除算（式(4.38)、法を割る）

「合同関係で割り算をするもうひとつの方法は、
法とする自身も他の数と同じように割ることである。。。。
これは、modの分配則だけに依存している。」
 *)  
  Lemma m_divn_dp m n d1 d2 :
    0 < d1 -> (m * d1 == n * d1 %[mod d2 * d1]) = (m == n %[mod d2]).
  Proof.
    move=> Hd1.
    rewrite -[RHS](eqn_pmul2r Hd1).
    rewrite 2!(muln_modl Hd1).
    done.
  Qed.

(**
### 最大公約数を法とする合同式（式(4.41)）

説明：まず、最大公約数とdivisibleの関係を使いやすい補題にしておきます。
 *)
  Check dvdn_lcm
    : forall d1 d2 m : nat, (lcmn d1 d2 %| m) = (d1 %| m) && (d2 %| m).
  
  Lemma lcmn_dvdn d1 d2 m : lcmn d1 d2 %| m -> d1 %| m.
  Proof.
    Check dvdn_lcm d1 d2 m.
    rewrite dvdn_lcm => /andP.
      by case.
  Qed.

  Lemma dvdn_lcmn d1 d2 m : d1 %| m -> d2 %| m -> lcmn d1 d2 %| m.
  Proof.
    Check dvdn_lcm d1 d2 m.
    rewrite dvdn_lcm => H1 H2.
    apply/andP.
      by split.
  Qed.
  
(**
``eqn_mod_dvd : (m == n %[mod d]) = (d %| (m - n))`` の補題を使って証明する都合上、
` ``n <= m`` と m < n`` で場合分けします。このとき、
後者の条件を ``m <= n`` に変形することで、場合分け後の証明を共通にすることができます。
その変形をする補題を証明しておきます。
*)
  Lemma le_m_n m n : (n <= m) = false -> m <= n.
  Proof.
    move=> Hmn.
      by ssromega.
  Qed.
  
(**
式(4.41)の→の共通部分です。
*)
  Lemma m_divn_lcmn_1_1_1 m n d1 d2 :
    n <= m -> m = n %[mod lcmn d1 d2] -> m = n %[mod d1].
  Proof.
    move=> Hnm H.
    apply/eqP.
    Check eqn_mod_dvd
      : forall d m n : nat, n <= m -> (m == n %[mod d]) = (d %| m - n).
    rewrite eqn_mod_dvd; last done.
    move/eqP in H.
      rewrite eqn_mod_dvd in H; last done.
        by move/lcmn_dvdn in H.
  Qed.

(**
証明の中核となる部分です。場合分けしてそれぞれに共通部分を適用します。
*)
  Lemma m_divn_lcm_1_1 m n d1 d2 :
    m = n %[mod lcmn d1 d2] -> m = n %[mod d1].
  Proof.
    move=> H.
    case Hnm : (n <= m).
    (* n <= m である場合 *)
    - by apply: m_divn_lcmn_1_1_1 H.
      
    (* m <= n である場合 *)
    - move/le_m_n in Hnm.       (* n > m を m <= n にする。 *)
      apply/esym.               (* 合同式の左辺と右辺を入れ替える。 *)
      move/esym in H.           (* 合同式の左辺と右辺を入れ替える。 *)
        by apply: m_divn_lcmn_1_1_1 H.
  Qed.
  
(**
式(4.41)の→の証明です。（ここでは、使用していません）
*)  
  Lemma m_divn_lcm_1 m n d1 d2 :
    m = n %[mod lcmn d1 d2] -> m = n %[mod d1] /\ m = n %[mod d2].
  Proof.
    split.
    Check @m_divn_lcm_1_1 m n d1 d2.
    - by apply: m_divn_lcm_1_1 H.
    - rewrite lcmnC in H.
        by apply: m_divn_lcm_1_1 H.
  Qed.


(**
式(4.41)の→の共通部分です。
*)
  Lemma m_divn_lcm_2_1 m n d1 d2 :
    n <= m -> m = n %[mod d1] -> m = n %[mod d2] -> m = n %[mod lcmn d1 d2].
  Proof.
    move=> Hnm H1 H2.
    apply/eqP.
    rewrite eqn_mod_dvd; last done.
    move/eqP in H1.
    move/eqP in H2.
    rewrite eqn_mod_dvd in H1; last done.
    rewrite eqn_mod_dvd in H2; last done.
      by apply: dvdn_lcmn.
  Qed.
  
(**
式(4.41)の←の証明です。
*)  
  Lemma m_divn_lcm_2 m n d1 d2 :
    m = n %[mod d1] -> m = n %[mod d2] -> m = n %[mod lcmn d1 d2].
  Proof.
    move=> H1 H2.
    case Hnm : (n <= m).
    - by apply: m_divn_lcm_2_1.
    - move/le_m_n in Hnm.       (* n > m を m <= n にする。 *)
      apply/esym.               (* 合同式の左辺と右辺を入れ替える。 *)
      move/esym in H1.          (* 合同式の左辺と右辺を入れ替える。 *)
      move/esym in H2.          (* 合同式の左辺と右辺を入れ替える。 *)
        by apply: m_divn_lcm_2_1.
  Qed.
  
(**
式(4.41)の証明です。MathComp風に、bool値の同値の式としました。
*)  
  Lemma m_divn_lcm m n d1 d2 :
    (m == n %[mod lcmn d1 d2]) = (m == n %[mod d1]) && (m == n %[mod d2]).
  Proof.
    apply/idP/idP => [/eqP H | /andP [/eqP H1 /eqP H2]].
    - apply/andP; split; apply/eqP.
      + by apply: m_divn_lcm_1_1 H.
      + rewrite lcmnC in H.
          by apply: m_divn_lcm_1_1 H.
    - apply/eqP.
        by apply: m_divn_lcm_2.
  Qed.

(**
### 中国人の剰余定理の特別な場合（式(4.42)）

説明： 互いに素なら、LCMは積であることを証明します。
補題 ``muln_lcm_gcd m n : lcmn m n * gcdn m n = m * n`` を使います。
*)  
  Lemma coprime_lcm d1 d2 : coprime d1 d2 -> lcmn d1 d2 = d1 * d2.
  Proof.
    rewrite /coprime.
    move=> /eqP Hco.
    Check muln_lcm_gcd :
      forall m n : nat, lcmn m n * gcdn m n = m * n.
      by rewrite -muln_lcm_gcd Hco muln1.
  Qed.

(**
その補題を使用すれば、式(4.41)からただちに求められます。
これは、中国人の剰余定理の特別な場合です。
より一般的な証明は、``div.v`` を参照してください。
*)  
  Lemma m_chinese_remainder m n d1 d2 :
    coprime d1 d2 ->
    (m == n %[mod d1 * d2]) = (m == n %[mod d1]) && (m == n %[mod d2]).        
  Proof.
    move=> Hco.
    rewrite -coprime_lcm; last done.
      by apply: m_divn_lcm.
  Qed.
  
End Modulo.

(**
[1] Graham, Knuth, Patashnik "Concrete Mathematics", Second Edition, A.W.


[2] 有澤、安村、萩野、石畑訳、「コンピュータの数学」共立出版


[3] math-comp/mathcomp/ssreflect/div.v

https://github.com/math-comp/math-comp/blob/master/mathcomp/ssreflect/div.v


[4] 中国人の剰余定理

https://qiita.com/suharahiromichi/items/1a135d9648a0f55f020a

 *)

(* END *)
