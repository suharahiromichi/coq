(**
コンピュータの数学 4.6 合同関係 の公式の証明（自然数版）
======

2020_10_24 @suharahiromichi
 *)

From mathcomp Require Import all_ssreflect.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section Modulo.
(**
コンピュータの数学[1][2]の 4.6 合同関係 の公式の証明をしてみます。
ただし、被除数と除数は自然数に限定します。
また、式の番号は[2]にあわせ、「」の中は[2]からの引用です。

このソースコードは、以下にあります。

https://github.com/suharahiromichi/coq/blob/master/gkp/gkp_4.6_modulo.v


変数名 m n p q d d1 d2 の使い方は、MathComp の div.v [3] 
にあわせて、被除数を``m``と``n``、除数を``d``としています。
これは、[1][2]とは異なるので注意してください。
*)
  
(**
# 合同式の加算

「合同な要素を足しても、合同関係は崩れない。」

$$ m = n \pmod{d} \Longrightarrow 
   p = q \pmod{d} \Longrightarrow 
   m + p = n + q \pmod{d} $$
 *)  
  Lemma m_addn m n p q d  :
    m = n %[mod d] -> p = q %[mod d] -> m + p = n + q %[mod d].
  Proof.
    move=> Hmp Hnd.
    Check modnDm : forall m n d : nat, m %% d + n %% d = m + n %[mod d].
    rewrite -[LHS]modnDm -[RHS]modnDm.
    (* m %% d + p %% d = n %% d + q %% d %[mod d] *)
    
    congr (_ %% _).            (* %[mod d] を外す。 *)
    (* m %% d + p %% d = n %% d + q %% d *)
    
    congr (_ + _).
    (* m %%d = n %% d *)
    - done.
    (* p %%d = q %% d *)
    - done.
  Qed.
  
(**
# 合同式の乗算

「掛け算もうまくいく。」

$$ m = n \pmod{d} \Longrightarrow 
   p = q \pmod{d} \Longrightarrow 
   m p = n q \pmod{d} $$
 *)  
  Lemma m_muln m n p q d  :
    m = n %[mod d] -> p = q %[mod d] -> m * p = n * q %[mod d].
  Proof.
    move=> Hmp Hnd.
    Check modnMm : forall m n d : nat, m %% d * (n %% d) = m * n %[mod d].
    rewrite -[LHS]modnMm -[RHS]modnMm.
    
    congr (_ %% _). (* %[mod d] を外す。 *)
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
# 合同式のべき乗

「掛け算の性質を繰り返し適用すると、べき乗することもできる。」

$$ p = q \pmod{d} \Longrightarrow p^{m} = q^{m} \pmod{d} $$
 *)  
  Lemma m_exprn p q m d :
    p = q %[mod d] -> p^m = q^m %[mod d].
  Proof.
    move=> Hpq.
    Check modnXm : forall m d p : nat, (p %% d) ^ m = p ^ m %[mod d].
    rewrite -[LHS]modnXm -[RHS]modnXm.
    
    congr (_ %% _).
      (* Goal : (p %% d) ^ m = (q %% d) ^ m *)
      by congr (_ ^ _).
  Qed.
  
(**
# 合同式の除算（式(4.37)）

「(p と d が)互いに素の場合には、(dを法とする)合同関係のもとでも(pによる)割り算ができる。」

$$ m p = n p \pmod{d} \Longleftrightarrow m = n \pmod{d}, 但し p \perp d $$

説明：まず、[1]の式(4.37) の→を証明します。
拡張したGCDを使用するので [3] の chinese_modl 補題の証明、および、
その解説の [4] も参考にしてください。
 *)  
  Lemma m_divn_d_1 m n p d :
    coprime p d -> m * p = n * p %[mod d] -> m = n %[mod d].
  Proof.
    rewrite /coprime => /eqP.               (* 前提を gcdn p d = 1 *)
    
    (* p = 0 と 0 < p に場合分けする。 *)
    case: (posnP p).
    
    (* p = 0 の場合 *)
    - move=> ->.                            (* p = 0 で書き換える。 *)
      rewrite gcd0n.                        (* 前提から d = 1 でもある。 *)
      move=> ->.                            (* d = 1 で書き換える。 *)
        by rewrite !modn1.
        
    (* 0 < p の場合 *)
    - move=> p_gt0 Hco.     (* 0 < p 条件と、coprime条件を intro する。 *)
      
      Check @egcdnP p d p_gt0 : egcdn_spec p d (egcdn p d).
      case: (@egcdnP p d p_gt0). (* 拡張ユーグリッドの互除法の定義を前提に積む。 *)
      (* egcdn_spec は inductive に定義されているので、条件がひとつでも case が要る。 *)
      (* km * p = kn * d + gcdn p d と kn * gcdn p d < p *)
      
      move=> p' d' Hdef _ H.
      rewrite Hco in Hdef.
      (* ``Hdef : p' * p = d' * d + 1`` は不定方程式を展開した状態である。 *)
    
      (* H の 両辺に p' をかける。 p' が p の逆数のような働きをする。 *)
      Check @m_muln' (m * p) (n * p) p' d
        : m * p = n * p %[mod d] -> m * p * p' = n * p * p' %[mod d].
      move/(@m_muln' (m * p) (n * p) p' d) in H.
      
      (* 不定方程式 ``Hdef`` を H に代入して整理する。 *)
      rewrite -2!mulnA -[p * p']mulnC in H.
      rewrite Hdef in H.
      rewrite 2!mulnDr 2!muln1 2!mulnA 2!modnMDl in H.
      done.
  Qed.
  
(**
[1]の式(4.37) の←は、掛け算の合同の公式から明らかなので、<->が証明できます。
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
# 合同式の除算（式(4.38)、法を割る）

「合同関係で割り算をするもうひとつの方法は、法とする自身も他の数と同じように割ることである。
これは、modの分配則だけに依存している。」

$$ m d_1 = n d_1 \pmod{d_2 d_1} \Longleftrightarrow m = n \pmod{d_2}, 但し 0 \lt d_1 $$
 *)  
  Lemma m_divn_dp m n d1 d2 :
    0 < d1 -> (m * d1 == n * d1 %[mod d2 * d1]) = (m == n %[mod d2]).
  Proof.
    move=> Hd1.
    rewrite -[RHS](eqn_pmul2r Hd1). (* 右辺の両辺にd1を掛ける。d1≠0なので可能である。 *)
    
    (* d1による）剰余の分配則を適用する。これも d1≠0なので可能である。 *)
    Check @muln_modl d1 : forall m d : nat, 0 < d1 -> m %% d * d1 = (m * d1) %% (d * d1).
      by rewrite 2!(muln_modl Hd1).
  Qed.
  
(**
# 最大公約数を法とする合同式（式(4.41)）

$$ m = n \pmod{lcm(d_1,d_2)} \Longleftrightarrow \\
   m = n \pmod{d_1} \ かつ\ m = n \pmod{d_2} $$

説明：まず、最大公約数とdivisibleの関係を使いやすい2つの補題にしておきます。
 *)
  Lemma lcmn_dvdn d1 d2 m : lcmn d1 d2 %| m -> d1 %| m.
  Proof.
    Check dvdn_lcm d1 d2 m : (lcmn d1 d2 %| m) = (d1 %| m) && (d2 %| m).
    rewrite dvdn_lcm => /andP.
      by case.
  Qed.
  
  Lemma dvdn_lcmn d1 d2 m : d1 %| m -> d2 %| m -> lcmn d1 d2 %| m.
  Proof.
    rewrite dvdn_lcm => H1 H2.
    apply/andP.
      by split.
  Qed.
  
(**
次いで、式(4.41)の→の共通部分です。
*)
  Lemma m_divn_lcmn_1_1_1 m n d1 d2 :
    n <= m -> m = n %[mod lcmn d1 d2] -> m = n %[mod d1].
  Proof.
    Check eqn_mod_dvd
      : forall d m n : nat, n <= m -> (m == n %[mod d]) = (d %| m - n).
    
    move=> Hnm /eqP H.
    rewrite eqn_mod_dvd in H; last done.
    move/lcmn_dvdn in H.
    
    apply/eqP.
    rewrite eqn_mod_dvd; last done.
    done.
  Qed.
  
(**
式(4.41)の→の補題で、証明の中核となる部分です。
場合分けしてそれぞれに共通部分を適用します。
*)
  Lemma m_divn_lcm_1_1 m n d1 d2 :
    m = n %[mod lcmn d1 d2] -> m = n %[mod d1].
  Proof.
    move=> H.
    Check (leq_total m n) : (m <= n) || (n <= m).
    case/orP: (leq_total n m) => Hnm.
    
    (* n <= m である場合 *)
    - by apply: m_divn_lcmn_1_1_1 H.
      
    (* m <= n である場合 *)
    - apply/esym.               (* 合同式の左辺と右辺を入れ替える。 *)
      move/esym in H.           (* 合同式の左辺と右辺を入れ替える。 *)
        by apply: m_divn_lcmn_1_1_1 H.
  Qed.
  
(**
式(4.41)の→の証明です。
*)  
  Lemma m_divn_lcm_1 m n d1 d2 :
    m = n %[mod lcmn d1 d2] -> m = n %[mod d1] /\ m = n %[mod d2].
  Proof.
    split.
    Check @m_divn_lcm_1_1 m n d1 d2 : m = n %[mod lcmn d1 d2] -> m = n %[mod d1].
    - by apply: m_divn_lcm_1_1 H.
    - rewrite lcmnC in H.
        by apply: m_divn_lcm_1_1 H.
  Qed.

(**
式(4.41)の←の補題です。
*)
  Lemma m_divn_lcm_2_1 m n d1 d2 :
    n <= m -> m = n %[mod d1] -> m = n %[mod d2] -> m = n %[mod lcmn d1 d2].
  Proof.
    move=> Hnm /eqP H1 /eqP H2.
    rewrite eqn_mod_dvd in H1; last done.
    rewrite eqn_mod_dvd in H2; last done.
    
    apply/eqP.
    rewrite eqn_mod_dvd; last done.
    
    Check dvdn_lcmn : forall d1 d2 m : nat, d1 %| m -> d2 %| m -> lcmn d1 d2 %| m.
      by apply: dvdn_lcmn.
  Qed.
  
(**
式(4.41)の←の証明です。
*)  
  Lemma m_divn_lcm_2 m n d1 d2 :
    m = n %[mod d1] -> m = n %[mod d2] -> m = n %[mod lcmn d1 d2].
  Proof.
    move=> H1 H2.
    case/orP: (leq_total n m) => Hnm.
    (* n <= m の場合 *)
    - by apply: m_divn_lcm_2_1.       (* 先の補題がそのまま使える。 *)
      
    (* m < n の場合 *)      
    - apply/esym. (* ゴールと条件の合同式の左辺と右辺を入れ替える。 *)
      move/esym in H1.
      move/esym in H2.
        by apply: m_divn_lcm_2_1.     (* 先の補題が使えるようになった。 *)
  Qed.
  
(**
式(4.41)の証明です。MathComp風に、bool値の同値の式としました。
*)  
  Lemma m_divn_lcm m n d1 d2 :
    (m == n %[mod lcmn d1 d2]) = (m == n %[mod d1]) && (m == n %[mod d2]).
  Proof.
    apply/idP/idP => [/eqP H | /andP [/eqP H1 /eqP H2]].
    - move/m_divn_lcm_1 in H.
      case: H => [H1 H2].
        by apply/andP; split; apply/eqP.
    - apply/eqP.
        by apply: m_divn_lcm_2.
  Qed.
  
(**
# 中国人の剰余定理の特別な場合（式(4.42)）

d1 と d2 が互いに素のとき、ある数を``d1 * d2``で割って余る数と、d1で割って
余る数と、d2で割って余る数が同じであることを証明します。

$$ m = n \pmod{d_1 d_2} \Longleftrightarrow \\
   m = n \pmod{d_1}\ かつ\ m = n \pmod{d_2}, 但し d_1 \perp d_2 $$

中国人の剰余定理の一般の場合は、これらの剰余が異なっていても成立するので、
その特別な場合であるといえます。``div.v`` の補題 ``chinese_remainder`` と同内容です。
*)

(**
説明：まず補題として、互いに素ならLCMは積であることを証明します。
補題 ``muln_lcm_gcd m n : lcmn m n * gcdn m n = m * n`` を使います。
m と n が互いに素であることから、``gcdn m n = 1`` を代入して gcdn を消します。
*)  
  Lemma coprime_lcm d1 d2 : coprime d1 d2 -> lcmn d1 d2 = d1 * d2.
  Proof.
    rewrite /coprime.
    move=> /eqP Hco.
    Check muln_lcm_gcd : forall m n : nat, lcmn m n * gcdn m n = m * n.
      by rewrite -muln_lcm_gcd Hco muln1.
  Qed.
  
(**
この補題と式(4.41)から、ただちに求められます。
*)  
  Lemma m_chinese_remainder m n d1 d2 :
    coprime d1 d2 ->
    (m == n %[mod d1 * d2]) = (m == n %[mod d1]) && (m == n %[mod d2]).        
  Proof.
    move=> Hco.
    rewrite -coprime_lcm; last done.
      by apply: m_divn_lcm.
  Qed.
  
(**
@morita_hm さんによる別の証明（なお、一部修正しました）。

eqn_mod_dvd を使って、合同式を整除可能に書き換えたあと、
Gauss_dvd を使って、整除可能の * と && の同値関係で証明をします。
Gauss_dvd の証明には mulm_lcm_gcd を使っています(div.vにて)。

なお、eqn_mod_dvd を使うために ``(m <= n)`` と ``(n <= m)`` の場合分けしています。
これは、前提によらす使用することができますので、覚えておくと便利です。


補足説明：bool式の真偽での場合分け ``case H : (m <= n)`` では、``(m <= n)`` と ``(n < m)``
となり、後者の条件を ``(n <= m)`` に書き換えるには補題 ltnW が必要になります。
*)
  Check eqn_mod_dvd
    : forall d m n : nat, n <= m -> (m == n %[mod d]) = (d %| m - n).
  
  Check Gauss_dvd
    : forall d1 d2 p : nat, coprime d1 d2 -> (d1 * d2 %| p) = (d1 %| p) && (d2 %| p).
  
  Lemma chinese_remainder_lite : forall d1 d2 m n : nat,
      coprime d1 d2 ->
      (m == n %[mod d1 * d2]) = (m == n %[mod d1]) && (m == n %[mod d2]).
  Proof.
    move=> d1 d2 m n co_mn.
    case/orP: (leq_total m n) => geq_mn. (* || を && にリフレクトして場合分けする。 *)
    
    - (* (m <= n) の場合 *)
      rewrite ![m == n %[mod _]]eq_sym.     (* 右辺と左辺を入れ替える。 *)
      rewrite !eqn_mod_dvd //.
        by rewrite Gauss_dvd.
        
    - (* (n <= m) の場合*)
      rewrite !eqn_mod_dvd //.
        by rewrite Gauss_dvd.
  Qed.
  
(**
中国人の剰余定理の一般的な場合の証明は、``div.v`` の ``chinese_mod`` を参照してください。
 *)
End Modulo.

(**
# 文献


[1] Graham, Knuth, Patashnik "Concrete Mathematics", Second Edition, A.W.


[2] 有澤、安村、萩野、石畑訳、「コンピュータの数学」共立出版


[3] math-comp/mathcomp/ssreflect/div.v

https://github.com/math-comp/math-comp/blob/master/mathcomp/ssreflect/div.v


[4] 中国人の剰余定理

https://qiita.com/suharahiromichi/items/1a135d9648a0f55f020a

 *)

(* END *)
