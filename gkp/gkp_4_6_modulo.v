(**
「コンピュータの数学」合同関係の公式の証明（自然数版）
======

2020_10_24 @suharahiromichi
 *)

From mathcomp Require Import all_ssreflect.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section Modulo.
(**
Knuth先生の「コンピュータの数学」[1][2] の「4.6 合同関係」に掲載されているの公式の証明をしてみます。
ただし、被除数と除数は自然数に限定します。
また、式の番号は[2]にあわせ、「」の中は[2]からの引用です。

このソースコードは、以下にあります。

https://github.com/suharahiromichi/coq/blob/master/gkp/gkp_4_6_modulo.v


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
    
    congr (_ %% d).            (* %[mod d] を外す。 *)
    (* m %% d + p %% d = n %% d + q %% d *)
    
    congr (_ + _).
    (* m %%d = n %% d *)
    - done.
    (* p %%d = q %% d *)
    - done.
  Qed.
  
(**
``p = q`` である特別な場合について証明しておきます。後で使います。
 *)
  Lemma m_addn' m n p d  :
    m = n %[mod d] -> m + p = n + p %[mod d].
  Proof.
    move=> H.
    by apply: m_addn.
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
    Check modnMm : forall m n d : nat, (m %% d) * (n %% d) = m * n %[mod d].
    rewrite -[LHS]modnMm -[RHS]modnMm.
    
    congr (_ %% d).            (* %[mod d] を外す。 *)
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
まとめて、線形性が成り立ちます。
*)
  Lemma m_linear m1 n1 m2 n2 p q d  :
    m1 = n1 %[mod d] ->
    m2 = n2 %[mod d] -> 
    m1 * p + m2 * q = n1 * p + n2 * q %[mod d].
  Proof.
    move=> H1 H2.
    by apply: m_addn; apply: m_muln'.
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
    
    congr (_ %% d).           (* %[mod d] を外す。 *)
    (* Goal : (p %% d) ^ m = (q %% d) ^ m *)
    by congr (_ ^ m).
  Qed.
  
(**
# 合同式の除算（式(4.37)）

「(p と d が)互いに素の場合には、(dを法とする)合同関係のもとでも(pによる)割り算ができる。」

$$ m p = n p \pmod{d} \Longleftrightarrow m = n \pmod{d}, 但し p \perp d $$
*)

(**
あらかじめ補題として、p と d が互いに素のときに、
不定方程式 ``p * p' = d * d' + 1`` に解があることを補題として証明します。
[4]も参照してください。
*)
  Lemma solve_indeterminate_equation (p d : nat) :
    0 < p -> coprime p d ->
    exists (p' d' : nat), p' * p = d' * d + 1.
  Proof.
    rewrite /coprime.
    move=> p_gt0 /eqP Hco.
    
    Check @egcdnP p d p_gt0 : egcdn_spec p d (egcdn p d).
    case: (@egcdnP p d p_gt0). (* 拡張ユーグリッドの互除法の定義を前提に積む。 *)
    (* egcdn_spec は inductive に定義されているので、条件がひとつでも case が要る。 *)
    (* km * p = kn * d + gcdn p d と kn * gcdn p d < p *)
    
    move=> p' d' Hdef _.
    exists p', d'.
    rewrite Hco in Hdef.
    done.
  Qed.
  
(**
説明：[1]の式(4.37) の→を証明します。
 *)  
  Lemma m_divn_d_1 m n p d :
    coprime p d -> m * p = n * p %[mod d] -> m = n %[mod d].
  Proof.
    (* p = 0 と 0 < p に場合分けする。 *)
    case: (posnP p).
    
    (* p = 0 の場合 *)
    - move=> ->.                       (* p = 0 で書き換える。 *)
      rewrite /coprime => /eqP.        (* 前提を gcdn p d = 1 *)
      rewrite gcd0n.                   (* 前提から d = 1 でもある。 *)
      move=> ->.                       (* d = 1 で書き換える。 *)
      by rewrite !modn1.
        
    (* 0 < p の場合 *)
    - move=> p_gt0 Hco H.
      (* 補題を使って、不定方程式の解を p' と d' とします。 *)
      move: (solve_indeterminate_equation p_gt0 Hco) => [p' [d' Hdef]].
      
      (* H の 両辺に p' をかける。 *)
      Check @m_muln' (m * p) (n * p) p' d
        : m * p = n * p %[mod d] -> m * p * p' = n * p * p' %[mod d].
      move/(@m_muln' (m * p) (n * p) p' d) in H.
      (* ``H : m * p * p' = n * p * p' %[mod d]`` *)
      
      (* 不定方程式 Hdef を H に代入して整理する。 *)
      rewrite -2!mulnA -[p * p']mulnC in H.
      rewrite Hdef in H.
      (* p' が p の逆数のような働きをする。 *)
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
    
    (* 右側の両辺に、d1を掛ける。 d1≠0なので可能である。 *)
    Check @eqn_pmul2r d1 m n Hd1 : (m * d1 == n * d1) = (m == n).
    rewrite -[RHS](eqn_pmul2r Hd1).

    (* 右側： (m %% d2 * d1 == n %% d2 * d1) *)
    
    (* 右側の両辺に、d1による剰余の分配則を適用する。これも d1≠0なので可能である。 *)
    Check @muln_modl d1 :
      forall m d : nat, 0 < d1 -> (m %% d) * d1 = (m * d1) %% (d * d1).
    
    rewrite 2!(muln_modl Hd1). (* MathCompの最新版で条件 0 < p 条件が削除されている。 *)
    done.
  Qed.
  
(**
# 最小公倍数LCMを法とする合同式（式(4.41)）

$$ m = n \pmod{lcm(d_1,d_2)} \Longleftrightarrow \\
   m = n \pmod{d_1} \ かつ\ m = n \pmod{d_2} $$

説明：最小公倍数LCMとdivisibleの関係、ふたつの自然数d1とd2の両方で割りきれることと、
その最小公倍数でも割りきれることは同値です。このこをとを使いやすい補題にしておきます。
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
次いで、式(4.41)の→の共通部分です。d1とd2の最小公倍数を法として合同なら、
d1を法として合同です。一般性を失わずに ``m ≦ n`` としています。
*)
  Lemma m_divn_lcmn_1_1_1 m n d1 d2 :
    n <= m -> m = n %[mod lcmn d1 d2] -> m = n %[mod d1].
  Proof.
    Check eqn_mod_dvd : forall d m n : nat, n <= m -> (m == n %[mod d]) = (d %| m - n).
    
    move=> Hnm /eqP H.
    rewrite eqn_mod_dvd in H; last done.
    move/lcmn_dvdn in H.
    (* ``H : d1 %| m - n`` *)
    
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
式(4.41)の←の補題です。d1とd2を法として合同なら、d1とd2の最小公倍数を法として合同です。
一般性を失わずに ``n ≦ m`` としています。
*)
  Lemma m_divn_lcm_2_1 m n d1 d2 :
    n <= m -> m = n %[mod d1] -> m = n %[mod d2] -> m = n %[mod lcmn d1 d2].
  Proof.
    move=> Hnm /eqP H1 /eqP H2.
    apply/eqP.
    
    rewrite eqn_mod_dvd in H1; last done.
    rewrite eqn_mod_dvd in H2; last done.
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
      
    (* m <= n の場合 *)      
    - apply/esym. (* ゴールと条件の合同式の左辺と右辺を入れ替える。 *)
      move/esym in H1.
      move/esym in H2.
      by apply: m_divn_lcm_2_1.   (* 先の補題が使えるようになった。 *)
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
説明：まず補題として、互いに素なら最小公倍数LCMは積であることを証明します。
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
証明したい定理は、補題 coprime_lcm で左側の法の積を lcm に書き換え、
式(4.41) m_divn_lcm を適用することで証明できます。
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
最後に ProofCafe で教えてもらった別の証明を``chinese_remainder_lite``として記載しておきます。
（なお、一部修正しました）。

eqn_mod_dvd を使って、合同式を整除可能に書き換えたあと、
Gauss_dvd を使って、整除可能の * と && の同値関係で証明をします。
Gauss_dvd の証明には mulm_lcm_gcd を使っています(div.vにて)。

なお、eqn_mod_dvd を使うために ``(m <= n)`` と ``(n <= m)`` の場合分けしています。
これは、前提によらず使用することができますので、覚えておくと便利です。


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
      rewrite 3![m == n %[mod _]]eq_sym. (* 右辺と左辺を入れ替える。 *)
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
