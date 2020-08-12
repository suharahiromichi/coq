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
## Concrete Mathematics [1] の公式
*)
  
(**
###
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

  Lemma m_subn m n p q d  :
    p <= m -> q <= n ->
    m = n %[mod d] -> p = q %[mod d] -> m - p = n - q %[mod d].
  Proof.
  Admitted.

(**
###
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
  
  (* 特別な場合。あとで使う。 *)
  Lemma m_muln' m n p d  :
    m = n %[mod d] -> m * p = n * p %[mod d].
  Proof.
    move=> H.
      by apply: m_muln.
  Qed.
  
(**
###
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
###
 *)  
  (* see also. coq/math/ssr_chinese_remainder.v *)
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
    Check @m_muln' (m * p) (n * p) p' d
      : m * p = n * p %[mod d] -> m * p * p' = n * p * p' %[mod d].
    move/(@m_muln' (m * p) (n * p) p' d) in H.
    rewrite -2!mulnA -[p * p']mulnC in H.
    rewrite Hdef in H.
      by rewrite 2!mulnDr 2!muln1 2!mulnA 2!modnMDl in H.
  Qed.
  
  Lemma m_divn_d' m n p d :
    coprime p d -> (m * p = n * p %[mod d] <-> m = n %[mod d]).
  Proof.
    move=> Hco.
    split.
    - by apply: m_divn_d_1.                 (* -> *)
    - by apply: m_muln'.                    (* <- *)
  Qed.

  Lemma m_divn_d m n p d :
    coprime p d -> (m * p == n * p %[mod d]) = (m == n %[mod d]).
  Proof.
    move=> Hco.
    apply/idP/idP; move/eqP => H; apply/eqP.
    - by apply: (@m_divn_d_1 _ _ p _).      (* -> *)
    - by apply: m_muln'.                    (* <- *)
  Qed.

(**
### 
 *)  
  Lemma m_divn_dp m n p d :
    0 < p -> (m * p == n * p %[mod d * p]) = (m == n %[mod d]).
  Proof.
    move=> Hp.
    rewrite -[RHS](eqn_pmul2r Hp).
    rewrite 2!(muln_modl Hp).
    done.
  Qed.

(**
##
 *)
  Search _ ((_ %| _)).
  Check modn_dvdm
    : forall m n d : nat, d %| m -> n %% m = n %[mod d].
  Check eqn_mod_dvd
    : forall d m n : nat, n <= m -> (m == n %[mod d]) = (d %| m - n).
  Check dvdn_lcm : forall d1 d2 m : nat, (lcmn d1 d2 %| m) = (d1 %| m) && (d2 %| m).

  Lemma test2 m n : (n <= m) = false -> m <= n.
  Proof.
    move=> Hmn.
    ssromega.
  Qed.

  
  Search _ ((_ == _ %[mod _]) = (_ == _ %[mod _]) ).
  Search _ (_ = _ -> _ -> _).
  
(*
  Lemma m_divn m n d p : m = n %[mod d * p] -> m = n %[mod d].
  Proof.
    move=> H.
    case Hnm : (n <= m).
    - apply/eqP.
      rewrite eqn_mod_dvd; last done.
      move/eqP in H.
      rewrite eqn_mod_dvd in H; last done.
        by move/test in H.
    - apply/esym.                           (* 単なる等式の右辺と左辺 *)
      move/esym in H.                     (* 単なる等式の右辺と左辺 *)
      move/test2 in Hnm.
      apply/eqP.
      rewrite eqn_mod_dvd; last done.
      move/eqP in H.
      rewrite eqn_mod_dvd in H; last done.
        by move/test in H.
  Qed.
 *)  
  
  Lemma test3 d1 d2 m : lcmn d1 d2 %| m -> d1 %| m.
  Proof.
    Check dvdn_lcm d1 d2 m.
    rewrite dvdn_lcm => /andP.
      by case.
  Qed.

  Lemma test4 d1 d2 m : d1 %| m -> d2 %| m -> lcmn d1 d2 %| m.
  Proof.
    Check dvdn_lcm d1 d2 m.
    rewrite dvdn_lcm => H1 H2.
    apply/andP.
      by split.
  Qed.
  
  Lemma m_divn_lcm_1_1 m n d1 d2 :
    m = n %[mod lcmn d1 d2] -> m = n %[mod d1].
  Proof.
    move=> H.
    case Hnm : (n <= m).
    - apply/eqP.
      rewrite eqn_mod_dvd; last done.
      move/eqP in H.
      rewrite eqn_mod_dvd in H; last done.
        by move/test3 in H.
    - apply/esym.                           (* 単なる等式の右辺と左辺 *)
      move/esym in H.                     (* 単なる等式の右辺と左辺 *)
      move/test2 in Hnm.
      apply/eqP.
      rewrite eqn_mod_dvd; last done.
      move/eqP in H.
      rewrite eqn_mod_dvd in H; last done.
        by move/test3 in H.
  Qed.

  Lemma m_divn_lcm_1 m n d1 d2 :
    m = n %[mod lcmn d1 d2] -> m = n %[mod d1] /\ m = n %[mod d2].
  Proof.
    split.
    Check @m_divn_lcm_1_1 m n d1 d2.
    - by apply: m_divn_lcm_1_1 H.
    - rewrite lcmnC in H.
        by apply: m_divn_lcm_1_1 H.
  Qed.

  Lemma m_divn_lcm_2 m n d1 d2 :
    m = n %[mod d1] -> m = n %[mod d2] -> m = n %[mod lcmn d1 d2].
  Proof.
    move=> H1 H2.
    case Hnm : (n <= m).
    - apply/eqP.
      rewrite eqn_mod_dvd; last done.
      move/eqP in H1.
      move/eqP in H2.
      rewrite eqn_mod_dvd in H1; last done.
      rewrite eqn_mod_dvd in H2; last done.
        by apply: test4.
    - apply/esym.                           (* 単なる等式の右辺と左辺 *)
      move/esym in H1.                     (* 単なる等式の右辺と左辺 *)
      move/esym in H2.                     (* 単なる等式の右辺と左辺 *)
      move/test2 in Hnm.
      apply/eqP.
      rewrite eqn_mod_dvd; last done.
      move/eqP in H1.
      move/eqP in H2.
      rewrite eqn_mod_dvd in H1; last done.
      rewrite eqn_mod_dvd in H2; last done.
        by apply: test4.
  Qed.

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

  Lemma coprime_lcm d1 d2 : coprime d1 d2 -> lcmn d1 d2 = d1 * d2.
  Proof.
    rewrite /coprime.
    move=> /eqP Hco.
    Check muln_lcm_gcd :  forall m n : nat, lcmn m n * gcdn m n = m * n.
      by rewrite -muln_lcm_gcd Hco muln1.
  Qed.
  
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
[1] Graham, Knuth, Patashnik "Concrete Mathematics", Second Edition
 *)

(* END *)
