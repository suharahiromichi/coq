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
  
  Lemma m_muln' m n p d  :
    m = n %[mod d] -> m * p = n * p %[mod d].
  Proof.
    move=> H.
      by apply: m_muln.
  Qed.
  
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
  
  Lemma m_divn_d_2 m n p d :
    m = n %[mod d] -> m * p = n * p %[mod d].
  Proof.
    move=> H.
      by apply: m_muln.
  Qed.

  Lemma m_divn_d m n p d :
    coprime p d -> (m * p = n * p %[mod d] <-> m = n %[mod d]).
  Proof.
    move=> Hco.
    split.
    - by apply: m_divn_d_1.
    - by apply: m_divn_d_2.
  Qed.

  Lemma m_divn_d' m n p d :
    coprime p d -> (m * p == n * p %[mod d]) = (m == n %[mod d]).
  Proof.
    move=> Hco.
    apply/idP/idP; move/eqP => H; apply/eqP.
    - by apply: (@m_divn_d_1 _ _ p).
    - by apply: m_divn_d_2.
  Qed.
  
End Modulo.

(**
[1] Graham, Knuth, Patashnik "Concrete Mathematics", Second Edition
 *)

(* END *)
