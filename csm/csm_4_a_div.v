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
## Concrete Mathematics の公式
*)
  Lemma m_addn a b c d m :
    a = b %[mod m] -> c = d %[mod m] -> a + c = b + d %[mod m].
  Proof.
    move=> Hac Hbd.
    Search _ (_ + _ %% _).
    Check modnDm
      : forall m n d : nat, m %% d + n %% d = m + n %[mod d].
    rewrite -[LHS]modnDm -[RHS]modnDm.
    congr (_ %% _).
    (* 前提からは、より一般的な定理が導けるわけである。 *)
    (* Goal : a %% m + c %% m = b %% m + d %% m *)
    congr (_ + _).
    - done.
    - done.
  Qed.

  Lemma m_muln a b c d m :
    a = b %[mod m] -> c = d %[mod m] -> a * c = b * d %[mod m].
  Proof.
    move=> Hac Hbd.
    Search _ ((_ * _) %% _).
    Check modnMm
      : forall m n d : nat, m %% d * (n %% d) = m * n %[mod d].
    rewrite -[LHS]modnMm -[RHS]modnMm.
    congr (_ %% _).
    (* Goal : a %% m * (c %% m) = b %% m * (d %% m) *)
      by congr (_ * _).
  Qed.
  
  Lemma m_exprn a b n m :
    a = b %[mod m] -> a^n = b^n %[mod m].
  Proof.
    move=> Hac.
    Search _ (_ ^ _ %% _).
    Check modnXm
      : forall m n a : nat, (a %% n) ^ m = a ^ m %[mod n].
    rewrite -[LHS]modnXm -[RHS]modnXm.
    congr (_ %% _).
    (* Goal : (a %% m) ^ n = (b %% m) ^ n *)
      by congr (_ ^ n).
  Qed.

End Modulo.

(**
[1] Graham, Knuth, Patashnik "Concrete Mathematics", Second Edition
 *)

(* END *)
