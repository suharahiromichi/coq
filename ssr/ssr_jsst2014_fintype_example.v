(**
日本ソフトウェア科学会
チュートリアル(1) 定理証明支援系Coq入門

講師：アフェルト レナルド 先生
https://staff.aist.go.jp/reynald.affeldt/ssrcoq/coq-jssst2014.pdf
 *)

(**
首記の講演から興味のもとに抜粋し、例題を追加したものです。
内容の責任は  @suharahiromichi にあります。
 *)

(**
fintype.v: 有限な数の要素のある型
 *)
(* fintype_example.v の 前半は略。 *)

Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq choice fintype.

Check 'I_3.                                 (* 0〜2までの、自然数の部分型 *)
Check 'I_4.                                 (* 0〜3までの、自然数の部分型 *)

Variable lt23 : 2 < 3.                      (* 2が3より小さいという証明のあるとき。 *)
Variable lt24 : 2 < 4.                      (* 2が4より小さいという証明のあるとき。 *)

Compute Ordinal lt23.                       (* 2 : 'I_3 を得る。 *)
Compute Ordinal lt24.                       (* 2 : 'I_4 を得る。 *)

Check erefl.                                (* _ = _ *)
Compute @Ordinal 3 2 erefl.                 (* 隠れた引数は 2 < 3 と順番が逆。 *)
Compute @Ordinal 4 2 erefl.                 (* 隠れた引数は 2 < 4 と順番が逆。 *)

Fail Check Ordinal lt23 = Ordinal lt24.     (* 型が違うので比較できない。  *)

(** 2 : 'I_3 どうしの一致の証明は val_inj を使用する。  *)
Goal forall lt23' : 2 < 3,
       Ordinal lt23 = Ordinal lt23'.
Proof.
  move=> lt23'.
    by apply: val_inj.
Qed.       

(** 自然数を取り出すには、nat_of_ord を使う。 *)
Compute nat_of_ord (Ordinal lt23).          (* 2 *)
Compute nat_of_ord (Ordinal lt24).          (* 2 *)

Module Test.
  Variable lt32 : 3 < 2.                    (* 3 < 2 を前提とすると、*)
  Compute Ordinal lt32.                     (* 3 : 'I_2 を得ることができる。 *)
  Compute nat_of_ord (Ordinal lt32).        (* 3 自然数にも戻る。 *)
End Test.

(** 3 = n の証明が与えられたとき、2 : 'I_3 に対して、2 : 'I_n を返す。 *)
Variable eqnn : 3 = 3.
Check cast_ord eqnn (Ordinal lt23) : 'I_3.

(** val_inj を使用した証明の例  *)
Goal forall (n : nat) (eq_nn : n = n) (i : 'I_n), cast_ord eq_nn i = i.
Proof.
  move=> n eqnn i.
  by apply: val_inj.
Qed.

(** val_inj を使用した証明の例  *)
Lemma cast_ord_comp n1 n2 n3 (eq_n2 : n1 = n2) (eq_n3 : n2 = n3) i :
  cast_ord eq_n3 (cast_ord eq_n2 i) = cast_ord (etrans eq_n2 eq_n3) i.
Proof.
  apply: val_inj.
  by [].
Qed.

Definition o0 := @Ordinal 3 O erefl.
Definition o1 := @Ordinal 3 1 erefl.
Definition o2 := @Ordinal 3 2 erefl.

Goal enum 'I_3 = [:: o0; o1; o2].
Proof.
  rewrite enum_ordS.
  congr (_ :: _).
  - by apply val_inj.
  - rewrite enum_ordS.
    rewrite /=.
    congr (_ :: _).
    + apply val_inj.
      by rewrite /=.
    + rewrite enum_ordS.
      rewrite /=.
      congr (_ :: _).
      * apply val_inj.
        by rewrite /=.
      * apply size0nil.
        rewrite size_map.
        rewrite size_map.
        rewrite size_map.
        rewrite size_enum_ord.
        by [].
Qed.

(* END *)
