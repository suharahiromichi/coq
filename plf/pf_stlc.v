(** ProofCafe SF/PLF Support Page *)
(** Stlc.v *)

(**
これは、「Software Foundations, Vol.2 Programming Language Foundations」 の
勉強会（ProofCafe）のサポートページです。復習などに利用しててください。

本ファイルの実行は、本ファイルを pfl ディレクトリの中に混ぜて置くか、
pfl のオリジナルの適当なファイルの適当な場所にcopy&pasteすることで可能です。
 *)

(** ご注意：

1. 実際の勉強会は、本ファイルではなく、オリジナルのファイルを直接編集・実行しておこないます。

2. 本ファイルには、演習問題の答えは含まれません。

*)

Require Import Coq.Arith.Arith.
Require Import Maps.
Require Import Imp. 
Require Import Smallstep.
Require Import Types.
Require Import Stlc.

(* ################################################################# *)
(** ProofCafe ##77 2018/07/21 *)

(** 自由変数の扱いについて。テクニカルノート *)

(** 「λx.(x x) の型付け不能」 最後の演習問題 *)

(** [~ (exists S, exists T, empty |- \x : S. x x \in T) ] **)
(** [~ (∃S. ∃T. ├ λx : S.(x x) ∈ T *)

Check STLC.typing_nonexample_3 :
  ~ (exists S T : STLC.ty,
        STLC.has_type empty
                      (STLC.tabs STLC.x S (STLC.tapp (STLC.tvar STLC.x) (STLC.tvar STLC.x)))
                      T).

(** ***************** *)
(** TAPL 演習 9.3.2 が参考になる。 *)
(** ***************** *)

(** TAPL の 演習 9.3.2 *)
(** 回答 9.3.2. では、すべての型が有限サイズを持つことから、
    T1 -> T2 = T1 は偽であるとしている。 *)
Lemma type_finiteness : forall (T1 T2 : STLC.ty), STLC.TArrow T1 T2 <> T1.
Proof.
  intros T1 T2 H.
  induction T1 as [|T11 H1 T12 H2].
  - (* T1 = TBool *)
    easy.
  - (* T1 = T11 -> T12 *)
    (* inversion タクティクは、TAPL の 型付け関係の逆転の補題
       (9.3.1 inversion lemma) を使うのとと同じ。 *)
    inversion H.
    (* T11 -> T12 = T11 を得る。 *)
    rewrite H4 in *.                      (* subst はエラーになる。 *)
    (* これは偽である。 *)
    easy.
Qed.

(** ***************** *)
(** これは、STLCに限定したことでははなく、コンストラクタ一般に成り立つ。  *)
(** ***************** *)

(** Smallstep で定義した Plus コンストラクタの場合 *)
Goal forall tm1 tm2, P tm1 tm2 <> tm1.
Proof.
  intros tm1 tm2 H.
  induction tm1.
  - easy.
  - inversion H.
    rewrite H1 in *.
    easy.
Qed.

(** list の cons の有限性 *)
Lemma list_finiteness : forall (n : nat) (l : list nat), cons n l <> l.
Proof.
  intros n l H.
  induction l as [|n' l].
  - easy.
  - inversion H; clear H.                 (* subst はエラーになる。 *)
    rewrite H1 in *; clear H1.
    easy.
Qed.

(** より一般的に、(Inductiveで定義された）コンストラクタの有限性を証明できないだろうか。 *)
(** 直観的な証明ではひとことで済むことが、形式的には毎回証明が必要になる例だろうか。 *)

(* END *)
