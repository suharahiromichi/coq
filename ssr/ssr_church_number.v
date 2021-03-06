(**
「リストは自分自身のfoldr関数として定義される」につついて
=========

2014_05_11 @suharahiromichi
 *)

(**
# はじめに

TAPL（参考文献1.)には、p.47とp.275の2箇所に渡って、
「リストは自分自身のfoldr関数として定義される」
と書かれている。
しかし、前後の説明を読んでもこの一文の意味することはよくわからなかった。

また、別なところ（同 p.277）で、
「(System Fは)fixに頼ることなく純粋な言語でソート関数のようなものが書ける…」
と極めて重要なことが書いてある。
これは、チャーチ数やリストのチャーチ表現がそのような性質を
持つのであって、System Fはそれらを扱える（型付けをすることができる）
と理解するべきなのだろう。

以上のことを納得するために、数やリストについて、

1. Inductiveな定義
2. チャーチ表現
3. fold関数


の関係を調べてみる。証明はCoq SSRefelctで行う。
*)
(**
この文章のソースコードは、以下にあります。

https://github.com/suharahiromichi/coq/blob/master/ssr/ssr_church_number.v
*)

Require Import ssreflect ssrbool ssrnat.

(**
# チャーチ数
  *)

(**
## チャーチ数(CNat)
*)
Definition CNat := forall X, (X -> X) -> X -> X.

Definition C0 : CNat := fun X => fun s : X -> X =>
                                   fun z : X => z.
Definition C1 : CNat := fun X => fun s : X -> X =>
                                   fun z : X => s z.
Definition C2 : CNat := fun X => fun s : X -> X =>
                                   fun z : X => s (s z).
Definition CSucc : CNat -> CNat :=
  fun n : CNat => fun X =>
                    fun s : X -> X =>
                      fun z : X => s (n X s z).
Eval compute in CSucc C0.

(**
## InductiveなNatの定義
*)
Inductive Nat : Type :=
| O
| S of Nat.

(**
## CNatとNatの間の変換

### CNatをNatに変換する関数
*)
Definition CNat2Nat (c : CNat) : Nat :=
  c Nat S O.

Eval compute in CNat2Nat C2.
(**
= S (S O) : Nat

これはチャーチ数cに、Sをfoldしているとみることもできる。
 *)

(**
### Fold関数

Inductiveに定義したNatに対しては、Foldを定義しなければならない。
*)
Fixpoint foldNat (X : Type) (s : X -> X) (z : X) (n : Nat) : X :=
  match n with
    | O => z
    | S n' => s (foldNat X s z n')
  end.

Check foldNat.
(**
 : forall X : Type, (X -> X) -> X -> Nat -> X
 *)

(**
### NatをCNatに変換する関数
*)
Definition Nat2CNat (n : Nat) : CNat :=
  fun X =>
    fun s : X -> X =>
      fun z : X => foldNat X s z n.

Eval compute in Nat2CNat (S (S O)).
(**
 = fun (X : Type) (s : X -> X) (z : X) => s (s z) : CNat

Inductiveに定義された整数nに、sをFoldし、そのsをλ抽象すると、チャーチ数が得られる。
 *)

(**
## 証明

### C0とOが同じ、CSuccとSの結果が同じになることの証明
*)
Theorem CNat_Nat_zero :
  CNat2Nat C0 = O.
Proof.
    by [].
Qed.

Theorem CNat_Nat_succ :
  forall c n,
    CNat2Nat c = n -> CNat2Nat (CSucc c) = S n.
Proof.
  rewrite /CNat2Nat /CSucc.
    by move=> c n ->.
Qed.

(**
### CNat2NatとNat2CNatで元に戻ることの証明
*)
Theorem CNat2Nat_Nat2CNat :
  forall n : Nat, CNat2Nat(Nat2CNat n) = n.
Proof.
  rewrite /CNat2Nat /Nat2CNat.
  elim.
    by [].
  by move=> /= n0 ->.
Qed.

(**
# 自然数のリスト

要素の自然数は、SSReflectのnatの定義を使う。
*)
(**
## チャーチ表現
*)
Definition CListNat := forall R, (nat -> R -> R) -> R -> R.

Definition CNil : CListNat :=
  fun R => fun c : nat -> R -> R =>
             fun n : R => n.                (* [] *)
Definition CL1 : CListNat :=
  fun R => fun c : nat -> R -> R =>
             fun n : R => c 1 n.            (* [1] *)
Definition CL2 : CListNat :=
  fun R => fun c : nat -> R -> R =>
             fun n : R => c 1 (c 2 n).      (* [1,2] *)
Definition CL3 : CListNat :=
  fun R => fun c : nat -> R -> R =>
             fun n : R => c 1 (c 2 (c 3 n)). (* [1,2,3] *)
Definition CCons : nat -> CListNat -> CListNat :=
  fun hd : nat =>
    fun tl : CListNat =>
      fun R =>
        fun c : nat -> R -> R =>
          fun n : R => c hd (tl R c n).
Eval compute in CCons 1 CNil.

(**
## Inductiveな定義
*)
Inductive ListNat : Type :=
| Nil
| Cons of nat & ListNat.

(**
## clistとlistの間の変換

### clistをlistに変換する関数
*)
Definition clist2list (c : CListNat) : ListNat :=
  c ListNat Cons Nil.

Eval compute in clist2list CL2.
(**
= Cons 1 (Cons 2 Nil) : ListNat

clist2listは、チャーチ表現のリストcに、Consをfoldrしているとみることもできる。
 *)

(**
### Foldr関数

Inductiveに定義したlistに対しては、Foldを定義しなければならない。
*)
Fixpoint foldr (R : Type) (c : nat -> R -> R) (n : R) (l : ListNat) : R :=
  match l with
    | Nil => n
    | Cons x l' => c x (foldr R c n l')
  end.

Check foldr.
(**
 : forall R : Type, (nat -> R -> R) -> R -> ListNat -> R
 *)

(**
### listをclistに変換する関数
*)
Definition list2clist (l : ListNat) : CListNat :=
  fun R =>
    fun c : nat -> R -> R =>
      fun n : R => foldr R c n l.

Eval compute in list2clist (Cons 1 (Cons 2 Nil)).
(**
 = fun (R : Type) (c : nat -> R -> R) (n : R) => c 1 (c 2 n) : CListNat

Inductiveに定義されたリストlに、cをFoldrし、そのcをλ抽象すると、
チャーチ表現で表したリストが得られる。
 *)

(**
## 証明

### CNilとnilが同じ、CConsとConsの結果が同じになることの証明
*)
Theorem clist_list_nil :
  clist2list CNil = Nil.
Proof.
    by [].
Qed.

Theorem clist_list_cons :
  forall c l n,
    clist2list c = l ->
    clist2list (CCons n c) = Cons n l.
Proof.
  rewrite /clist2list /CCons.
    by move=> c l n ->.
Qed.

(**
## clist2listとlist2clistで元に戻ることの証明
*)

Theorem clist2list_list2clist :
  forall l : ListNat, clist2list(list2clist l) = l.
Proof.
  rewrite /clist2list /list2clist.
  elim.
    by [].
  by move=> /= n l ->.
Qed.

(**
# まとめ

わかったこと。
チャーチ数やリストのチャーチ表現は、それ自身にFoldの機能を持っていること。
また、Inductiveに定義したnatやlistは、Fold関数によってチャーチ表現に変換できること。

参考文献2.は、無限大のチャーチ数と不動点演算子の関係をHaskellで
論じたもので、FoldNatの定義などを参考にさせていただいた。
*)

(**
# 参考文献

1. Pierce、住井 監訳「型システム入門 プログラミング言語と型の理論」オーム社
2. 酒井 「不動点演算子はチャーチ数での無限大?」 http://msakai.jp/d/?date=20100628
*)

(* END *)
