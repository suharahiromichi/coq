(**
「リストは自分自身のfoldr関数として定義される」こと、または、チャーチ数について
=========

2014_05_11 @suharahiromichi
 *)

(**
# はじめに

TAPL（参考文献1.)には、p.47とp.275の2箇所に渡って、
「リストは自分自身のfoldr関数として定義される」
と書かれている。
しかし、前後の説明を読んでもこの一文の意味することはよくわからなかった。

また、別なところで、
「fixに頼ることなく純粋な言語でソート関数のようなものが書ける…」（同 p.277）
と極めて重要そうなことが書いてある。
これは、チャーチ数やリストのチャーチ表現がそのような性質を持つのであって、
System Fはそれらの型付けをすることができる。と理解するべきなのだろう。

以上のことを納得するために、数やリストについて、

1. Inductiveな定義
2. チャーチ表現
3. fold関数

の関係を調べてみる。
*)

Require Import ssreflect ssrbool ssrnat.

(**
# チャーチ数
  *)

(**
## Inductiveな定義
*)
Inductive Nat : Type :=
| O
| S of Nat.

(**
## チャーチ数
*)
Definition CNat := forall X, (X -> X) -> X -> X.

Definition C0 : CNat := fun X => fun s : X -> X =>
                                   fun z : X => z.
Definition C1 : CNat := fun X => fun s : X -> X =>
                                   fun z : X => s z.
Definition C2 : CNat := fun X => fun s : X -> X =>
                                   fun z : X => s (s z).

(**
## チャーチ数をInductiveな定義にする
*)
Definition cnat2nat (c : CNat) : Nat :=
  c Nat S O.

Eval compute in cnat2nat C2.
(**
= S (S O) : Nat

cnat2natは、チャーチ数cに、Sをfoldしているとみることもできる。
 *)

(**
## Fold関数
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
## Inductiveな定義をチャーチ数にする
*)
Definition nat2cnat (n : Nat) : CNat :=
  fun X =>
    fun s : X -> X =>
      fun z : X => foldNat X s z n.

Eval compute in nat2cnat (S (S O)).
(**
 = fun (X : Type) (s : X -> X) (z : X) => s (s z) : CNat
 *)

(**
## cnat2natとnat2cnatとで元に戻ることの証明
*)

Theorem cnat2nat_nat2cnat :
  forall n : Nat, cnat2nat(nat2cnat n) = n.
Proof.
  rewrite /cnat2nat /nat2cnat.
  elim.
    by [].
  by move=> /= n0 ->.
Qed.

(**
# リスト
*)

(**
## Inductiveな定義
*)
Inductive ListNat : Type :=
| Nil
| Cons of nat & ListNat.

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

(**
## チャーチ表現をInductiveな定義にする
*)
Definition clist2list (c : CListNat) : ListNat :=
  c ListNat Cons Nil.

Eval compute in clist2list CL2.
(**
= Cons 1 (Cons 2 Nil) : ListNat

clist2listは、チャーチ表現のリストcに、Consをfoldrしているとみることもできる。
 *)

(**
## Foldr関数
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
## Inductiveな定義をチャーチ表現にする
*)
Definition list2clist (l : ListNat) : CListNat :=
  fun R =>
    fun c : nat -> R -> R =>
      fun n : R => foldr R c n l.

Eval compute in list2clist (Cons 1 (Cons 2 Nil)).
(**
 = fun (R : Type) (c : nat -> R -> R) (n : R) => c 1 (c 2 n) : CListNat
 *)

(**
## clist2listとlist2clistとで元に戻ることの証明
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

参考文献2.は、無限大のチャーチ数と不動点演算子の
関係をHaskellで論じていて、参考になった。
*)

(**
# 参考文献

1. Pierce、住井 監訳「型システム入門 プログラミング言語と型の理論」オーム社
2. 酒井 「不動点演算子はチャーチ数での無限大?」 http://msakai.jp/d/?date=20100628
*)

(* END *)
