(**
置換を最小の互換の列に変換する関数の健全性、最小性をCoq/SSReflectで証明する
(2024年TPPmark問1,2の解答)

https://qiita.com/nekonibox/items/91cbeb3bc1e1e6abbf35
*)
From mathcomp Require Import all_ssreflect all_fingroup.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(**
# 置換、循環、互換
*)

Section a.
  Variable T : finType.
  
(**
## perm,v 置換を循環に変換するふたつの方法
 *)
  (* 有限関数を返す。 *)
  Check @porbit T : {perm T} -> T -> {set T}.
  (* 列を返す。 *)
  Check (fun (s : {perm T}) x => traject s x #|porbit s x|) : {perm T} -> T -> seq T.
  
  (* 両者は一致する。 *)
  Check @porbit_traject T
    : forall (s : {perm T}) (x : T), porbit s x =i traject s x #|porbit s x|.
  Check @porbitP T
    : forall (s : {perm T}) (x y : T), reflect (exists i : nat, y = (s ^+ i)%g x) (y \in porbit s x).
  
(**
## 互換を計算する
*)
  Check @tpermL T : forall x y : T, (tperm x y) x = y.
  Check @tpermR T : forall x y : T, (tperm x y) y = x.
  Check @tpermD T : forall x y z : T, x != z -> y != z -> tperm x y z = z. (* 互換が起きない場合 *)
  
  Goal forall (x y z a : T), tperm x y z = a.
  Proof.
    move=> x y z a.
    case: tpermP.
    Check z = x -> y = a.
    Check z = y -> x = a.
    Check z <> x -> z <> y -> z = a.
  Admitted.

(**
# perm.vにはない置換に関する汎用的な定理
*)  
  (* 略 *)
End a.

Require Import tppmark2024.

(**
# 問1 置換から互換の列への変換関数
*)
Section s1.

  Variable T : finType.

(**
## 関数
*)
  Check seq (seq T).                        (* 循環の列 *)
  
  (* 循環の列を置換に変換する。 *)
  Check @toperm T : seq (seq T) -> {perm T}. (* 前から、循環の先頭の要素と互換 *)
  Check @irtoperm T : seq (seq T) -> {perm T}. (* 後から、循環の隣り合った要素と互換 *)
  (* 置換を循環の列に変換する。 *)
  Check @fromperm T : {perm T} -> seq (seq T).
  
  (* 互換であることを判定する。 *)
  Check {perm T}.                           (* 互換 *)
  Check @istperm T : pred {perm T}.

  (* 互換の列であることを判定する。 *)
  Check seq {perm T}.                       (* 互換の列 *)
  Check @isexchanges T : pred (seq {perm T}).

  (* 循環の列を互換の列に変換する。 *)
  Check @toexchanges T : seq (seq T) -> seq {perm T}.

  (* 置換を互換の列に変換する。 *)
  Check @toexchanges T \o @fromperm T : {perm T} -> seq {perm T}.

  (* 置換のノルム *)
  Check @permnorm T : {perm T} -> nat.

(**
## 補題

### fromperm の健全性
  fromperm して toperm するともとに戻る。
 *)
  Check @toperm_fromperm T : cancel (@fromperm T) (@toperm T).

(**
### toexchanges の正しさ

- その結果が、互換の列であること。
 *)
  Check @toexchange_isexchanges T
    : forall (s : seq (seq T)), isexchanges (toexchanges s).
(**  
- 右辺：循環の列を互換の列に変換して、その互換の列をすべて掛けて得た置換は、
  左辺：循環の列を置換に変換したもの、に等しい。
 *)
  Check @toexchanges_toperm T
    : forall s : seq (seq T), toperm s = foldr mulg 1%g (toexchanges s).


(**
# 2 問1の関数の健全性

## 補題

### toexchanges \o fromperm (置換を互換の列に変換) の正しさ

- その結果が、互換の列であること。
 *)
  Check @toexchange_fromperm_isexchanges T
    : forall p : {perm T}, isexchanges (toexchanges (fromperm p)).

(**
- toexchanges \o fromperm の健全性
  置換を互換の列に変換したものは、互換の列を全て掛けるともとの置換に戻る。
*)
  Check @toexchanges_fromperm T
    : cancel (@toexchanges T \o @fromperm T) (foldr mulg 1%g).


(**
# 2 問1の関数の最小性

## 補題

- toexchanges \o fromperm で得られた互換の列の長さは、permnorm に等しい。以下サイズと呼ぶ。
 *)
  Check @permnorm_size_toexchanges T
    : forall p : {perm T}, permnorm p = size (toexchanges (fromperm p)).

(**
- 証明したい定理 : toexchanges \o fromperm で得られた互換の列は、最小である。
 *)
  Check @toexchanges_min T
    : forall (p : {perm T}) (s : seq {perm T}),
      isexchanges s ->
      foldr mulg 1%g s = p ->
      size (toexchanges (fromperm p)) <= size s.

(**
## tperm x y * pに関する性質
*)
  Check @porbit_tperm_notin T
    : forall (p : {perm T}) (x y : T),
       y \notin porbit p x -> porbit ((tperm x y) * p) x = porbit p x :|: porbit p y.

  Check @porbit_tperm_in T
    : forall (p : {perm T}) (x y : T),
      y \in porbit p x -> porbit ((tperm x y) * p) x :|: porbit ((tperm x y) * p) y = porbit p x.

  Check @porbit_disjointP T
    : forall (p : {perm T}) (x y : T), reflect [disjoint porbit p x & porbit p y] (y \notin porbit p x).

  Check @permnorm_tperm_notin T
    : forall (p : {perm T}) (x y : T), y \notin porbit p x -> (permnorm p).+1 = permnorm ((tperm x y) * p).

  Check @permnorm_tperm_in T
    : forall (p : {perm T}) (x y : T),
      y != x -> y \in porbit p x -> permnorm p = (permnorm ((tperm x y) * p)).+1.

(**
- 置換pのサイズは、置換pに互換をひとつ加えたもののサイズ(+1) 以下である。
  以上の補題から下記が証明できる。さらに、これの帰納法で、証明したい定理を証明できる。
*)
  Check @permnorm_tperm T
    : forall (p : {perm T}) (x y : T), permnorm p <= (permnorm ((tperm x y) * p)).+1.
  
End s1.

(* END *)
