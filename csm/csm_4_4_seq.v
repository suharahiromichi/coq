(**
Coq/SSReflect/MathComp による定理証明

第4章 MathComp ライブラリの基本ファイル

4.4 seq.v --- リスト、seq 型のライブラリ

======

2018_12_05 @suharahiromichi
 *)

From mathcomp Require Import all_ssreflect.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(**
# はじめに

本節はテキストを参照しながら、MathComp のソースコードに沿って説明していきます。
ソースコードが手元にあるならば、それも参照してください。
opamでインストールしている場合は、ssrbool.v のソースは、たとえば以下にあります。

~/.opam/4.07.1/lib/coq/user-contrib/mathcomp/ssreflect/seq.v
*)

(**
# cat に関する補題
*)


Check cat0s : forall (T : Type) (s : seq T), [::] ++ s = s.
Check cats0 : forall (T : Type) (s : seq T), s ++ [::] = s.
Check cat1s : forall (T : Type) (x : T) (s : seq T), [:: x] ++ s = x :: s.
Check cats1
  : forall (T : Type) (s : seq T) (z : T), s ++ [:: z] = rcons s z.
Check catA
  : forall (T : Type) (s1 s2 s3 : seq T), s1 ++ s2 ++ s3 = (s1 ++ s2) ++ s3.
Check cat_cons
  : forall (T : Type) (x : T) (s1 s2 : seq T), (x :: s1) ++ s2 = x :: s1 ++ s2.
Check cat_nseq
  : forall (T : Type) (n : nat) (x : T) (s : seq T), nseq n x ++ s = ncons n x s.
Check cat_rcons
  : forall (T : Type) (x : T) (s1 s2 : seq T), rcons s1 x ++ s2 = s1 ++ x :: s2.
Check cat_take_drop
  : forall (n0 : nat) (T : Type) (s : seq T), take n0 s ++ drop n0 s = s.
Check catrev_catl
  : forall (T : Type) (s t u : seq T), catrev (s ++ t) u = catrev t (catrev s u).
Check catrev_catr
  : forall (T : Type) (s t u : seq T), catrev s (t ++ u) = catrev s t ++ u.
Check catrevE : forall (T : Type) (s t : seq T), catrev s t = rev s ++ t.
Check cat_uniq
  : forall (T : eqType) (s1 s2 : seq T),
    uniq (s1 ++ s2) = [&& uniq s1, ~~ has (mem s1) s2 & uniq s2].


(**
# 特別な帰納法 last_ind (rcons でする帰納法の例）

cons と rcons でする帰納法の例：
https://github.com/suharahiromichi/coq/blob/master/ssr/ssr_palindrome.v
*)

Check last_ind
  : forall (T : Type) (P : seq T -> Type),
    P [::] ->
    (forall (s : seq T) (x : T), P s -> P (rcons s x)) -> forall s : seq T, P s.

(**
# has と all
 *)

(**
# catrev (末尾再帰) と rev
 *)

Print rev.
(* Definition rev := catrev^~ [::] *)
(* Definition rev s := catrev s [::] *)

(**
# seq_predType (\in が使える)
*)

Check [:: 1; 2] : seq_predType nat_eqType.
Compute 1 \in [:: 1; 2].                    (* true *)

(**
# seq_eqType (== が使える)
*)

Check [:: 1; 2] : seq_eqType nat_eqType.
Compute [:: 1; 2] == [:: 3; 4].             (* false *)

(**
# map と filter
*)

Check map_cons
  : forall (T1 T2 : Type) (f : T1 -> T2) (x : T1) (s : seq T1),
    [seq f i | i <- x :: s] = f x :: [seq f i | i <- s].
Check map_cat
  : forall (T1 T2 : Type) (f : T1 -> T2) (s1 s2 : seq T1),
    [seq f i | i <- s1 ++ s2] = [seq f i | i <- s1] ++ [seq f i | i <- s2].
Check map_rcons
  : forall (T1 T2 : Type) (f : T1 -> T2) (s : seq T1) (x : T1),
    [seq f i | i <- rcons s x] = rcons [seq f i | i <- s] (f x).
      
(**
使用例：

https://github.com/suharahiromichi/coq/blob/master/egison/ssr_egison_map.v
 *)

(* filter_cons がないので、自分で証明してみる。 *)
Lemma filter_cons (T : Type) (a : pred T) (x : T) (s : seq T) :
  [seq x <- x :: s | a x] =
  (if a x then x :: [seq x <- s | a x] else [seq x <- s | a x]).
Proof.
  elim : s => /=.
  Undo 1.
  elim/last_ind : s => /=.
  - by [].
  - by [].
Qed.

Check filter_cat
  : forall (T : Type) (a : pred T) (s1 s2 : seq T),
    [seq x <- s1 ++ s2 | a x] = [seq x <- s1 | a x] ++ [seq x <- s2 | a x].
Check filter_rcons
  : forall (T : Type) (a : pred T) (s : seq T) (x : T),
    [seq x <- rcons s x | a x] =
    (if a x then rcons [seq x <- s | a x] x else [seq x <- s | a x]).
                                                       

(**
Standard Coq の Forall や Exists と In のリフレクションの例：

https://github.com/suharahiromichi/coq/blob/master/pearl/ssr_list_1.v
 *)

(* END *)
