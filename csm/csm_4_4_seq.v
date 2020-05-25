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
# seq

seq はpolymorphicな型である。

Standard Coqのlistをリネームしたものであるので、CICに基づく帰納法の原理は、
list_indである。seq_indではない。
 *)
Check list_ind
  : forall (A : Type) (P : seq A -> Prop),
    P [::] ->
    (forall (a : A) (l : seq A), P l -> P (a :: l)) -> forall l : seq A, P l.


(**
# rcons

rcons は再帰的に定義されている。

Fixpoint rcons s z := if s is x :: s' then x :: rcons s' z else [:: z].

教科書にあるような、リストの後ろにcat (++, append) する定義とは異なる。
 *)
Definition rcons' (T : Type) (s : seq T) (z : T) : seq T := s ++ [:: z].

(**
しかし、両者が同値であることは証明できる。
*)
Goal forall (T : Type) (s : seq T) (z : T), rcons s z = rcons' s z.
Proof.
  move=> T s z.
  elim: s => //.
  move=> a s IH /=.
    by rewrite IH /rcons' /=.

  Restart.
  move=> T s z.
    by rewrite /rcons' cats1.
Qed.


(**
# cat (++, append) 

## cat に関する補題
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

(**
## Inductive に定義した append と cat の同値を証明する。
*)
Section Lists1.
  Variable A : Type.

  Inductive append : seq A -> seq A -> seq A -> Prop :=
  | append_nil (b : seq A) : append [::] b b
  | append_cons (h : A) (a b c : seq A) :
      append a b c -> append (h :: a) b (h :: c).
  Hint Constructors append.
  
  Lemma append_cat (a b c : seq A) : append a b c <-> a ++ b = c.
  Proof.
    split.
    - elim=> b'' //= a' b' c' H IH.
        by rewrite IH.
    - elim: a b c => //= [b c -> // | n' a' IH b' c' <-].
      apply: append_cons.
        by apply: IH.
  Qed.
(**
補足： <-> のかたちの補題を適用するときは、apply/V を使う。
*)
End Lists1.

  
(**
# has と all と nth

## 説明

リストのある要素（すべての要素）に対して、条件が成立する。
 *)

Compute has odd [:: 1; 2; 3].               (* true *)
Compute has odd [:: 2; 4; 6].               (* false *)

Compute all odd [:: 1; 2; 3].               (* false *)
Compute all odd [:: 1; 3; 5].               (* true *)

(**
## forall や exists を使った定義

has や all は再帰関数として定義されているが、exists や forall を使った定義もある。
それとのリフレクションが定義されている。
 *)

Check @hasP : forall (eT : eqType) (a : pred eT) (s : seq eT),
    reflect (exists2 x : eT, x \in s & a x) (has a s).

Check @allP : forall (eT : eqType) (a : pred eT) (s : seq eT),
    reflect (forall x : eT, x \in s -> a x) (all a s).

(**
なお、exists2 は、論理式をふたつとれる「∃」。
MathComp ぽい命名だが、バニラCoqで定義されている。
*)
Check ex : forall A : Type, (A -> Prop) -> Prop.
Check ex2 : forall A : Type, (A -> Prop) -> (A -> Prop) -> Prop.
Check forall (A : Type) (x : A) (P : Prop), (exists x : A, P).
Check forall (A : Type) (x : A) (P Q : Prop), (exists2 x : A, P & Q).

(**
## Standard Coq の 命題

Standard Coq の List.v には、インダクティブな命題として、
Exists と Forall が定義されている。それとのリフレクションを定義した例：

https://github.com/suharahiromichi/coq/blob/master/pearl/ssr_list_1.v
 *)

(**
## has と all と nth についての補題
*)

(* *** 後で追加する。*** *)


(**
# rev

## 説明

rev は catrev (末尾再帰) を使って定義されている。
 *)
Print rev.
(* Definition rev := catrev^~ [::] *)
(* Definition rev s := catrev s [::] *)

Section Lists2.
  Variable A : Type.

(**
## Inductive に定義した reverse と rev の同値を証明する。
*)
  Inductive reverse : seq A -> seq A -> Prop :=
  | reverse_nil (s : seq A) : reverse [::] [::]
  | reverse_cons (x : A) (s t : seq A) :
      reverse s t -> reverse (x :: s) (rcons t x).
  Hint Constructors reverse.

  Lemma rev0 : @rev A [::] = [::].
  Proof.
      by rewrite /rev.
  Qed.
  
  Lemma rev1 (x : A) : @rev A [:: x] = [:: x].
  Proof.
      by rewrite /rev.
  Qed.
  
  Lemma rev_catrev (s t : seq A) : reverse s t <-> rev s = t.
  Proof.
    split.
    - elim=> [s' | x s' t' H IH].
      + by rewrite /rev.
      + by rewrite rev_cons IH.
    - elim: s t => //= [t <- | x s IH t' <-].
      + rewrite rev0.
          by apply: reverse_nil.
      + rewrite rev_cons.
        apply: reverse_cons.
          by apply: IH.
  Qed.

(**
末尾再帰ではない rev につていも、同様に証明する。
 *)
  Fixpoint ntrev (s : seq A) : seq A :=
    match s with
    | [::] => [::]
    | x :: a => rcons (ntrev a) x
    end.
  
  Lemma rev_ntrev (s t : seq A) : reverse s t <-> ntrev s = t.
  Proof.
    split.
    - elim=> [s' | x s' t' H <-] //=.
    - elim: s t => //= [t <- | x s IH t' <-].
      + by apply: reverse_nil.
      + apply: reverse_cons.
          by apply: IH.
  Qed.      
End Lists2.

(**
## rev に関する補題
 *)
Check catrev_catl
  : forall (T : Type) (s t u : seq T), catrev (s ++ t) u = catrev t (catrev s u).
Check catrev_catr
  : forall (T : Type) (s t u : seq T), catrev s (t ++ u) = catrev s t ++ u.
Check catrevE : forall (T : Type) (s t : seq T), catrev s t = rev s ++ t.
Check cat_uniq
  : forall (T : eqType) (s1 s2 : seq T),
    uniq (s1 ++ s2) = [&& uniq s1, ~~ has (mem s1) s2 & uniq s2].
Check rev_cons
  : forall (T : Type) (x : T) (s : seq T), rev (x :: s) = rcons (rev s) x.
Check size_rev
  : forall (T : Type) (s : seq T), size (rev s) = size s.
Check rev_cat
  : forall (T : Type) (s t : seq T), rev (s ++ t) = rev t ++ rev s.
Check rev_rcons
  : forall (T : Type) (s : seq T) (x : T), rev (rcons s x) = x :: rev s.

Check revK                                  (* rev (rev s) = s *)
  : involutive rev.

Check nth_rev
  : forall (T : Type) (x0 : T) (n : nat) (s : seq T),
    n < size s -> nth x0 (rev s) n = nth x0 s (size s - n.+1).
Check filter_rev
  : forall (T : Type) (a : pred T) (s : seq T),
    [seq x <- rev s | a x] = rev [seq x <- s | a x].
Check count_rev
  : forall (T : Type) (a : pred T) (s : seq T), count a (rev s) = count a s.
Check has_rev
  : forall (T : Type) (a : pred T) (s : seq T), has a (rev s) = has a s.
Check all_rev
  : forall (T : Type) (a : pred T) (s : seq T), all a (rev s) = all a s.

(**
# == と \in について
 *)

(**
## seq_eqType (== が使える)

eqType 型クラス（インターフェース）のインスタンスとして seq_eqType を定義している。
すると、seq eT 型 (ただし eT は、eqType のインスタンス） は、== の左右に書けるようになる。
*)

Check [:: 1; 2] : seq_eqType nat_eqType.
Compute [:: 1; 2] == [:: 3; 4].             (* false *)

(**
== の定義として eqseq が使われる。
*)
Check @eqseq : forall T : eqType, seq T -> seq T -> bool.

(*
## seq_predType (\in が使える)

predType 型クラス（インターフェース）のインスタンスとして seq_predType を定義している。
すると、seq eT 型 (ただし eT は、eqType のインスタンス） は、\in の右に書けるようになる。
*)

Check [:: 1; 2] : seq_predType nat_eqType.
Compute 1 \in [:: 1; 2].                    (* true *)

(**
Standard Coq の List.v には、インダクティブな命題として、
In が定義されている。それとのリフレクションを定義した例：

https://github.com/suharahiromichi/coq/blob/master/pearl/ssr_list_1.v
 *)
(**
\in の定義として mem_seq が使われる。
*)
Check @mem_seq : forall T : eqType, seq T -> T -> bool.

(**
## \in についての補題
 *)

(* *** 後で追加する。*** *)

(**
# map と filter

## 説明
*)

Compute map succn [::  1; 2; 3].            (* [:: 2; 3; 4] *)
Compute [seq succn x | x <- [:: 1; 2; 3]].  (* [:: 2; 3; 4] *)

Compute filter odd [:: 1; 2; 3].            (* [:: 1 3] *)
Compute [seq x <- [:: 1;2;3] | odd x].      (* [:: 1 3] *)


(**
ラムダ式を書かなくてすむ。
 *)
Compute map (fun x => x + 2) [::  1; 2; 3]. (* [:: 3; 4; 5] *)
Compute [seq x + 2 | x <- [:: 1; 2; 3]].    (* [:: 3; 4; 5] *)

Compute filter (fun x => ~~ odd x) [:: 1; 2; 3]. (* [:: 2] *)
Compute [seq x <- [:: 1;2;3] | ~~ odd x].        (* [:: 2] *)


(**
まとめてひとつの [seq ... ] で書けるわけではない。
 *)
Compute [seq x <- [seq succn x | x <- [:: 1; 2; 3]]  | odd x]. (* [:: 3] *)
Compute [seq succn x | x <- [seq x <- [:: 1;2;3] | odd x]]. (* [:: 2; 4] *)


(**
## map と filter の補題

map と filter についてのいくつかの補題が証明されている。かなり便利である。
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
# foldr と foldl
 *)

(* *** 後で追加する。*** *)



(**
# 特別な帰納法
 *)

(**
## lastP

(これは帰納法でないが) ゴールを ``[::]`` と ``rcons p x`` に分ける。
 *)

(* *** 後で追加する。*** *)


(**
## last_ind

rcons でする帰納法である。
*)
Check last_ind
  : forall (T : Type) (P : seq T -> Type),
    P [::] ->
    (forall (s : seq T) (x : T), P s -> P (rcons s x)) -> forall s : seq T, P s.

Section FoldLeft.

  Variables (T R : Type) (f : R -> T -> R).
  
  Lemma foldl_rev (z : R) (s : seq T) :
    foldl f z (rev s) = foldr (fun x z => f z x) z s.
  Proof.
    elim/last_ind: s z => [|s x IHs] z //=.
      by rewrite rev_rcons -cats1 foldr_cat -IHs.
  Qed.
End FoldLeft.

(**
## seq2_ind
 *)
Lemma seq2_ind T1 T2 (P : seq T1 -> seq T2 -> Type) :
    P [::] [::] -> (forall x1 x2 s1 s2, P s1 s2 -> P (x1 :: s1) (x2 :: s2)) ->
  forall s1 s2, size s1 = size s2 -> P s1 s2.
Proof. by move=> Pnil Pcons; elim=> [|x s IHs] [] //= x2 s2 [] /IHs/Pcons. Qed.


(**
## alt_list_ind

https://github.com/suharahiromichi/coq/blob/master/ssr/ssr_palindrome.v

回文の証明で使用した cons と rcons でする帰納法の例：

alt_list_ind : 
    P [::] ->
    (forall (x : X), P [:: x]) ->
    (forall (l : seq X), P l -> forall (x y : X), P (x :: (l ++ [:: y]))) ->
    forall (ln : seq X), P ln.
*)

(* END *)
