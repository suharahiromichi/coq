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

Standard Coqのlistをリネーム (Definiton seq := list) したものであるので、
CICに基づく帰納法の原理は、list_indである。seq_indではない。
 *)
Check list_ind
  : forall (A : Type) (P : seq A -> Prop),
    P [::]                                  (* 帰納法に基底 *)
    ->
    (forall (a : A) (l : seq A), P l        (* 帰納法の仮定 *)
                                 ->
                                 P (a :: l)) (* 証明するべきもの *)
    ->
    forall l : seq A, P l.                  (* 結論 *)

(**
# rcons

rcons は再帰的に定義されている。

Fixpoint rcons s z := if s is x :: s' then x :: rcons s' z else [:: z].

教科書にあるような、リストの後ろにcat (++, append) する定義とは異なる。
 *)
Section RconsQ.
  Variable T : Type.
  
  Definition rcons' (T : Type) (s : seq T) (z : T) : seq T := s ++ [:: z].

(**
（演習）両者が同値であることを証明してください。
*)
  Goal forall (s : seq T) (z : T), rcons s z = rcons' s z.
  Proof.
  Admitted.                                 (* 演習問題 *)

End RconsQ.

(**
# head と last

- head は最初の要素をとりだす（空なら第1引数）。behead はその残りの要素（空なら空）。
- last は最後の要素をとりだす（空なら第1引数）。belast は？

## ``belast' [::] = [::]`` の定義を使う例

see. csm_4_4_x_seq_head_last.v

## ``ohead``

ohead は最初の要素を option型（Some なんとか) で取り出す（空ならNONE）。
*)

Compute ohead [::].                         (* None *)
Compute ohead [:: 1; 2; 3].                 (* Some 1 *)


(**
# size (seq の寸法）
 *)
Section Size.
  
  Variable T : Type.

(**
## size_cons

自明であるが x :: s の寸法は、sの寸法の.+1である。
 *)
  Lemma size_cons (x : T) (s : seq T) : size (x :: s) = (size s).+1.
  Proof.
    done.
  Qed.

(*
## size に関する補題

大抵の関数に関するsizeの補題が証明されているので、使うべきである。
 *)
  Check size_cat
    : forall (T : Type) (s1 s2 : seq T), size (s1 ++ s2) = size s1 + size s2.
  Check size_rcons
    : forall (T : Type) (s : seq T) (x : T), size (rcons s x) = (size s).+1.
  Check size_drop
    : forall (n0 : nat) (T : Type) (s : seq T), size (drop n0 s) = size s - n0.
  Check size_rev : forall (T : Type) (s : seq T), size (rev s) = size s.
  Check size_behead  : forall (T : Type) (s : seq T), size (behead s) = (size s).-1.
(**
このうち、size_behead は直観に反している。``0.-1 = 0`` であることに注意してください。
*)
End Size.

(**
## 空リストとサイズの関係

以下の ``0 < size s`` を ``1 <= size s`` にしても同じ。
「<」は「<=」で定義されているため。
 *)
Locate "_ < _".                            (* "m < n" := leq m.+1 n *)

Section Size1.
(**
重要な補題：寸法0と空リストの関係を示す。
 *)
  Variable T : eqType.
  
  Check size_eq0 : forall (T : eqType) (s : seq T), (size s == 0) = (s == [::]).
  
(**
これの否定を証明しておく。
 *)
  Lemma size_not_eq0 (s : seq T) : (size s != 0) = (s != [::]).
  Proof.
(**
s は 本当は seq_eqType なので「==」と「!=」が使える。
また、右辺は ``~~ (s == [::])`` なので、右辺の書き換えで証明できる。
 *)
      by rewrite size_eq0.
  Qed.

(**
使い方。寸法に関する命題と空リストか判定する命題とを相互に書き換えできる。

splitしているので煩瑣だが、実際の証明では、どちらかの「->」だけを証明することになる。
*)
  Goal forall (s : seq T), (1 <= size s) <-> (s <> [::]).
  Proof.
    move=> s.
    Check lt0n : forall n : nat, (0 < n) = (n != 0). (* 覚えておくとよい。 *)
    rewrite lt0n.
    split=> H.
    - apply/eqP.
        by rewrite -size_not_eq0.
    - move/eqP in H.
        by rewrite size_not_eq0.
  Qed.
  
(**
nilp s は size s == 0 で定義されている。これのリフレクション補題が証明されている。
*)
  Print nilp. (*= fun (T : Type) (s : seq T) => size s == 0 *)
  Check @nilP : forall T s, reflect (s = [::]) (nilp s).

(**
使い方。寸法に関する命題と空リストか判定する命題とを相互に変換（リフレクト）できる。

apply/nilP または move/nilP で、相互に変換できるので便利であろう。
*)
  Goal forall (s : seq T), (1 <= size s) <-> (s <> [::]).
  Proof.
    move=> s.
    Check lt0n : forall n : nat, (0 < n) = (n != 0). (* 覚えておくとよい。 *)
    rewrite lt0n.
    split=> H.
    - by apply/nilP.
    - by apply/nilP.
  Qed.
End Size1.

(**
# cat (++, append) 

## cat に関する補題
*)

Locate "_ ++ _". (* := cat x y : seq_scope (default interpretation) *)

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
Section Append.
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
End Append.

(**
# rev

## 説明

rev は catrev (末尾再帰) を使って定義されている。
 *)
Print rev.
(* Definition rev := catrev ^~ [::] *)
(* Definition rev s := catrev s [::] *)
Print catrev.
(**
fun T : Type =>
fix catrev (s1 s2 : seq T) {struct s1} : seq T :=
  match s1 with
  | [::] => s2
  | x :: s1' => catrev s1' (x :: s2)
  end
*)

Section Lists2.
  Variable A : Type.

(**
## （演習）末尾再帰ではない reverse と rev の同値を証明する。
 *)
  Fixpoint reverse (xs : seq A) :=
  match xs with
  | nil => nil
  | x :: xs' =>
    reverse xs' ++ [:: x] (* rcons にしてもよいが、証明がかなり変わる *)
  end.
  
  Goal forall (s : seq A), rev s = reverse s.
  Proof.
  Admitted.                                 (* 演習問題 *)
  
(**
## Inductive に定義した isreverse と rev の同値を証明する。
*)
  Inductive isreverse : seq A -> seq A -> Prop :=
  | reverse_nil (s : seq A) : isreverse [::] [::]
  | reverse_cons (x : A) (s t : seq A) :
      isreverse s t -> isreverse (x :: s) (t ++ [:: x]).
(**
isreverse (x :: s)  (rcons t x) とすると、証明は少し変わる。
いずれにせよ、Inductiveな定義の中に、複雑な関数を書いてもかまわない。
 *)
  Hint Constructors isreverse.

(**
自明な補題を証明しておく。
*)
  Lemma rev0 : @rev A [::] = [::].
  Proof. done. Qed.
  
  Lemma rev1 (x : A) : @rev A [:: x] = [:: x].
  Proof. done. Qed.
  
  Lemma rev_catrev (s t : seq A) : isreverse s t <-> rev s = t.
  Proof.
    split.
    - elim=> [s' | x s' t' /= H IH].
      + by rewrite /rev.
      + rewrite -IH.
        rewrite -rev1 -rev_cat /=.
        done.
    - elim: s t => //= [t <- | x s IH t' <-].
      + rewrite rev0.
          by apply: reverse_nil.
      + rewrite rev_cons -cats1.
        apply: reverse_cons.
          by apply: IH.
  Qed.
  
(**
## Inductive に定義した isreverse と reverse の同値を証明する。
*)
  Lemma rev_reverse (s t : seq A) : isreverse s t <-> reverse s = t.
  Proof.
    split.
    - elim=> [s' | x s' t' H IHs /=].
      + done.
      + rewrite IHs.
          by rewrite cats1.
    - elim: s t => [s' /= H | x s' IHs /= H1 H2].
      + rewrite -H.
          by apply: reverse_nil.
      + rewrite -H2.
        apply reverse_cons.
          by apply: IHs.
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

Check revK : involutive rev. (* rev (rev s) = s 、 覚えておくこと。 *)

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
# has と all

## 説明

リストのある要素、または、すべての要素に対して、条件が成立する。
 *)

Compute has odd [:: 1; 2; 3].               (* true *)
Compute has odd [:: 2; 4; 6].               (* false *)

Compute all odd [:: 1; 2; 3].               (* false *)
Compute all odd [:: 1; 3; 5].               (* true *)

(**
## forall（∀）や exists（∃）を使った定義

has や all は再帰関数として定義されているが、exists や forall を使った同値な命題もある。
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
Print ex2.
(**
Inductive ex2 (A : Type) (P Q : A -> Prop) : Prop :=
    ex_intro2 : forall x : A, P x -> Q x -> exists2 x : A, P x & Q x
*)
Check forall eT a s, exists2 x : eT, x \in s & a x.
Check forall eT a s, ex2 (fun x : eT => x \in s) (fun x : eT => a x).

(**
参考。普通のexists。

「Coq/SSReflect/MathComp による定理証明」 p.77
*)
Print ex.
(**
Inductive ex (A : Type) (P : A -> Prop) : Prop :=
    ex_intro : forall x : A, P x -> exists y, P y
*)
Check forall eT a s, exists x : eT, a x.
Check forall eT a s, ex (fun x : eT => a x).

(**
## Standard Coq の 命題

Standard Coq の List.v には、インダクティブな命題として、
Exists と Forall が定義されている。それとのリフレクションを定義した例：

https://github.com/suharahiromichi/coq/blob/master/pearl/ssr_list_1.v
 *)

(**
## has と all についての補題
*)

Check has_nil : forall (T : Type) (a : pred T), has a [::] = false. (* hasの定義から *)
Check has_seq1 : forall (T : Type) (a : pred T) (x : T), has a [:: x] = a x.
Check has_cat : forall (T : Type) (a : pred T) (s1 s2 : seq T),
    has a (s1 ++ s2) = has a s1 || has a s2.
Check has_rcons : forall (T : Type) (a : pred T) (s : seq T) (x : T),
    has a (rcons s x) = a x || has a s.

Check all_nil : forall (T : Type) (a : pred T), all a [::] = true. (* allの定義から *)
Check all_seq1 : forall (T : Type) (a : pred T) (x : T), all a [:: x] = a x.
Check all_cat : forall (T : Type) (a : pred T) (s1 s2 : seq T),
    all a (s1 ++ s2) = all a s1 && all a s2.
Check all_rcons : forall (T : Type) (a : pred T) (s : seq T) (x : T),
    all a (rcons s x) = a x && all a s.

(**
# nth
 *)

(**
## nth についての補題
*)

(**
# take と drop
 *)

(**
## take と drop についての補題
*)

(**
# == と \in について （seq_eqType と seq_predType は polymorphicな型）
 *)

(**
## (seq_eqType T_eqType) ... 「==」 が使える

eqType 型クラス（インターフェース）のインスタンスとして seq_eqType を定義している。
すると、seq eT 型 (ただし eT は、eqType のインスタンス） は、== の左右に書けるようになる。
*)
Check [:: 1; 2] : seq nat.
Check [:: 1; 2] : seq_eqType nat_eqType.
Compute [:: 1; 2] == [:: 3; 4].             (* false *)

(**
== の定義として eqseq が使われる。
*)
Check @eqseq : forall T : eqType, seq T -> seq T -> bool.

(*
## (seq_predType T_eqTYpe) ... 「\in」 が使える

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
## 任意の eqType について
 *)
Section In.
  Variable eT : eqType.
  Variable a b c : eT.

  Check [:: a; b; c] : seq eT.
  Check [:: a; b; c] : seq_eqType eT.

  Goal [:: a] == [:: a].
  Proof.
    rewrite eqseq_cons.
    apply/andP.
    done.
  Qed.
  
  Goal a \in [:: a; b; c].
  Proof.
    rewrite !in_cons.
    apply/orP/or_introl.
    done.
  Qed.
End In.

(**
## \in についての補題
 *)

Check in_cons : forall (T : eqType) (y : T) (s : seq T) (x : T),
    (x \in y :: s) = (x == y) || (x \in s).
Check in_nil : forall (T : eqType) (x : T), (x \in [::]) = false.

Check @mem_seq1 : forall (T : eqType) (x y : T),
    (x \in [:: y]) = (x == y).
Check mem_cat : forall (T : eqType) (x : T) (s1 s2 : seq T),
    (x \in s1 ++ s2) = (x \in s1) || (x \in s2).
Check mem_head : forall (T : eqType) (x : T) (s : seq T), x \in x :: s.
Check mem_last : forall (T : eqType) (x : T) (s : seq T), last x s \in x :: s.

Check mem_nth : forall (T : eqType) (x0 : T) (s : seq T) (n : nat),
    n < size s -> nth x0 s n \in s.
Check mem_take : forall (n0 : nat) (T : eqType) (s : seq T) (x : T),
    x \in take n0 s -> x \in s.
Check mem_drop : forall (n0 : nat) (T : eqType) (s : seq T) (x : T),
    x \in drop n0 s -> x \in s.

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
まとめてひとつの [seq ... ] で書けるわけではないので、ネストさせる必要がある。
ネストした例：
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
    by elim : s => //.
Qed.

Check filter_cat
  : forall (T : Type) (a : pred T) (s1 s2 : seq T),
    [seq x <- s1 ++ s2 | a x] = [seq x <- s1 | a x] ++ [seq x <- s2 | a x].
Check filter_rcons
  : forall (T : Type) (a : pred T) (s : seq T) (x : T),
    [seq x <- rcons s x | a x] =
    (if a x then rcons [seq x <- s | a x] x else [seq x <- s | a x]).
                                                       
(**
# foldl と foldr

OCamil と引数の順番が異なることに注意してください。
 *)
Check @foldl : forall T R : Type, (R -> T -> R) -> R -> seq T -> R.
Check @foldr : forall T R : Type, (T -> R -> R) -> R -> seq T -> R.

(**
## foldl と foldr についての補題
*)
Check foldr_cat : forall (T2 R : Type) (f : T2 -> R -> R) (z0 : R) (s1 s2 : seq T2),
    foldr f z0 (s1 ++ s2) = foldr f (foldr f z0 s2) s1.
Check foldl_cat : forall (T R : Type) (f : R -> T -> R) (z : R) (s1 s2 : seq T),
    foldl f z (s1 ++ s2) = foldl f (foldl f z s1) s2.
(**
foldl と foldr は、rev すると同じになる。
*)
Check foldl_rev : forall (T R : Type) (f : R -> T -> R) (z : R) (s : seq T),
    foldl f z (rev s) = foldr (fun (x : T) (y : R) => f y x) z s.

(**
# 場合分け
 *)
Section Case.
  Variable T : Type.
  
(**
## ディフォルトの場合分け

ゴールを ``[::]`` と ``x :: s`` に分ける。
*)

(**
まず、リストの先頭の要素を取り除いた残りを返す関数 tail を定義する。
nilならnilを返すものとする。
*)
  Definition tail (s : seq T) : seq T :=
    match s with
    | _ :: b => b
    | [::] => [::]
    end.
  
(**
補題として、cons x s に対して、上記の関数を適用すると s が得られることを証明する。
 *)
  Lemma tail_cons x s : tail (x :: s) = s.
  Proof.
    done.
  Qed.
  
(**
``size (tail s) < size s`` を証明したい。

s = [::] だと ``size (tail s) = size s`` になるので、``1 <= size s`` の条件をつける。
証明は、s を [::] と x :: s に場合分けして、前者の場合は前提矛盾で成立とする。
*)
  Lemma size_tail_1 s : 1 <= size s -> size (tail s) < size s.
  Proof.
    case: s => [| x s] Hs.          (* [::] と x :: s に分ける。 *)
    
    (* Hs : 0 < size [::] *)
    (* Goal : size (tail [::]) < size [::]  ..... これは使わない。 *)
    - rewrite /= in Hs.
      done.        (* 前提 Hs は矛盾で、ゴールは無条件の成立する。  *)
      
    (* Hs : 0 < size (x :: s) ..... これは使わない。 *)
    (* Goal : size (tail (x :: s)) < size (x :: s) *)
    - rewrite tail_cons.                    (* 単に /= でもよい。 *)
      rewrite size_cons.                    (* 単に /= でもよい。 *)
      (* size s < (size s).+1 *)
      done.
  Qed.

(**
## 自然数について類似な例

``n / n = 1`` を証明したいが、n = 0 なら ``0 / 0 = 0`` で成立しないので、
``0 < n`` の条件をつける。
 *)
  Lemma divNN (n : nat) : 0 < n -> n %/ n = 1.
  Proof.
    case: n => [| n ] Hn.
    (* Hn : 0 < 0 *)
    - done.                                 (* 前提矛盾 *)
      
    (* Hn : 0 < n.+1 *)
    (* n.+1 %/ n.+1 = 1 *)
    - rewrite -{1}[n.+1]mul1n.
      rewrite -[1 * n.+1]addn0.
      (* Goal : (1 * n.+1 + 0) %/ n.+1 = 1 *)
      Check divnMDl : forall q m d : nat, 0 < d -> (q * d + m) %/ d = q + m %/ d.
      rewrite divnMDl.
      (* Goal : 1 + 0 %/ n.+1 = 1 *)
      + done.
      (* Goal : 0 < n.+1 *)
      + done.                           (* 前提 Hn を使う。 *)        
  Qed.
  
(**
## lastP

ゴールを ``[::]`` と ``rcons s x`` に分ける。
 *)
  
(**
まず、リストの最後の要素を取り除いた残りを返す関数 init を定義する。
nilならnilを返すものとする。
*)
  Definition init (s : seq T) : (seq T) := rev (tail (rev s)).
  
(**
補題として、rcons s x に対して、上記の関数を適用すると s が得られることを証明する。
 *)
  Lemma init_rcons s x : init (rcons s x) = s.
  Proof.
      by rewrite /init rev_rcons /tail revK.
  Qed.
  
(**
``size (init s) < size s`` を証明したい。

s = [::] だと ``size (init s) = size s`` になるので、``1 <= size s`` の条件をつける。
証明は、s を [::] と rocns s x に場合分けして、前者の場合は前提矛盾で成立とする。
*)
  Lemma size_init_1 s : 1 <= size s -> size (init s) < size s.
  Proof.
    case/lastP: s => [| s x] Hs.    (* [::] と rcons s x に分ける。 *)

    (* Hs : 0 < size [::] *)
    (* Goal : size (init [::]) < size [::]   ..... これは使わない。 *)
    - rewrite /= in Hs.                     (*  *)
      done.        (* 前提 Hs は矛盾で、ゴールは無条件の成立する。  *)
      
    (* Hs : 0 < size (rcons s x) ..... これは使わない。 *)
    (* Goal : size (init (rcons s x)) < size (rcons s x) *)
    - rewrite init_rcons.
      rewrite size_rcons.
      (* size s < (size s).+1 *)
      done.
  Qed.
  
(**
## 補足 : init' を直接定義した場合、カスタムインダクションを使う
*)
  Require Import Recdef.                      (* Function コマンド *)
  Function init' (s : seq T) : (seq T) :=
    match s with
    | [::] => [::]
    | [:: x] => [::]
    | x' :: s => x' :: init' s
    end.
  Check init'_ind.
  Check init'_equation.
  
  Lemma size_init'_1 s : 1 <= size s -> size (init' s) < size s.
  Proof.
    functional induction (init' s).
    - done.
    - done.
    - move=> Hs /=.
      (* Hs : 0 < size s0 -> size (init' s0) < size s0 *)
      (* Goal : (size (init' s0)).+1 < (size s0).+1 *)
      Check ltnS : forall m n : nat, (m < n.+1) = (m <= n).
      (* ここで、 m := m.+1 のとき、 (m.+1 < n.+1) = (m.+1 <= n) = (m < n) となる。 *)
      (* ltnSのマジックは、csm_4_3_x_eq0.v を参照のこと。 *)
      rewrite ltnS.
      (* Goal : size (init' s0) < size s0 *)
      apply: IHl.
      case: s0 y Hs.
      + done.                               (* s0 が [::] *)
      + move=> x s _ Hs.                    (* s0 が x :: s *)
        done.
  Qed.
End Case.

Compute tail [::].                          (* [::] *)
Compute tail [:: 1; 2; 3].                  (* [:: 2; 3] *)

Compute init [::].                          (* [::] *)
Compute init [:: 1; 2; 3].                  (* [:: 1; 2] *)

Compute init' [::].
Compute init' [:: 1; 2; 3].

(**
# 特別な帰納法
 *)

(**
## last_ind

rcons でする帰納法である。
*)
Check last_ind
  : forall (T : Type) (P : seq T -> Type),
    P [::]                                  (* 帰納法の基底 *)
    ->
    (forall (s : seq T) (x : T), P s        (* 帰納法の仮定 *)
                                 ->
                                 P (rcons s x)) (* 証明するべきもの *)
    ->
    forall s : seq T, P s.                  (* 結論 *)

Section FoldLeft.
  Variables (T R : Type) (f : R -> T -> R).
  
(**
foldl と foldr が rev で、同じ結果になることを証明する。
  *)
  Lemma foldl_rev (z : R) (s : seq T) :
    foldl f z (rev s) = foldr (fun x z => f z x) z s.
  Proof.
    (* elim/last_ind : s z => [| s x IHs] z. *)
    move: s z.
    apply: last_ind => [| s x IHs] z.
    
(*
Goal : foldl f z (rev [::]) = foldr (fun z x => f x z) z [::]
 *)
    - rewrite /=.                        (* 第3引数が [::] である。 *)
      done.
      
    (* 
IHs : forall z : R, foldl f z (rev s) = foldr (fun z x => f x z) z s.
Goal : foldl f z (rev (rcons s x)) = foldr (fun z x => f x z) z (rcons s x)

``foldl f z (rev s) = ... `` であると仮定して、証明したいのは、
``foldl f z (rev (rcons s x)) = ...`` であるが、左辺の x を第3引数の外に出すと、
``foldl (f z x) s = ... `` となる。これが成立することを証明する。
     *)
    (* ゴールの左辺 *)
    rewrite rev_rcons.
    rewrite [LHS]/=.
    (* ゴールの右辺 *)
    rewrite -cats1.
    rewrite foldr_cat.
    rewrite [RHS]/=.
    rewrite -IHs.
    done.
  Qed.
End FoldLeft.

(**
## map2 の帰納法

ふたつのリストを引数にとる場合の帰納法である。
*)
Check @seq_ind2
  : forall (S T : Type) (P : seq S -> seq T -> Type),
    P [::] [::]                             (* 帰納法の基底 *)
    ->
    (forall (x : S) (y : T) (s : seq S) (t : seq T), (* 帰納法の仮定 *)
        size s = size t -> P s t
        (* ^^^^^^^^^^^  *)
        ->
        P (x :: s) (y :: t))                (* 証明するべきもの *)
    ->
    forall (s : seq S) (t : seq T), size s = size t -> P s t. (* 結論 *)

(**
古い版では seq2_ind だった。
seq_ind2 になったときに帰納法の仮定に寸法が追加され、「弱まった」が使い易くなった。
ただし、今回は仮定は使っていません。
 *)
Lemma seq2_ind T1 T2 (P : seq T1 -> seq T2 -> Type) :
  P [::] [::] -> (forall x1 x2 s1 s2, P s1 s2 -> P (x1 :: s1) (x2 :: s2)) ->
  forall s1 s2, size s1 = size s2 -> P s1 s2.
Proof.
    by move=> Pnil Pcons; elim=> [|x s IHs] [] //= x2 s2 [] /IHs/Pcons.

  Restart.
  move=> Pnil Pcons s1 s2.
  elim: s1 s2 => [|x s IHs].
  - move=> [] //=.
  - move=> [] //=.
    move=> x2 s2 [].
    move/IHs/Pcons.                  (* スタックトップにapplyする。 *)
    done.
Qed.

Lemma seq2_ind T1 T2 (P : seq T1 -> seq T2 -> Type) :
  P [::] [::] -> (forall x1 x2 s1 s2, P s1 s2 -> P (x1 :: s1) (x2 :: s2)) ->
  forall s1 s2, size s1 = size s2 -> P s1 s2.
Proof. by move=> Pnil Pcons; elim=> [|x s IHs] [] //= x2 s2 [] /IHs/Pcons. Qed.

Section Map2_Mask.
  Variable T : Type.
(**
### mask 関数の証明

seq bool で seq T をマスクする mask 関数に関する証明に使う。
 *)
  Compute mask [:: true; false; true] [:: 1; 2; 3]. (* [:: 1; 3] *)
  
(**
#### size_mask
*)
  Goal forall (m : seq bool) (s : seq T),   (* size_mask *)
      size m = size s -> size (mask m s) = count id m. (* true の数を数える。 *)
  Proof.
    apply: seq_ind2 => // x m s t /= Hs IHs.
    rewrite -IHs.
    case: ifP => Hx /=.
    - rewrite IHs.
      done.
    - rewrite add0n.
      done.
  Qed.

(**
#### mask_cat.
*)
  Goal forall (m1 m2 : seq bool) (s1 s2 : seq T), (* mask_cat *)
      size m1 = size s1 -> mask (m1 ++ m2) (s1 ++ s2) = mask m1 s1 ++ mask m2 s2.
  Proof.
    move=> m1 m2 s1 s2.
    move: m1 s1.
    (* ゴールのスタックに、m1 s1 と size を残すことに注意！ *)
    apply: seq_ind2.
    - by move=> /=.
    - move=> /=.
      move=> x y m s /= Hs IHs.
      (* ``if x then .... else ...`` の then と else で場合分けする。  *)
      case: ifP => Hx.
      + rewrite IHs.                        (* x = true の場合 *)
        done.
      + rewrite IHs.                        (* x = false の場合 *)
        done.
  Qed.
End Map2_Mask.

(**
## map2 関数の定義

MathComp には map2 はないので定義してみる。
*)
Section Map2_Def.
  Variable T : Type.
  
  Fixpoint map2 op (s1 s2 : seq T) : seq T :=
    match s1, s2 with
    | [::], _ => [::]
    | _, [::] => [::]
    | (x1 :: s1), (x2 :: s2) => (op x1 x2) :: map2 op s1 s2
    end.
End Map2_Def.

Check map2 addn.
Compute map2 addn [:: 0; 1; 1; 2; 3; 5; 8] [:: 1; 1; 2; 3; 5; 8].

Section Map2_Lemma.
  Variable T : Type.
(**
### map2_cons
*)  
  Lemma map2_cons f (x1 x2 : T) (s1 s2 : seq T) :
    map2 f (x1 :: s1) (x2 :: s2) = f x1 x2 :: map2 f s1 s2.
  Proof.
      by [].
  Qed.
  
(**
### map2_cat
*)  
  Lemma map2_cat f (s11 s12 s21 s22 : seq T) :
    size s11 = size s21 -> 
    map2 f (s11 ++ s12) (s21 ++ s22) = map2 f s11 s21 ++ map2 f s12 s22.
  Proof.
    move: s11 s21.
    (* ゴールのスタックに、s11 s21 と size を残すことに注意！ *)
    apply: seq_ind2.
    - move=> /=.
      done.
    - move=> /=.
      move=> x1 x2 s11 s21 Hsize IHs.
      rewrite IHs.
      done.
  Qed.    
End Map2_Lemma.

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

(**
# 演習の答え
*)

Section RconsA.
  Variable T : Type.
  
(**
（演習）両者が同値であることを証明してください。
*)
  Goal forall (s : seq T) (z : T), rcons s z = rcons' s z.
  Proof.
    move=> s z.
    elim: s => //.
    move=> a s IH /=.
      by rewrite IH /rcons' /=.

    Restart.
    move=> s z.
      by rewrite /rcons' cats1.             (* 実はMathCompに補題がある。*)
  Qed.
End RconsA.

Section ReverseA.
  Variable A : Type.

(**
## （演習）末尾再帰ではない reverseと rev の同値を証明する。
 *)
  Goal forall (s : seq A), rev s = reverse s.
  Proof.
    elim => // a s IHs /=.
    rewrite -IHs.
    rewrite -rev1 -rev_cat /=.
    done.
  Qed.

(**
## rcons を使使って reverse' を定義する場合：
 *)
  Fixpoint reverse' (xs : seq A) :=
  match xs with
  | nil => nil
  | x :: xs' =>
    rcons (reverse' xs') x
  end.
  
  Goal forall (s : seq A), rev s = reverse' s.
  Proof.
    elim/last_ind => // a s IHs.
    (* rev の中に rcons が出現するので、この場合が簡単にならない。 *)
    Undo 1.
    
    elim => // a s IHs /=.
    rewrite -IHs.
    rewrite /rev.
    rewrite !catrevE !rev_cons !cats0.
    done.
  Qed.
End ReverseA.

(* END *)
