(**
Coqでcall/cc（Coqで継続モナド、その2）
===============================

2014_05_17 @suharahiromichi

2014_05_18 @suharahiromichi 「証明」の部分を見直した


継続モナドの続きとして、
前回（文献1.）にも定義してあったcall/ccを使ってみる。
例題は今回も文献2.からいただいています。

本資料のソースコードは以下にあります。

https://github.com/suharahiromichi/coq/blob/master/ssr/ssr_monad_callcc.v
*)

Require Import ssreflect ssrbool ssrnat seq.

(**
# 継続モナド

## 定義（再掲）
*)
Definition MCont R A := (A -> R) -> R.

Definition bind {R A : Type} (c : MCont R A)
           (f : A -> MCont R A) : MCont R A :=
  fun (k : A -> R) => c (fun (a : A) => f a k).

Definition ret {R A : Type} (a : A) : MCont R A :=
  fun k => k a.

(* call/cc、文献3の定義を参考にした。 *)
Definition callcc {R A B : Type}
           (f : (A -> MCont R B) -> MCont R A) : MCont R A :=
  fun (k : A -> R) => f (fun (a : A) => fun _ => k a) k.
Check callcc.
(**
    : ((A -> MCont R B) -> MCont R A) -> MCont R A

call/ccの型は、モナドの部分を除いて見ると、
古典論理を扱うときの「パースの公理」に対応する。

     ((P -> Q) -> P) -> P
*)

(**
演算子と、do記法も定義しておく。
*)
Notation "c >>= f" :=
  (bind c f)
    (at level 42, left associativity).

Notation "s1 >> s2" :=
  (s1 >>= fun _ => s2)
    (at level 42, left associativity).

Notation "'DO' a <- A ; b <- B ; C 'OD'" :=
  (A >>= fun a => B >>= fun b => C)
    (at level 100, no associativity).

Notation "'DO' A ; B ; C 'OD'" :=
  (A >> B >> C)
    (at level 100, no associativity).

(**
# 例題

## 大域脱出の例（文献2.）
 *)
Definition bar1 (cont : nat -> MCont nat nat) := ret 1 : MCont nat nat.
Definition bar2 (cont : nat -> MCont nat nat) := cont 2 : MCont nat nat.
Definition bar3 (cont : nat -> MCont nat nat) := ret 3 : MCont nat nat.

Definition foo (cont : nat -> MCont nat nat) :=
  DO
    bar1 cont;
    bar2 cont;                              (* !! *)
    bar3 cont
  OD.

Definition test := callcc (fun k => foo k) id.
Eval cbv in test.                           (* 2 *)

(**
## flatten list

2次元リストを1次元にする。ただし、空リストがあったら空リストを返す（文献2.）。
*)

(**
### モナドを使わない定義
 *)
Fixpoint flatten_cps (l : seq (seq nat)) : MCont (seq nat) (seq nat) :=
  fun cont =>
    match l with
      | [::]      => cont [::]
      | [::] :: _ => [::]                   (* !! *)
      | x :: xs   => flatten_cps xs (fun y => cont (x ++ y))
    end.

Eval cbv in flatten_cps [:: [:: 1;2];[:: 3;4];[:: 5;6]] id.
Eval cbv in flatten_cps [:: [:: 1;2];[:: 3;4];[::];[:: 5;6]] id. (* [::] *)
Eval cbv in flatten_cps [:: [:: 1;2];[::];[:: 3;4];[:: 5;6]] id. (* [::] *)

(**
### モナドを使う定義
 *)
Fixpoint flatten' (k : seq nat -> MCont (seq nat) (seq nat))
         (l : seq (seq nat)) : MCont (seq nat) (seq nat) :=
  match l with
    | [::]      => ret [::]
    | [::] :: _ => k [::]                   (* !! *)
    | x :: xs   => flatten' k xs >>= fun y => ret (x ++ y)
  end.

Definition flatten_callcc (l : seq (seq nat)) : MCont (seq nat) (seq nat) :=
  callcc (fun (k : seq nat -> MCont (seq nat) (seq nat)) => flatten' k l).

Eval cbv in flatten_callcc [:: [:: 1;2];[:: 3;4];[:: 5;6]] id.
Eval cbv in flatten_callcc [:: [:: 1;2];[:: 3;4];[::];[:: 5;6]] id. (* [::] *)
Eval cbv in flatten_callcc [:: [:: 1;2];[::];[:: 3;4];[:: 5;6]] id. (* [::] *)

(**
以上で、継続モナドに関連してのcall/ccの話は終わりである
（flatten_cpsとflatten_callccの等価の証明も大変そうなので）。
しかし、Coqでcall/ccという表題をつけたからには、
古典論理の定理をcall/ccを使って証明しなければいけないだろう。


# 二重否定の除去の証明

「二重否定の除去」とは、任意のP:Propに対して以下が成立することである。

    ~ ~ P -> P

ここで、~P は P->False であるから以下と同じである。

    ((P -> False) -> False) -> P

さらに、モナドを使ったcallccの定義にあわせて、モナドにしてみる（恣意的！）。

    (P -> MCont R False) -> MCont R False) -> MCont R P

「二重否定の除去」は古典論理の範疇に属する定理だから、
何かの規則を追加しないとCoqでは証明できない。
ここでは、callccを使うことで証明してみる。
*)

Axiom exfalso_with_monad :
  forall R (P : Prop), MCont R False -> MCont R P.

Theorem double_negative_elimination_joke :
  forall R (P : Prop),
    ((P -> MCont R False) -> MCont R False) -> MCont R P.
Proof.
  move=> R P HPFF.
  have HPFP : ((P -> MCont R False) -> MCont R P).
    move=> HPF.
    apply HPFF in HPF.
    by apply exfalso_with_monad.
  Check @callcc R P False.
  by apply (@callcc R P False) in HPFP.
Qed.

Print double_negative_elimination_joke.
(**
中身は以下のようなものである。実行してもなにも出てこない。

    double_negative_elimination_joke = 
    fun (R : Type) (P : Prop) (HPFF : (P -> MCont R False) -> MCont R False) =>
    ssr_have ((P -> MCont R False) -> MCont R P)
      (fun HPF : P -> MCont R False =>
       (fun HPF0 : MCont R False => exfalso_with_monad R P HPF0) (HPFF HPF))
      (fun HPFP : (P -> MCont R False) -> MCont R P =>
       (fun HPFP0 : MCont R P => HPFP0) (callcc HPFP))
         : forall (R : Type) (P : Prop),
           ((P -> MCont R False) -> MCont R False) -> MCont R P
*)

(**
本章の内容は半ば冗談である。
二重否定除去はパースの公理：
*)
Axiom peirce : forall P Q : Prop, ((P -> Q) -> P) -> P.
(**
を使って証明できる（文献4. 練習問題: classical_axioms）。
なので、上記のように変形をしておけば、callccで
証明できるのは当然である。
*)

(**
補足説明：
この資料の最初の版では「証明」以下のようにしていた。
*)
Theorem double_negative_elimination_joke' :
  forall R (P : Prop),
    ((P -> MCont R False) -> MCont R False) -> MCont R P.
Proof.
  move=> R P HPFF.
  Check @callcc.       (* callccの暗黙の引数 R,A,B に対して、それぞれ *)
  Check @callcc R P False.                  (* R,P,False を与える。 *)
  Check @callcc R False P.                  (* R,False,P を与える。 *)
  
  apply (@callcc R P False) => HPF.
  apply exfalso_with_monad.
  apply (@callcc R False P) => HFP.
    by apply HPFF, HPF.
Qed.
(**
この場合、証明には、

    @callcc R False P : (False -> P) -> False -> False

も必要としていて、「call/ccで証明した」とは言い難かった。
証明を見直すにあたって文献5.を参考にさせていただいた。
*)

(**
# 文献

1. Coqで継続モナド
   http://qiita.com/suharahiromichi/items/f07f932103c28f36dd0e

2. お気楽 Haskell プログラミング入門 ●継続渡しスタイル
   http://www.geocities.jp/m_hiroi/func/haskell38.html

3. モナドのすべて Continuationモナド
   http://www.sampou.org/haskell/a-a-monads/html/contmonad.html

4. Pierce他、梅村他訳「ソフトウエアの基礎」、Coqにおける論理
   http://proofcafe.org/sf/Logic_J.html

5. Playing with Pointers Archived、Classical Axioms in Coq
   http://pwparchive.wordpress.com/2012/09/18/classical-axioms-in-coq-2/
*)

(* END *)
