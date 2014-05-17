(**
Coqでcall/cc (継続モナドの続き)
===============================

2014_05_18 @suharahiromichi


文献1.に紛れ込ませておいたcall/ccの定義を使ってみる。
今回も例題は文献2.からいただいています。

本資料のソースコードは以下にあります。

https://github.com/suharahiromichi/coq/blob/master/ssr/ssr_monad_callcc.v
*)

Require Import ssreflect ssrbool ssrnat seq.

(**
# 継続モナド

## 定義
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
古典論理を扱うときの「パースの公理」と対応する。

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
以上で、継続モナドの枠でのcall/ccの話は終わりである
（flatten_cpsとflatten_callccの等価の証明も大変そうなので）。
しかし、Coqでcall/ccという表題をつけたからには、
古典論理の定理をcall/ccを使って証明しなければいけないだろう。


# 二重否定の証明

古典論の定理の「二重否定の除去」とは、任意のP:Propに対して以下が成立することである。

    ~ ~ P -> P

ここで、~P は P->False であるから以下と同じである。

    ((P -> False) -> False) -> P

さらに、モナドを使ったcallccの定義にあわせて、MContを挿入してみる（恣意的）。

    (P -> MCont R False) -> MCont R False) -> MCont R P

これを、callccを使って証明してみる。callccは以下の型をとる、
 
    (P -> MCont R Q) -> MCont R P) -> MCont R P
*)

Axiom exfalso_with_monad : 
  forall R (P : Prop), MCont R False -> MCont R P.

Theorem double_negative_elimination_joke :
  forall R (P : Prop),
    ((P -> MCont R False) -> MCont R False) -> MCont R P.
Proof.
  move=> R P HPFF.
  Check @callcc.                            (* callccの暗黙の引数 R,A,B に対して、それぞれ *)
  Check @callcc R P False.                  (* R,P,False を与える。 *)
  Check @callcc R False P.                  (* R,False,P を与える。 *)
  
  apply (@callcc R P False) => HPF.
  apply exfalso_with_monad.
  apply (@callcc R False P) => HFP.
    by apply HPFF, HPF.
Qed.

Print double_negative_elimination_joke.
(**
中身は以下のようなものである。

    double_negative_elimination_joke = 
    fun (R : Type) (P : Prop) (HPFF : (P -> MCont R False) -> MCont R False) =>
      callcc
        (fun HPF : P -> MCont R False =>
           exfalso_with_monad R P
             (callcc (fun _ : False -> MCont R P => HPFF HPF)))
      : forall (R : Type) (P : Prop),
          ((P -> MCont R False) -> MCont R False) -> MCont R P
*)

(**
前に書いたとおり、二重否定除去はパースの公理：
*)
Axiom peirce : forall P Q : Prop, ((P -> Q) -> P) -> P.
(**
を使って証明できるので、
上記のような恣意的な変形をしておけば証明できるのは当然である。

ただし、パースの公理を使う場合でも同じだが、
二重否定除去を証明する場合は、
次の両方が必要なるだろうことに留意する必要がありそうだ。

    @callcc P False : (P -> False) -> P -> P
    @callcc False P : (False -> P) -> False -> False
*)

(**
# 文献

1. Coqで継続モナド
   http://qiita.com/suharahiromichi/items/f07f932103c28f36dd0e

2. お気楽 Haskell プログラミング入門 ●継続渡しスタイル
   http://www.geocities.jp/m_hiroi/func/haskell38.html

3. モナドのすべて Continuationモナド
   http://www.sampou.org/haskell/a-a-monads/html/contmonad.html
*)

(* END *)
