(* とても簡単な例を作ってみた。 *)
(* http://ilyasergey.net/pnp/ *)

Require Import ssreflect ssrbool ssrnat eqtype seq ssrfun.

Add LoadPath "./../htt".
Require Import prelude pred pcm unionmap heap heaptac
        stmod stsep stlog stlogR.  

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(**
プログラム部分に使える記号：
a <-- e : immutable 変数 (Coq上の変数) a に、eの値を代入する。
!e      : eのポインタの指す先の値を得る。
x ::= e : eの値をポインタxの指す先に代入する。

c1 ;; c2       : c1の結果が捨てられる場合。
x <-- c1 ;  c2 : c1の結果が、xを通してc2に渡される場合。xはimmutable 変数。

We will be using the syntax x ::= e to denote the assignment of a value e to the pointer
bound by x.  Similarly, the syntax !e stands for dereferencing a pointer, whose address is
a value obtained by evaluating a pure expression e.

To account for this, we will be using the syntax x <- c1; c2 (pronounced “bind”) as a
generalization of the sequential composition from Section 8.1.1. The bind first executes
the program c1, then binds this result to an immutable variable x and proceeds to the
execution of the program c2, which can possibly make use of the variable x, so all the
occurrences of x in it are replaced by its value before it starts evaluating. If the
result of c1 is not used by c2, we will use the abbreviation c1 ;; c2 to denote this
specific case.
 *)

(**
型の部分に使える記号：
A \+ B : Aで言及しているポインタと、Bで言及しているポインタが指しているヒープ領域が、
分離されている(エイリアシングがない)。
x :-> y : ポインタxの指し示すヒープの中身は y である。

The notation x :-> y corresponds to the the points-to assertion x → y in the mathematical
representation of separation logic,
*)

(* 最も簡単な例 *)
Definition test1_tp (N : nat) :=
  STsep ([Pred h | h = Unit], 
         [vfun res h => res = N /\ h = Unit]).

Program Definition test1 (N : nat) : test1_tp N :=
  Do (acc <-- alloc N;
      res <-- !acc;
      dealloc acc;;
      ret res).
Next Obligation.
  rewrite /conseq => /=.
  move=> i ->.                              (* rewriteは、 i = Unit  *)
  apply: bnd_allocR => /= x.                (* heval. だけでもよい。 *)
  rewrite unitR.                            (* x \+ Unit を x *)
  apply: bnd_readR => /=.
  apply: bnd_deallocR => /=.
  apply: val_ret => /=.
  by [].                                    (* heval. だけでもよい。 *)
Qed.


(* 最も簡単な関数呼び出しの例 *)

(** ループ不変式 *)
Definition func_inv (n : ptr) (N : nat) h : Prop := 
  exists n' a': nat,
    h = n :-> n' /\ n' = N.

(** 関数部分の証明  *)
Definition func_acc_tp (n : ptr) := 
  unit -> {N},
  STsep (func_inv n N, 
           [vfun (res : nat) h => func_inv n N h /\ res = N]).

Program Definition func_acc (n : ptr) : func_acc_tp n := 
  fun (_ : unit) =>
    Do (n' <-- !n;
        ret n').
Next Obligation. 
  apply: ghR => i N.                        (* conseq を消す。 *)
  case=> n' [a'] []. move=> -> Hi _.        (* case=> n' [a'][->{i}] Hi _.  *)

  Search (verify _ _ _).
  heval.
Qed.

(** 全体の証明  *)
Definition func_tp (N : nat) :=
  STsep ([Pred h | h = Unit], 
         [vfun res h => res = N /\ h = Unit]).

Check func_acc.
Program Definition func (N : nat) : func_tp N :=
  Do (n   <-- alloc N;
      res <-- func_acc n tt;
      dealloc n;;
      ret res).
Next Obligation.
  rewrite /conseq => /=.
  move=> i ->.                              (* rewriteは、 i = Unit  *)
  heval=> n.                                (* n <-- alloc N をheapに。 *)
  rewrite unitR.                            (* x \+ Unit を x *)

  Search _ (verify _ _ _).
  (* (x <-- e1; e2 x) を変形する。 *)
  apply: bnd_seq => /=.

  (* (func_acc n acc tt) を (Do func_acc n acc tt)  *)
  apply: (gh_ex N).

  (* (Do func_acc n acc tt) *)
  apply: val_doR => //.

  (* func_inv n acc N (n :-> N) の証明 *)
  - by exists N, 1.
  (*  *)
  - move=> x m.
    case.
    case=> n'.
    case=> a'.
    case=> H1 _ H2 _.
    (* move=> x m [] [n'] [a'] [] H1 _ H2 _.
       または
       move=> x m [[n'] [a'] [H1] _ H2 _]. *)
    rewrite H1 H2.
    by heval.                               (* e1;; e2;; ret _ *)
Qed.

(* END *)
