(* とても簡単な例を作ってみた。 *)
(* http://ilyasergey.net/pnp/ *)

Require Import ssreflect ssrbool ssrnat eqtype seq ssrfun.

Add LoadPath "./../htt".
Require Import prelude pred pcm unionmap heap heaptac
        stmod stsep stlog stlogR.  

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** 最も簡単な例 *)
Definition test1_tp (N : nat) :=
  STsep ([Pred h | h = Unit], 
         [vfun res h => res = N /\ h = Unit]).

Program Definition test1 (N M : nat) : test1_tp N :=
  Do (n <-- alloc N;
      m <-- alloc M;
      res <-- !n;
      dealloc n;;
      dealloc m;;
      ret res).
Next Obligation.
  rewrite /conseq => /=.
  move=> i ->.                              (* rewriteは、 i = Unit  *)
  heval => n.                               (* heval. だけでもよい。 *)
  rewrite unitR.                            (* x \+ Unit を x *)
  heval => m.
  apply: bnd_readR => /=.
  apply: bnd_deallocR => /=.
  apply: bnd_deallocR => /=.
  apply: val_ret => /=.
  heval.
Qed.

(* ふたつのポインタに対して、なにもしない。 *)
Definition test2_tp (n m : ptr) (N M : nat) :=
  STsep ([Pred h |                 h = n :-> N \+ m :-> M], 
         [vfun res h => res = N /\ h = n :-> N \+ m :-> M]).

Program Definition test2 (n m : ptr) (N M : nat) : test2_tp n m N M :=
  Do (res <-- !n;
      ret res).
Next Obligation.
  rewrite /conseq => /=.
  move=> i ->.
  heval.
Qed.

(* ふたつのポインタに対して、一方の内容を上書きする。 *)
Definition test3_tp (n m : ptr) (N M : nat) :=
  STsep ([Pred h |                 h = n :-> N \+ m :-> M], 
         [vfun res h => res = N /\ h = n :-> N \+ m :-> N]).

Program Definition test3 (n m : ptr) (N M : nat) : test3_tp n m N M :=
  Do (n' <-- !n;
      m ::= n';;
      ret n').
Next Obligation.
  rewrite /conseq => /=.
  move=> i ->.
  heval.
Qed.

Program Definition test3' (n m : ptr) (N M : nat) : test3_tp n m N M :=
  Do (n' <-- read nat n;
      m ::= n';;
      ret n').
Next Obligation.
  rewrite /conseq => /=.
  move=> i ->.
  heval.
Qed.

Definition test4_tp (n m : ptr) (N M : nat) :=
  STsep ([Pred h |                 h = n :-> N \+ m :-> M], 
         [vfun res h => res = N /\ h = n :-> N \+ m :-> N]).

Program Definition test4 (n m : ptr) (N M : nat) : test4_tp n m N M :=
  Do (n' <-- !n;
      m' <-- read nat m;                    (* Hint *)
      n ::= n';;
      m ::= n';;
      ret n').
Next Obligation.
  admit.
Qed.

(* swap *)
Definition swap_tp (n m : ptr) (N M : nat) :=
  STsep ([Pred h |                 h = n :-> N \+ m :-> M], 
         [vfun res h => res = N /\ h = n :-> M \+ m :-> N]).

Program Definition swap (n m : ptr) (N M : nat) : swap_tp n m N M :=
  Do (n' <-- !n;
      p <-- alloc(n');

      m' <-- read nat m;
      n ::= m';;

      t' <-- read nat p;
      m ::= t';;

      dealloc(p);;
      ret n').
Next Obligation.
  admit.
Qed.

  (* 
Obligation 1 of swap_acc:
ptr -> ptr -> unit -> nat -> ptr -> Type.
が残るのは、: の右の型がおかしいから。
うまくいった例であっても、: の右の型を省くと同じ事象がおきる。
 *)


(* END *)
