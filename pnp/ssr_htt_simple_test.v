(* とても簡単な例を作ってみた。 *)

Require Import ssreflect ssrbool ssrnat eqtype seq ssrfun.

Add LoadPath "./../htt".
Require Import prelude pred pcm unionmap heap heaptac
        stmod stsep stlog stlogR.  

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

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
  heval=> acc.                              (* acc <-- alloc 1 をheapに。 *)
  rewrite unitR.                            (* x \+ Unit を x *)
  Search (verify _ _ _).
  apply: bnd_readR => /=.
  apply: bnd_deallocR => /=.
  apply: val_ret => /=.
  by [].                                    (* heval. だけでもよい。 *)
Qed.

(* END *)
(* http://ilyasergey.net/pnp/ *)
