(** Programs and Proofs Ilya Sergey *)
(* http://ilyasergey.net/pnp/ *)

(** * 「Hoare Type Theory の基礎」から抜粋 *)
(** * Elements of Hoare Type Theory *)

Require Import ssreflect ssrbool ssrnat eqtype seq ssrfun.

Add LoadPath "./../htt".
Require Import prelude pred pcm unionmap heap heaptac
        stmod stsep stlog stlogR.  

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ふたつのポインタに対して、なにもしない。 *)
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

(** ふたつのポインタに対して、一方の内容を上書きする。 *)
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

(** n' <-- !n ではなく、n' <-- read nat n と「de-sugared」する。 *)
(** p.133 の Hint にあるとおり、そうしないとうまくいかない。  *)
Program Definition test3' (n m : ptr) (N M : nat) : test3_tp n m N M :=
  Do (n' <-- read nat n;                    (* Hint *)
      m ::= n';;
      ret n').
Next Obligation.
  rewrite /conseq => /=.
  move=> i ->.
  heval.
Qed.

(** ふたつのポインタを読み出して、もとにもどす。  *)
Definition test4_tp (n m : ptr) (N M : nat) :=
  STsep ([Pred h |                 h = n :-> N \+ m :-> M], 
         [vfun res h => res = N /\ h = n :-> N \+ m :-> N]).

Program Definition test4 (n m : ptr) (N M : nat) : test4_tp n m N M :=
  Do (n' <-- read nat n;                    (* !n *)
      m' <-- read nat m;                    (* Hint *)
      n ::= n';;
      m ::= n';;
      ret n').
Next Obligation.
  rewrite /conseq => /= _ ->.
  heval.
Qed.

(** Exercise 8.1 swap *)
(** ふたつのポインタを読み出して、swapしてもどす。  *)
Definition swap_tp (n m : ptr) (N M : nat) :=
  STsep ([Pred h |                 h = n :-> N \+ m :-> M], 
         [vfun res h => res = N /\ h = n :-> M \+ m :-> N]).

Program Definition swap (n m : ptr) (N M : nat) : swap_tp n m N M :=
  Do (n' <-- read nat n;                    (* !n *)
      p <-- alloc(n');

      m' <-- read nat m;                    (* !m *)
      n ::= m';;

      t' <-- read nat p;                    (* !p *)
      m ::= t';;

      dealloc(p);;
      ret n').
Next Obligation.
  rewrite /conseq => /= _ ->.
  heval => p.
  heval.
Qed.

(** Exercise 8.2 swap' *)
(** 自動証明を使わないで証明する。 *)
Program Definition swap' (n m : ptr) (N M : nat) : swap_tp n m N M :=
  Do (n' <-- read nat n;                    (* !n *)
      p <-- alloc(n');

      m' <-- read nat m;                    (* !m *)
      n ::= m';;

      t' <-- read nat p;                    (* !p *)
      m ::= t';;

      dealloc(p);;
      ret n').
Next Obligation.
  rewrite /conseq => /= _ ->.
  Search _ (verify _ _ _).
  apply: bnd_readR => /=.
  apply: bnd_allocR => /= p.
  apply: bnd_readR => /=.
  apply: bnd_writeR => /=.
  apply: bnd_readR => /=.
  apply: bnd_writeR => /=.
  apply: bnd_deallocR => /=.
  rewrite joinC unitR.
  Search _ (verify _ _ _) (ret _).
  apply: val_ret => /=.
  by [].
Qed.

(* END *)
