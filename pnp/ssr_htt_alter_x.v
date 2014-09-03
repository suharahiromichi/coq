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

(** * Structuring the program verification in HTT *)

(* NOTE: the current implementation of HTT does not support
value/type dependencies in the logical variables (e.g., {T (x: T)}),
so such cases won't be properly handled by the ghR lemma. *)

Program Definition alter_x A (x : ptr) (v : A): 
  {y (Y : nat)}, 
  STsep (fun h => exists B (w : B), h = x :-> w \+ y :-> Y,
           [vfun (_: unit) h => h = x :-> v \+ y :-> Y]) := 
  Do (x ::= v).

Next Obligation.
  apply: ghR.                               (* y と Y を外に出す。 *)
  
  move=> h1 [y Y][B][w] H.                  (* h1 は前提のheap *)
  (* H は、h1 = ......  *)
  rewrite H.                                (* h1 を展開する。 *)
  move=> _ /=.                              (* .1 と .2 を計算する。 *)

  (* 「verify 前提のheap 命令文 実行結果」 のかたちになる。  *)
  Search (verify _ (_ ::= _) _).
  apply: val_write => _ /=.
  by [].
(* 代わりに by heval. でもよい。 *)
Qed.

(* END *)
