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

(**
Hoare Type とは、依存型に基づいて、
Hoareスタイルのspecificationをコード化したもの。
 *)
(* All these observation resulted in a series of works on Hoare Type
Theory (or just HTT), which defines a notion of an indexed Hoare monad
(or, Hoare type) as a mechanism to encode Hoare-style specifications
as dependent types and reduce the verification of effectful 
progress to proving propositions in Coq. *)

(** * Structuring the program verification in HTT *)

(* NOTE: the current implementation of HTT does not support
value/type dependencies in the logical variables (e.g., {T (x: T)}),
so such cases won't be properly handled by the ghR lemma. *)

(** Hoare Type  *)
Definition alter_x_tp A (x : ptr) (v : A) :=
  (* Aは任意の型の意味。 *)
  {(y : ptr) (Y : nat)},                    (* Y の型はなんでもいい。 *)
  STsep (
      (** pre-condition : heap -> Prop *)
      fun h => exists B (w : B), h = x :-> w \+ y :-> Y,
      (** post-condition : unit -> heap -> Prop
          この場合、実行結果は unit（いわゆるvoid）である。 *)
      [vfun (tt : unit) h => h = x :-> v \+ y :-> Y]
    ).

(** 証明するもの。 *)
Program Definition alter_x A (x : ptr) (v : A) : alter_x_tp x v :=
  Do (x ::= v).                             (* 命令文 *)
Next Obligation.
  apply: ghR.                               (* y と Y を外に出す。 *)
  
  move=> h1 [y Y] [B] [w] H.                (* h1 はpre-condのheap *)
  (* H は、h1 = ......  *)
  rewrite H.                                (* h1 を展開する。 *)
  move=> _ /=.                              (* .1 と .2 を計算する。 *)

  (* 「verify 前提のheap 命令文 実行結果」 のかたちになる。  *)
  Search (verify _ (_ ::= _) _).
  apply: val_writeR => _ /=.                (* validの項は捨ててよい。 *)
  by [].
(* 代わりに by heval. でもよい。 *)
Qed.

(* END *)
