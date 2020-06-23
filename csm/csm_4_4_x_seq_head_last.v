(**
Coq/SSReflect/MathComp による定理証明

第4章 MathComp ライブラリの基本ファイル

4.4 seq.v --- head, behead, last, belast

- head は最初の要素をとりだす。behead はその残りの要素。空なら空。
- last は最後の要素をとりだす。belast は？

そこで試みに belast' [::] = [::] の定義を使って展開する。

======

2020_06_09 @suharahiromichi
 *)

From mathcomp Require Import all_ssreflect.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section belast'.
  
  Variable T : eqType.

  Print head. (* head x0 s == the head (zero'th item) of s if s is non-empty, else x0 *)
  Print behead. (* behead s == s minus its head if s is non-empty, else [::]  *)
  Print last. (* last x s == the last element of (x :: s), which is non-empty *)
(**
last の定義は、the last of s if s is non-empty, else x と同じなので納得できる。
 *)

  Print belast.       (* belast x s == (x :: s) minus its last item *)
(**
belast の定義は納得いかないし、そもそも使えない！
 *)

(**
そこで試みに belast' [::] = [::] の定義にしてみる。すなわち、

belast' s == s minus its last if s is non-empty, else [::]
*)
  Fixpoint belast' (s : seq T) : (seq T) :=
    match s with
    | [::] => [::]
    | [:: x] => [::]
    | x' :: s => x' :: belast' s
    end.
  
  (* s の条件が要るのは、ここだけ。零割りを避けるようなもの。。。 *)
  Lemma belast'_cons (s : seq T) (x : T) :
    1 <= size s -> belast' (x :: s) = x :: belast' s.
  Proof.
      by elim: s.
  Qed.

  Lemma belast'_rcons (s : seq T) (x : T) : belast' (rcons s x) = s.
  Proof.
    elim: s => // a s IHs.
    rewrite rcons_cons.
    rewrite belast'_cons; last by rewrite size_rcons.
      by rewrite IHs.
  Qed.
  
  Lemma lastI' (x : T) (s : seq T) :
    x :: s = rcons (belast' (x :: s)) (last x s).
  Proof.
    case/lastP : s => // s x'.
    rewrite last_rcons.
    rewrite belast'_cons; last by rewrite size_rcons.
      by rewrite belast'_rcons.
  Qed.
  
(**
last'I は headI と、ちゃんと双対となっている。
cons - rcons,      head - last,    behead - belast'
    
もとの belast の定義のほうは、双対になっていない。
 *)
  Check headI : forall (T : Type) (s : seq T) (x : T),
      rcons s x = head x s :: behead (rcons s x).
  
  Check lastI : forall (T : Type) (x : T) (s : seq T),
      x :: s = rcons (belast x s) (last x s).
End belast'.

Compute head 0 [:: 1;2;3].                  (* 1 *)
Compute head 0 [::].                        (* 0 *)

Compute behead [:: 1;2;3].                  (* [:: 2; 3] *)
Compute behead [::].                        (* [::] *)

Compute last 0 [:: 1;2;3].                  (* 3 *)
Compute last 0 [::].                        (* 0 *)

Compute belast' [:: 1;2;3].                 (* [:: 1; 2] *)
Compute belast' [::].                       (* [::] *)

Section lemma_belast'.

  Variable T U : eqType.
  
  Lemma belast'_map (f : T -> U) (s : seq T) :
    belast' (map f s) = map f (belast' s).
  Proof.
    case/lastP : s => // s y.
    rewrite map_rcons.
    by rewrite !belast'_rcons.
  Qed.
  
End lemma_belast'.

Section size_body.

  Variable T : eqType.
  
(**
s = [::] だと ``size (tbody s) = size s`` になるので、``1 <= size s`` の条件をつける。
証明は、s を [::] と rocns s x に場合分けして、前者の場合は前提矛盾で成立とする。
*)
  Goal forall (s : seq T), 1 <= size s -> size (belast' s) < size s.
  Proof.
    case/lastP.
    - rewrite /=.                           (* 0 < 0 -> 0 < 0 、前提矛盾。 *)
      done.
    - move=> s x _.                         (* もう 1 <= size s は不要である。 *)
      rewrite belast'_rcons.
        by rewrite size_rcons.
  Qed.

(**
より、MathComp らしい補題です。以下に注意してください；

beelast' [::] = [::]    ,       0.-1 = 0
*)  
  Lemma size_belast' (s : seq T) : size (belast' s) = (size s).-1.
  Proof.
    case/lastP: s => // s IHs.
      by rewrite belast'_rcons size_rcons.
  Qed.
  
  Check size_behead : forall (T : Type) (s : seq T), size (behead s) = (size s).-1.
  
End size_body.

(* END *)
