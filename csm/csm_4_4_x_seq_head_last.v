(**
Coq/SSReflect/MathComp による定理証明

第4章 MathComp ライブラリの基本ファイル

4.4 seq.v --- head, behead, last, belast

試みに belast' [::] = [::] の定義を使って展開する。

======

2020_06_09 @suharahiromichi
 *)

From mathcomp Require Import all_ssreflect.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section belast'.
  
  Variable T : eqType.

  Print head.
(*
fun (T : Type) (x0 : T) (s : seq T) => match s with
                                       | [::] => x0
                                       | x :: _ => x
                                       end
     : forall T : Type, T -> seq T -> T
 *)

  Print behead.
(*
fun (T : Type) (s : seq T) => match s with
                              | [::] => [::]
                              | _ :: s' => s'
                              end
     : forall T : Type, seq T -> seq T
 *)

  Print last.
(*
fun T : Type =>
fix last (x : T) (s : seq T) {struct s} : T :=
  match s with
  | [::] => x
  | x' :: s' => last x' s'
  end
 *)
  
  Fixpoint belast' (s : seq T) : (seq T) :=
    match s with
    | [::] => [::]
    | [:: x] => [::]
    | x' :: s => x' :: belast' s
    end.
  
  (* s の条件が要るのは、ここだけ。 *)
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
  
  Check headI : forall (T : Type) (s : seq T) (x : T),
      rcons s x = head x s :: behead (rcons s x).
  (* last'I は headI と、ちゃんと双対となっている。 *)
  
  Check lastI : forall (T : Type) (x : T) (s : seq T),
      x :: s = rcons (belast x s) (last x s).
  (* これは双対となっていない。 *)
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
  
  Lemma size_behead (s : seq T) : 1 <= size s -> size (behead s) < size s.
  Proof.
      by case: s.
  Qed.
  
(**
s = [::] だと ``size (tbody s) = size s`` になるので、``1 <= size s`` の条件をつける。
証明は、s を [::] と rocns s x に場合分けして、前者の場合は前提矛盾で成立とする。
*)
  Lemma size_belast'' (s : seq T) : 1 <= size s -> size (belast' s) < size s.
  Proof.
    case/lastP: s.
    - rewrite /=.                           (* 0 < 0 -> 0 < 0 、前提矛盾。 *)
      done.
    - move=> s x _.                         (* もう 1 <= size s は不要である。 *)
      rewrite belast'_rcons.
        by rewrite size_rcons.
  Qed.

  Lemma size_belast' (s : seq T) : size (belast' s) = (size s).-1.
  Proof.
    case/lastP: s => // s IHs.
      by rewrite belast'_rcons size_rcons.
  Qed.
  
End size_body.

(* END *)
