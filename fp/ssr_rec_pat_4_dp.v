(* -*- coding: utf-8 -*- *)
From mathcomp Require Import all_ssreflect.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(**
典型的な DP (動的計画法) のパターンを整理 Part 1 ～ ナップサック DP 編 ～
https://qiita.com/drken/items/a5e6fe22863b7992efdb
 *)

(**
# 定義
*)
Section Defs.

  Variable S T : Type.
  
(**
中間計算のドライバ
*)
  Fixpoint map2 (f : S -> S -> S) (s1 s2 : seq S) :=
    match (s1, s2) with
    | (a1 :: s1, a2 :: s2) => f a1 a2 :: map2 f s1 s2
    | ([::], s) => s
    | (s, [::]) => s
    end.

(**
末尾再帰のループ
*)
  Fixpoint refold psi (t : seq T) (s : seq S) : seq S :=
    match t with
    | [::] => s
    | x :: t' => refold psi t' (psi x s)
  end.

(**
2引数のoption_map。Noneを0とする方をつかう。
*)
  Variable A B C : Type.
  
  Definition option_map2 (f : A -> B -> C) (a : option A) (b : option B) : option C :=
    match (a, b) with
    | (Some a', Some b') => Some (f a' b')
    | _ => None
    end.

  Definition option_map2' (f : A -> A -> A) (a : option A) (b : option A) : option A :=
    match (a, b) with
    | (Some a', Some b') => Some (f a' b')
    | (_, None) => a
    | (None, _) => b
    end.
  
End Defs.

(**
## 部分和問題
*)
Section P1.
  
  Definition psumpsi (m : nat) (s : seq bool) :=
    map2 orb s (ncons m false s).

  Definition psum (t : seq nat) (A : nat) :=
    nth false (refold psumpsi t [:: true]) A.

  Compute psum [:: 7; 5; 3] 10.             (* true *)
  Compute psum [:: 9; 7] 6.                 (* false *)

End P1.

(**
## 0-1ナップザック問題
 *)
Section P2.

(* option 型を使用する例。気持ちがいいが、実際はNoneは不要である。 *)

  Definition knapsackpsi' (x : nat * nat) (s : seq (option nat)) :=
    let (m, n) := x in
    map2 (option_map2' maxn) s (ncons m (Some 0) (map (option_map (addn n)) s)).

  Definition knapsack' (t : seq (nat * nat)) :=
    (refold knapsackpsi' t [:: Some 0]).

  (* 2kg, 8円 *)
  Compute knapsackpsi' (2, 8) [:: Some 0; None; Some 4; Some 7; None; Some 11].
  (*  [:: Some 0; Some 0; Some 8; Some 7; Some 12; Some 15; None; Some 19] *)

  Compute knapsack' [:: (2,3);(1,2);(3,6);(2,1);(1,3);(5,85)]. (* (w,v) *)
(*
    = [:: Some 0; Some 3; Some 5; Some 6; Some 9; Some 85; 
          Some 88; Some 90; Some 91; Some 94; Some 96; Some 97; 
          Some 99; Some 98; Some 100]
*)  
  Compute knapsack' [:: (3,2);(4,3);(1,2);(2,3);(3,6)].
(*
    = [:: Some 0; Some 2; Some 3; Some 6; Some 8; Some 9; 
          Some 11; Some 11; Some 11; Some 13; Some 14; Some 14; 
          Some 14; Some 16]
*)

(* 0 にする例 *)
  
  Definition knapsackpsi (x : nat * nat) (s : seq nat) :=
    let (m, n) := x in map2 maxn s (ncons m 0 (map (addn n) s)).

  Definition knapsack (t : seq (nat * nat)) := refold knapsackpsi t [:: 0].
  
  (* 2kg, 8円 *)
  Compute knapsackpsi (2, 8) [:: 0; 0; 4; 7; 0; 11].
  (* = [:: 0; 0; 8; 8; 12; 15; 8; 19] *)

  Compute knapsack [:: (2,3);(1,2);(3,6);(2,1);(1,3);(5,85)]. (* (w,v) *)
  (* = [:: 0; 3; 5; 6; 9; 85; 88; 90; 91; 94; 96; 97; 99; 98; 100] *)

  Compute knapsack [:: (3,2);(4,3);(1,2);(2,3);(3,6)].
  (* = [:: 0; 2; 3; 6; 8; 9; 11; 11; 11; 13; 14; 14; 14; 16] *)
  
End P2.

(* END *)
