(**
整数割算
========================

@suharahiromichi

2026/10/15
 *)

(**
# はじめに

いろいろな整数割算をみてみる。
計算をすることを前提に。
*)

From mathcomp Require Import all_ssreflect.
From mathcomp Require Import all_algebra.
From mathcomp Require Import ssrZ zify ring lra.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GRing.Theory.         (* mulrA などを使えるようにする。 *)
Import Num.Theory.           (* unitf_gt0 などを使えるようにする。 *)
Import intZmod.              (* addz など *)
Import intRing.              (* mulz など *)
Import Order.Theory.         (* 不等号関連 *)

Open Scope ring_scope.       (* 環の四則演算を使えるようにする。 *)


(**
# いろいろな整数割算

## ユークリッド除算

- 剰余は0または正
- Rocq の ``%/`` と ``%%``
 *)

Definition edivmod (m d : int) := (m %/ d, m %% d)%Z.

(**
例
*)
Compute edivmod 10 3.                       (* 3, 1 *)
Compute edivmod 10 (-3).                    (* -3, 1 *)
Compute edivmod (-10) 3.                    (* -4, 2 *)
Compute edivmod (-10) (-3).                 (* 4, 2 *)

Compute edivmod 0 3.                        (* 0, 0 *)
Compute edivmod 0 (-3).                     (* 0, 0 *)
Compute edivmod 1 3.                        (* 0, 1 *)
Compute edivmod 1 (-3).                     (* 0, 1 *)
Compute edivmod (-1) 3.                     (* -1, 2 *)
Compute edivmod (-1) (-3).                  (* 1, 2 *)

(**
被除数に戻ること。
 *)
Goal forall m d : int, d != 0 ->
                   let: (q, r) := edivmod m d in m = q * d + r.
Proof.
  move=> m d Hd //=.
  lia.
Qed.

(**
剰余の範囲
 *)
Goal forall m d : int, d != 0 ->
                   let: (q, r) := edivmod m d in `|r| < `|d|.
Proof.
  move=> m n Hd //=.
  lia.
Qed.

(**
剰余は0または正
 *)
Goal forall m d : int, d != 0 ->
                   let: (q, r) := edivmod m d in 0 <= r.
Proof.
  move=> m n Hd //=.
  lia.
Qed.

(**
まとめた式
 *)
Goal forall m d : int, d != 0 ->
                   let: (q, r) := edivmod m d in 0 <= r < `|d|.
Proof.
  move=> m n Hd //=.
  lia.
Qed.

(**
## Truncation towards zero division

- 剰余は0または被除数と同符号
- 商が正なら切り捨て、商が負なら切り上げる。
- C言語の ``%%``
*)

Definition tdivmod (m d : int) :=
  let: r := (m %% d)%Z in
  let: q := (m %/ d)%Z in
  if (r == 0) then (q, r)
  else if (m < 0) then
         if (q < 0) then (q + 1, r - d)
         else (q - 1, r + d)
       else (q, r).

(**
例
*)
Compute tdivmod 10 3.                       (* 3, 1 *)
Compute tdivmod 10 (-3).                    (* -3, 1 *)
Compute tdivmod (-10) 3.                    (* -3, -1 *)
Compute tdivmod (-10) (-3).                 (* 3, -1 *)

Compute tdivmod 0 3.                        (* 0, 0 *)
Compute tdivmod 0 (-3).                     (* 0, 0 *)
Compute tdivmod 1 3.                        (* 0, 1 *)
Compute tdivmod 1 (-3).                     (* 0, 1 *)
Compute tdivmod (-1) 3.                     (* 0, -1 *)
Compute tdivmod (-1) (-3).                  (* 0, -1 *)

(**
被除数に戻ること。
 *)
Goal forall m d : int, d != 0 ->
                   let: (q, r) := tdivmod m d in m = q * d + r.
Proof.
  move=> m d Hd.
  rewrite /tdivmod.
  case: ifP; [| case: ifP; [case: ifP |]]; lia.
Qed.

(**
剰余の範囲
 *)
Goal forall m d : int, d != 0 ->
                   let: (q, r) := tdivmod m d in `|r| < `|d|.
Proof.
  move=> m d Hd.
  rewrite /tdivmod.
  do! case: ifP; lia.
Qed.

(**
被除数が0以上なら剰余は0以上、被除数が0未満なら剰余は0以下
 *)
Goal forall m d : int, d != 0 ->
                   let: (q, r) := tdivmod m d in (0 <= m /\ 0 <= r) \/ (m < 0 /\ r <= 0).
Proof.
  move=> m d Hd.
  rewrite /tdivmod.
  do! case: ifP; lia.
Qed.

(**
まとめた式
 *)
Goal forall m d : int, d != 0 ->
                   let: (q, r) := tdivmod m d in
                   if (0 <= m) then 0 <= r < `|d| else - `|d| < r <= 0.
Proof.
  move=> m d Hd.
  rewrite /tdivmod.
  do! case: ifP; lia.
Qed.

(**
## Flooring division

- 剰余は0か除数と同符号。
- 商を切り捨てる。
- Python の ``%%``
*)

Definition fdivmod (m d : int) :=
  let: r := (m %% d)%Z in
  let: q := (m %/ d)%Z in
  if (r == 0) then (q, r)
  else if (d < 0) then (q - 1, r + d)
       else (q, r).

(**
例
*)
Compute fdivmod 10 3.                       (* 3, 1 *)
Compute fdivmod 10 (-3).                    (* -4, -2 *)
Compute fdivmod (-10) 3.                    (* -4, 2 *)
Compute fdivmod (-10) (-3).                 (* 3, -1 *)

Compute fdivmod 0 3.                        (* 0, 0 *)
Compute fdivmod 0 (-3).                     (* 0, 0 *)
Compute fdivmod 1 3.                        (* 0, 1 *)
Compute fdivmod 1 (-3).                     (* -1, -2 *)
Compute fdivmod (-1) 3.                     (* -1, 2 *)
Compute fdivmod (-1) (-3).                  (* 0, -1 *)

(**
被除数に戻ること。
 *)
Goal forall m d : int, d != 0 ->
                   let: (q, r) := fdivmod m d in m = q * d + r.
Proof.
  move=> m d Hd.
  rewrite /fdivmod.
  case: ifP; [| case: ifP]; lia.
Qed.

(**
剰余の範囲
 *)
Goal forall m d : int, d != 0 ->
                   let: (q, r) := fdivmod m d in `|r| < `|d|.
Proof.
  move=> m d Hd.
  rewrite /fdivmod.
  do! case: ifP; lia.
Qed.

(**
除数が0を超えるなら剰余は0以上、除数が0未満なら剰余は0以下
 *)
Goal forall m d : int, d != 0 ->
                   let: (q, r) := fdivmod m d in (0 < d /\ 0 <= r) \/ (d < 0 /\ r <= 0).
Proof.
  move=> m d Hd.
  rewrite /fdivmod.
  do! case: ifP; lia.
Qed.

(**
まとめた式
*)
Goal forall m d : int, d != 0 ->
                   let: (q, r) := fdivmod m d in 0 <= r < d \/ d < r <= 0.
Proof.
  move=> m d Hd.
  rewrite /fdivmod.
  case: ifP; [| case: ifP]; lia.
Qed.

(**
## Symmetry Division

- 剰余は0か商と同符号。ただし、商が0の場合をのぞく（商が0なら剰余は被除数とおなじ）。
- 被除数が正なら商を切り捨て、被除数が負なら商を切り上げる。
 *)

Definition sdivmod (m d : int) :=
  let: r := (m %% d)%Z in
  let: q := (m %/ d)%Z in
  if (r == 0) then (q, r)
  else if (0 <= m) then
         if (d < 0) then (q - 1, r + d)
         else (q, r)
       else
         if (0 < d) then (q + 1, r - d)
         else (q, r).

(**
例
*)
Compute sdivmod 10 3.                       (* 3, 1 *)
Compute sdivmod 10 (-3).                    (* -4, -2 *)
Compute sdivmod (-10) 3.                    (* -3, -1 *)
Compute sdivmod (-10) (-3).                 (* 4, 2 *)

Compute sdivmod 0 3.                        (* 0, 0 *)
Compute sdivmod 0 (-3).                     (* 0, 0 *)
Compute sdivmod 1 3.                        (* 0, 1 *)
Compute sdivmod 1 (-3).                     (* -1, -2 *)
Compute sdivmod (-1) 3.                     (* 0, -1 *)
Compute sdivmod (-1) (-3).                  (* 1, 2 *)


(**
被除数に戻ること。
 *)
Goal forall m d : int, d != 0 ->
                   let: (q, r) := sdivmod m d in m = q * d + r.
Proof.
  move=> m d Hd.
  rewrite /sdivmod.
  do! case: ifP; lia.
Qed.

(**
剰余の範囲
 *)
Goal forall m d : int, d != 0 -> let: (q, r) := sdivmod m d in `|r| < `|d|.
Proof.
  move=> m d Hd.
  rewrite /sdivmod.
  do! case: ifP; lia.
Qed.

(**
商が0を超えるなら剰余は0以上、商が0未満なら剰余は0以下、商が0の場合は剰余は不問。
 *)
Goal forall m d : int, d != 0 -> let: (q, r) := sdivmod m d in
                             (0 < q /\ 0 <= r) \/ (q < 0 /\ r <= 0) \/ (q == 0).
Proof.
  move=> m d Hd.
  rewrite /sdivmod.
  do! case: ifP; nia.
Qed.

(**
まとめた式
*)
Goal forall m d : int, d != 0 -> let: (q, r) := sdivmod m d in
                             if (0 < q) then 0 <= r < `|d|
                             else if (q < 0) then - `|d| < r <= 0
                                  else - `|d| < r < `|d|. (* q = 0 の場合 *)
Proof.
  move=> m d Hd.
  rewrite /sdivmod.
  do! case: ifP; nia.
Qed.

(**
# Euclidean division の実装
*)

(**
## Truncation Division による Euclidean division
*)

Definition edivmod_t (m d : int) : int * int :=
  let: (q, r) := tdivmod m d in
  if (r == 0) then (q, r)
  else if (0 <= r) then (q, r)
  else
    let: r1 := r + d in
    if (0 <= r1) && (r1 < `|d|) then (q - 1, r1)
    else (q + 1, r - d).

(**
例
*)
Compute edivmod_t 10 3.                     (* 3, 1 *)
Compute edivmod_t 10 (-3).                  (* -3, 1 *)
Compute edivmod_t (-10) 3.                  (* -4, 2 *)
Compute edivmod_t (-10) (-3).               (* 4, 2 *)

(**
被除数に戻ること。
 *)
Goal forall m d : int, d != 0 ->
                   let: (q, r) := edivmod_t m d in m = q * d + r.
Proof.
  move=> m d Hd //=.
  rewrite /edivmod_t /tdivmod.
  do! case: ifP; lia.
Qed.

(**
剰余の範囲を確認する。
 *)
Goal forall m d : int, d != 0 ->
                   let: (q, r) := edivmod_t m d in r < `| d |.
Proof.
  move=> m n Hd //=.
  rewrite /edivmod_t /tdivmod.
  do! case: ifP; lia.
Qed.


(**
## Flooring Division による Euclidean division
*)

Definition edivmod_f (m d : int) :=
  let: (q, r) := fdivmod m d in
  if (r == 0) then (q, r)
  else if (d < 0) then (q + 1, r - d)
       else (q, r).

(**
例
*)
Compute edivmod_f 10 3.                     (* 3, 1 *)
Compute edivmod_f 10 (-3).                  (* -3, 1 *)
Compute edivmod_f (-10) 3.                  (* -4, 2 *)
Compute edivmod_f (-10) (-3).               (* 4, 2 *)

(**
被除数に戻ること。
 *)
Goal forall m d : int, d != 0 ->
                   let: (q, r) := edivmod_f m d in m = q * d + r.
Proof.
  move=> m d Hd //=.
  rewrite /edivmod_f /fdivmod.
  do! case: ifP; lia.
Qed.

(**
剰余の範囲を確認する。
 *)
Goal forall m d : int, d != 0 ->
                   let: (q, r) := edivmod_f m d in 0 <= r < `|d|.
Proof.
  move=> m n Hd //=.
  rewrite /edivmod_f /fdivmod.
  do! case: ifP; lia.
Qed.

(**
## Symmetry Division による Euclidean division
*)

Definition edivmod_s (m d : int) : (int * int) :=
  let: (q, r) := sdivmod m d in
  if (r == 0) then (q, r)
  else if (0 <= m) then
         if (d < 0) then (q + 1, r - d) else (q, r)
       else
         if (0 < d) then (q - 1, r + d) else (q, r).


(**
例
*)
Compute edivmod_s 10 3.                     (* 3, 1 *)
Compute edivmod_s 10 (-3).                  (* -3, 1 *)
Compute edivmod_s (-10) 3.                  (* -4, 2 *)
Compute edivmod_s (-10) (-3).               (* 4, 2 *)

(**
被除数に戻ること。
 *)
Goal forall m d : int, d != 0 ->
                   let: (q, r) := edivmod_s m d in m = q * d + r.
Proof.
  move=> m d Hd //=.
  rewrite /edivmod_s /sdivmod.
  do! case: ifP; lia.
Qed.

(**
剰余の範囲を確認する。
 *)
Goal forall m d : int, d != 0 ->
                   let: (q, r) := edivmod_s m d in 0 <= r < `|d|.
Proof.
  move=> m n Hd //=.
  rewrite /edivmod_s /sdivmod.
  do! case: ifP; lia.
Qed.

(* END *)
