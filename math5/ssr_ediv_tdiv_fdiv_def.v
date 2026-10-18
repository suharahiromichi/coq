(**
整数割算
========================

@suharahiromichi

2026/10/15
 *)

(**
# はじめに

いろいろな整数割算をみてみる。
証明をすることを前提に。
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
## 切り捨て割り算
*)
Definition div_floor (m d : int) :=
  if (m %% d == 0)%Z then (m %/ d)%Z
  else if (0 < d) then (m %/ d)%Z else (m %/ d)%Z - 1.

Definition divmod_floor (m d : int) :=
  let: q := div_floor m d in (q, m - q * d).

Compute divmod_floor 10 3.                  (* 3, 1 *)
Compute divmod_floor 10 (-3).               (* -4, -2 *)
Compute divmod_floor (-10) 3.               (* -4, 2 *)
Compute divmod_floor (-10) (-3).            (* 3, -1 *)

Lemma pos_d__pos_r__div_floor (m d : int) :
  0 < d -> let: (q, r) := divmod_floor m d in 0 <= r < d.
Proof.
  rewrite /divmod_floor /div_floor.
  do! case: ifP; lia.
Qed.

Lemma neg_d__neg_r__div_floor (m d : int) :
  d < 0 -> let: (q, r) := divmod_floor m d in d < r <= 0.
Proof.
  rewrite /divmod_floor /div_floor.
  do! case: ifP; lia.
Qed.


(**
## 切り上げ割り算
*)
Definition div_ceil (m d : int) :=
  if (m %% d == 0)%Z then (m %/ d)%Z
  else if (0 < d) then (m %/ d)%Z + 1 else (m %/ d)%Z.

Definition divmod_ceil (m d : int) :=
  let: q := div_ceil m d in (q, m - q * d).

Compute divmod_ceil 10 3.                   (* 4, -2 *)
Compute divmod_ceil 10 (-3).                (* -3, 1 *)
Compute divmod_ceil (-10) 3.                (* -3, -1 *)
Compute divmod_ceil (-10) (-3).             (* 4, 2 *)

Lemma pos_d__neg_r__div_ceil (m d : int) :
  0 < d -> let: (q, r) := divmod_ceil m d in -d < r <= 0.
Proof.
  rewrite /divmod_ceil /div_ceil.
  do! case: ifP; lia.
Qed.

Lemma neg_d__pos_r__div_ceil (m d : int) :
  d < 0 -> let: (q, r) := divmod_ceil m d in 0 <= r < -d.
Proof.
  rewrite /divmod_ceil /div_ceil.
  do! case: ifP; lia.
Qed.

(**
# いろいろな整数割算

## ユークリッド除算

- 剰余は0または正
- Rocq の ``%/`` と ``%%``
 *)

Definition edivmod (m d : int) :=
  if (0 < d) then divmod_floor m d else divmod_ceil m d.

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
  move=> m d Hd.
  rewrite /edivmod /divmod_floor /divmod_ceil /div_floor /div_ceil.
  do! case: ifP; lia.
Qed.

(**
剰余の範囲
 *)
Goal forall m d : int, d != 0 ->
                   let: (q, r) := edivmod m d in `|r| < `|d|.
Proof.
  move=> m n Hd.
  rewrite /edivmod /divmod_floor /divmod_ceil /div_floor /div_ceil.
  do! case: ifP; lia.
Qed.

(**
剰余は0または正
 *)
Goal forall m d : int, d != 0 ->
                   let: (q, r) := edivmod m d in 0 <= r.
Proof.
  move=> m n Hd.
  rewrite /edivmod /divmod_floor /divmod_ceil /div_floor /div_ceil.
  do! case: ifP; lia.
Qed.

(**
まとめた式
 *)
Goal forall m d : int, d != 0 ->
                   let: (q, r) := edivmod m d in 0 <= r < `|d|.
Proof.
  move=> m n Hd.
  rewrite /edivmod /divmod_floor /divmod_ceil /div_floor /div_ceil.
  do! case: ifP; lia.
Qed.

(**
## Truncation towards zero division

- 剰余は0または被除数と同符号
- 商が正なら切り捨て、商が負なら切り上げる。
- C言語の ``%%``
*)

Definition tdivmod (m d : int) :=
  if (0 < m) then
    if (0 < d) then divmod_floor m d else divmod_ceil m d
  else if (m < 0) then
    if (0 < d) then divmod_ceil m d else divmod_floor m d
  else (0, 0).                              (* m == 0 *)

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
  rewrite /tdivmod /divmod_floor /divmod_ceil /div_floor /div_ceil.
  do! case: ifP; lia.
Qed.

(**
剰余の範囲
 *)
Goal forall m d : int, d != 0 ->
                   let: (q, r) := tdivmod m d in `|r| < `|d|.
Proof.
  move=> m d Hd.
  rewrite /tdivmod /divmod_floor /divmod_ceil /div_floor /div_ceil.
  do! case: ifP; lia.
Qed.

(**
被除数が0以上なら剰余は0以上、被除数が0未満なら剰余は0以下
 *)
Goal forall m d : int, d != 0 ->
                   let: (q, r) := tdivmod m d in (0 <= m /\ 0 <= r) \/ (m < 0 /\ r <= 0).
Proof.
  move=> m d Hd.
  rewrite /tdivmod /divmod_floor /divmod_ceil /div_floor /div_ceil.
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
  rewrite /tdivmod /divmod_floor /divmod_ceil /div_floor /div_ceil.
  do! case: ifP; lia.
Qed.

(**
## Flooring division

- 剰余は0か除数と同符号。
- 商を切り捨てる。
- Python の ``%%``
*)

Definition fdivmod (m d : int) := if (m == 0) then (0, 0) else divmod_floor m d.

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
  rewrite /fdivmod /divmod_floor /div_floor.
  do! case: ifP; lia.
Qed.

(**
剰余の範囲
 *)
Goal forall m d : int, d != 0 ->
                   let: (q, r) := fdivmod m d in `|r| < `|d|.
Proof.
  move=> m d Hd.
  rewrite /fdivmod /divmod_floor /div_floor.
  do! case: ifP; lia.
Qed.

(**
除数が0を超えるなら剰余は0以上、除数が0未満なら剰余は0以下
 *)
Goal forall m d : int, d != 0 ->
                   let: (q, r) := fdivmod m d in (0 < d /\ 0 <= r) \/ (d < 0 /\ r <= 0).
Proof.
  move=> m d Hd.
  rewrite /fdivmod /divmod_floor /div_floor.
  do! case: ifP; lia.
Qed.

(**
まとめた式
*)
Goal forall m d : int, d != 0 ->
                   let: (q, r) := fdivmod m d in 0 <= r < d \/ d < r <= 0.
Proof.
  move=> m d Hd.
  rewrite /fdivmod /divmod_floor /div_floor.
  do! case: ifP; lia.
Qed.

(**
## Symmetry Division

- 剰余は0か商と同符号。ただし、商が0の場合をのぞく（商が0なら剰余は被除数とおなじ）。
- 被除数が正なら商を切り捨て、被除数が負なら商を切り上げる。
 *)

Definition sdivmod (m d : int) :=
  if (0 < m) then divmod_floor m d
  else if (m < 0) then divmod_ceil m d
  else (0, 0).                              (* m == 0 *)
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
  rewrite /sdivmod /divmod_floor /divmod_ceil /div_floor /div_ceil.
  do! case: ifP; lia.
Qed.

(**
剰余の範囲
 *)
Goal forall m d : int, d != 0 -> let: (q, r) := sdivmod m d in `|r| < `|d|.
Proof.
  move=> m d Hd.
  rewrite /sdivmod /divmod_floor /divmod_ceil /div_floor /div_ceil.
  do! case: ifP; lia.
Qed.

(**
商が0を超えるなら剰余は0以上、商が0未満なら剰余は0以下、商が0の場合は剰余は不問。
 *)
Goal forall m d : int, d != 0 -> let: (q, r) := sdivmod m d in
                             (0 < q /\ 0 <= r) \/ (q < 0 /\ r <= 0) \/ (q == 0).
Proof.
  move=> m d Hd.
  rewrite /sdivmod /divmod_floor /divmod_ceil /div_floor /div_ceil.
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
  rewrite /sdivmod /divmod_floor /divmod_ceil /div_floor /div_ceil.
  do! case: ifP; nia.
Qed.

(* END *)
