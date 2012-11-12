(** 非同期順序回路（マスタークロックを使わない順序論理回路）を同期順序
   回路として実装するための、コード例。
   
   値の一部を次周期に回し、それを前回値として参照することで、見掛け上組
   み合わせ論理だけで、順序同期回路を実現できる。
*)

Require Import Bool.
Require Import Arith.

(** 基本素子 *)
Definition elm (s r t c : bool) (d z p : nat) : nat :=
  match s,   r,     t,     c with
    | false, false, false, false => z
    | _,     true,  _,     _     => 0       (* R *)
    | _,     _,     true,  _     => z + 1   (* S *)
    | true,  _,     _,     _     => p - 1   (* D *)
    | _,     _,     _,     true  => d       (* T *)
  end.

Definition ff (s r t c d z : bool) : bool :=
  match s,   r,     t,     c with
    | false, false, false, false => z
    | _,     true,  _,     _     => false   (* R *)
    | true,  _,     _,     _     => true    (* S *)
    | _,     _,     _,     true  => d       (* D *)
    | _,     _,     true,  _     => negb z  (* T *)
  end.

Definition act (d z : bool) : bool :=
  match d, z with
    | true, false => true
    | _, _ => false
  end.

Definition neg (d z : bool) : bool :=
  match d, z with
    | false, true => true
    | _, _ => false
  end.

(** 応用回路 *)

(** モノマルチ *)
(* d : カウント開始信号 *)
(* zd : dの前回値 *)
(* qz : qの前回値 *)
(* cz : cの前回値 *)
(* p : カウント上限値、この値までとる *)
Definition monomulti (d zd qz : bool) (cz p : nat) : (bool * nat) :=
(* q : カウントアップ中判定  *)
(* c : カウント値 *)
  match ff (act d zd) (beq_nat cz p) false false false qz with
(* 前回、上限pだったら、リセットする。これが肝だ。 *)
    | false => (false, 0)
    | true  => (true, cz + 1)
  end.

(** たすき掛け回路 *)
(* t1 : 1側トグル *)
(* c1 : 1側→2側コピー *)
(* z1 : 1側前回値 *)
Definition tasiki (t1 c1 z1 t2 c2 z2 : bool) : (bool * bool) :=
  (ff false false t1 c2 z2 z1,              (* q1 : 1側 *)
    ff false false t2 c1 z1 z2).            (* q2 : 2側 *)

Fixpoint ble_nat (n m : nat) : bool :=
  match n with
  | O => true
  | S n' =>
      match m with
      | O => false
      | S m' => ble_nat n' m'
      end
  end.

(** ベセルスイッチ入力 *)
(* d : スイッチの生値 *)
(* q : 100msモノマルチ *)
(* tz : tの前回値 *)
Definition bezel0 (d q : bool) (tz : nat) : (bool * bool * nat) :=
(* u0 : モノマルチで引き伸ばした押下中 *)
(* v0 : 長押し判定した押下中 *)
(* t : 長押し時間 *)
  match (d, q) with
    | (_, true) | (true, _) => (true, ble_nat 3000 (tz + 1), tz + 1)
    | _                     => (false, false, 0)
  end.

(** ベゼルエッジ判定  *)
(* u0 : モノマルチで引き伸ばした押下中 *)
(* v0 : 長押し判定した押下中 *)
(* uz : u0 前回値 *)
(* vz : u0 前回値 *)
(* rz : rの前回値 *)
Definition bezel1 (u0 v0 uz vz : bool) (rz : nat) : (bool * bool * bool * nat) :=
(* u : 短押し立下り *)
(* v : 長押し立上り、長押し判定時 *)
(* w : 繰り返し  *)
(* r : 繰り返しカウンタ *)
  match (uz, u0, vz, v0) with
    | (true, false, false, _) =>            (* 短押し終わり *)
      (true, false, true, 0)
    | (false, false, false, true) =>        (* 長押し初め *)
      (false, true, false, 0)
    | (false, false, true, true) =>         (* 長押しのあいだ *)
      match ble_nat 1000 rz with
        | true  => (false, false, true, 0)
        | false => (false, false, false, rz + 1)
      end
    | (_, _, _, _) =>                       (* 押されていない *)
      (false, false, false, 0)
  end.

(** ベゼル入力処理 *)
(* d : スイッチの生値 *)
(* z : 前回値 *)
Definition bezel (d : bool) (z : bool * bool * bool * bool * nat * nat * nat) :
  bool * bool * bool *          (bool * bool * bool * bool * nat * nat * nat) :=
(* u : 短押し立下り *)
(* v : 長押し立上り、長押し判定時 *)
(* w : 繰り返し  *)
(* z : 前回値 *)
  match z with
    | (dz, qz, uz, vz, cz, tz, rz) =>
    match (monomulti d dz qz cz 100) with
      | (q, c) =>
      match (bezel0 d q tz) with
        | (u0, v0, t) =>
        match (bezel1 u0 v0 uz vz rz) with
          | (u, v, w, r) =>
            (u, v, w, (d, q, u0, v0, c, t, r))
        end
      end
    end
  end.

(* END *)
