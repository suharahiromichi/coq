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
    | _,     true,  _,     _     => 0
    | true,  _,     _,     _     => p - 1
    | _,     _,     true,  _     => z + 1
    | _,     _,     _,     true  => d
  end.

Definition ff (s r t c d z : bool) : bool :=
  match s,   r,     t,     c with
    | false, false, false, false => z
    | _,     true,  _,     _     => false
    | true,  _,     _,     _     => true
    | _,     _,     true,  _     => negb z
    | _,     _,     _,     true  => d
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

(* END *)
