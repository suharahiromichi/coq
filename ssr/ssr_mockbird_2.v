(* ラムダ式をコンビネータに変換するα消去のプログラム *)
(* 
   TODO:

   SKI と x y z を項として分離する。
   in_bird を \in を使えるようにする。
   α消去で与える変数を自動化する。
 *)

From mathcomp Require Import all_ssreflect.

Inductive var : Set := I | S | K | x | y | z.

Definition eqVar (x y : var) : bool :=
  match x, y with
    | I,  I => true
    | S,  S => true
    | K,  K => true
    | x,  x => true
    | y,  y => true
    | z,  z => true
    | _,  _ => false
  end.

Lemma var_eqP : forall (x y : var), reflect (x = y) (eqVar x y).
Proof.
  move=> x y.
  by apply: (iffP idP); case: x; case: y.
(*  
  case H : (eqVar x y).
  - apply: Bool.ReflectT.
    by case: x H; case: y => //=.
  - apply: Bool.ReflectF.
    by case: x H; case: y => //=.
*)
Qed.

Definition var_eqMixin := @EqMixin var eqVar var_eqP.
Canonical var_eqType := @EqType var var_eqMixin.

Reserved Notation "x '@' y" (at level 50, left associativity).
Inductive birdterm : Set :=
| bird of var
| birdapp of birdterm & birdterm.            (* x @ y *)
Notation "x @ y" := (birdapp x y).

Fixpoint in_bird (v : var) (M : birdterm) : bool :=
  match M with
  | bird u => v == u
  | M1 @ M2 => in_bird v M1 || in_bird v M2
  end.

Fixpoint lc_bird (v : var) (M : birdterm) : birdterm :=
  match M with
  | bird u =>
    if u == v then bird I else bird K @ bird u
  | M1 @ M2 =>
    let M1' := if in_bird v M1 then lc_bird v M1 else bird K @ M1 in
    let M2' := if in_bird v M2 then lc_bird v M2 else bird K @ M2 in
    bird S @ M1' @ M2'
  end.

(* 実行例 *)

(* 合成鳥 *)
Definition B := bird x @ (bird y @ bird z).

(* ものまね鳥 *)
Definition M := bird x @ bird x.

Compute lc_bird z B.
(* = bird S @ (bird K @ bird x) @ (bird S @ (bird K @ bird y) @ bird I) *)

Compute lc_bird x (lc_bird y (lc_bird z B)).
(* = bird S @
       (bird S @ (bird K @ bird S) @
        (bird S @ (bird K @ bird K) @
         (bird S @ (bird K @ bird S) @ (bird S @ (bird K @ bird K) @ bird I)))) @
       (bird K @
        (bird S @ (bird S @ (bird K @ bird S) @ (bird S @ (bird K @ bird K) @ bird I)) @
         (bird K @ bird I)))
*)

Compute lc_bird x M.
(* = bird S @ bird I @ bird I *)

(* END *)
