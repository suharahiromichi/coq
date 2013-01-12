(* 
   発表用のコード
   2013_01_16
   *)
Require Export SfLib_J.

Check list nat.
Print ble_nat.

(* 
   ループ不変式：
   m と 「lの最大」の大きいほうは、「listの最大」に等しい。
   
   この処理：
   m と mi(lの先頭)の大きい方と、li(lの残り)を引数に再帰的に自分を呼び出す。
   再帰呼び出しが終了するなら、処理はループ不変式に等しい。
   *)
Fixpoint maximum (m : nat) (l : list nat) : nat :=
  match l with
    | nil => m
    | cons mi li =>
      match ble_nat m mi with
        | true => maximum mi li
        | false => maximum m li
      end
  end.
Definition list := cons 1 (cons 3 (cons 2 (cons 1 nil))).
Eval compute in maximum 0 list.             (* 3 *)
Eval compute in maximum 0 (cons 1 (cons 3 (cons 2 (cons 1 nil)))). (* 3 *)
Eval compute in maximum 1         (cons 3 (cons 2 (cons 1 nil))).  (* 3 *)
Eval compute in maximum 3                 (cons 2 (cons 1 nil)).   (* 3 *)
Eval compute in maximum 3                         (cons 1 nil).    (* 3 *)
Eval compute in maximum 3                                 nil.     (* 3 *)

(* 実際は、型宣言は要らない。 *)
Fixpoint maximum''' m l :=
  match l with
    | nil => m
    | cons mi li =>
      match ble_nat m mi with
        | true => maximum mi li
        | false => maximum m li
      end
  end.

(* 
   ループ不変式：
   foldl f = F とする。
   f m (F l) は、F list に等しい。
 *)
Fixpoint foldl {X Y : Type} (f : Y -> X -> Y) m l :=
  match l with
    | nil => m
    | cons mi li => foldl f (f m mi) li
  end.
Print foldl.

Definition max x y :=
  match ble_nat x y with
    | true => y
    | false => x
  end.
(*
   ループ不変式： max m (maximum l) は、maximun list に等しい。
   *)
Definition maximum' := foldl max.
Eval compute in maximum' 0 list.

(* 
   ループ不変式： plus m (sum l) は、sum list に等しい。
   m と 「lの総和」の和は、「listの総和」に等しい。
   *)
Check plus.
Definition sum := foldl plus.
Eval compute in sum 0 list.
Eval compute in foldl minus 100 list.

Fixpoint foldr {X Y : Type} (f : X -> Y -> Y) m l : Y :=
  match l with
    | nil => m
    | cons mi li => f mi (foldr f m li)
  end.
Print foldr.

Eval compute in foldr plus 0 list.

(*
   pairコンストラクタで、見えるようにしてみる。
   *)
Inductive pair_left {X : Type} : Type :=
| nl : pair_left
| pl : pair_left -> X -> pair_left.
Eval compute in foldl pl nl list.
(* pr 1 (pr 3 (pr 2 (pr 1 nr))) *)

Inductive pair_right {X : Type} : Type :=
| nr : pair_right
| pr : X -> pair_right -> pair_right.
Eval compute in foldr pr nr list.
(* pr 1 (pr 3 (pr 2 (pr 1 nr))) *)

(* END *)
