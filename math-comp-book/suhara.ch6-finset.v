From mathcomp Require Import all_ssreflect.
From mathcomp Require Import perm.

Check [set: bool] : {set bool}.
Compute true \in [set: bool].
Compute false \in [set: bool].

Check finset (fun x => x \in [set: bool]).



(* predArgType のひとつのみかた *)

(* これまで勉強してきた型は predArgType として定義されている。 *)
Check 'I_3               : predArgType.
Check {tuple 3 of nat}   : predArgType.
Check {ffun bool -> nat} : predArgType.
Check {set  'I_3} : predArgType.
Check {perm 'I_3} : predArgType.

(* 任意の型を predArgType にすることもできる。 *)
Check {: bool}    : predArgType.
Check {: nat}     : predArgType.

(* predArgType の要素のひとつの見方は、pred T の T になることができる。 *)
(* pred T は、T -> bool の決定可能な述語である。 *)
Check pred {: nat} : Type.

(* predArgType から pred へのコアーションがある。 *)
Print Graph.
(* [pred_of_argType] : predArgType >-> simpl_pred *)

Check pred_of_argType : forall T : predArgType, pred T.
Print pred_of_argType.                      (* = [eta @predT] *)
(* = @predT *)
(* = fun {T : predArgType} (x : T) => true *)
(* predT は、任意の引数にたいして true だけを返す関数だが、 *)
(* 省略可能な第一引数で指定した型と一致しなければ、ならない。 *)

Check pred_of_argType {: nat} : pred {: nat}.
Check pred_of_argType {: nat} : pred nat.
Check {: nat}                 : pred {: nat}.
Check {: nat}                 : pred nat.
Check pred_of_argType nat : pred {: nat}.
Check pred_of_argType nat : pred nat.
Fail Check nat                 : pred {: nat}.
Fail Check nat                 : pred nat.

(* 実行してみると。 *)
Check {: nat} 1 : bool.
Compute {: nat} 1.                          (* true しか返さない。 *)
Fail Compute {: nat} bool.                  (* エラーになる。 *)

(* END *)
