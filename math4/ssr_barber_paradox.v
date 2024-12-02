(**
床屋のパラドックス

-------------------

Lean by Example の演習問題の「床屋のパラドックス」を解いてみます。

https://lean-ja.github.io/lean-by-example/Tutorial/Exercise/BarberParadox.html
*)

Search (_ <-> _).

From mathcomp Require Import all_ssreflect.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section Barber.

(**
## Lean の演習問題の部分をCoqにする
*)

(* 全体集合となる人々の集合 *)
Variable Person : Type.

(* p さんが q さんの髭を剃るという述語 *)
Variable shave : Person -> Person -> bool.

(* 床屋が存在するという仮定 *)
Variable barber : Person.

(* 床屋の信念を仮定として表現したもの *)
(*
Variable policy : forall p : Person, (shave barber p <-> ~ shave p p).
*)

(**
## 補題
*)
Lemma paradox (q : bool) : (q -> ~q) -> (~q -> q) -> False.
Proof.
  case: q => H1 H2.
  - by case: H1.
  - by case: H2.
Qed.

(**
## 証明したいもの
 *)
Theorem nosuchbarber :
  ~ (forall p : Person, shave barber p <-> ~ shave p p).
Proof.
  move/(_ barber).
  case.
  by apply: paradox.
Qed.

End Barber.

(* END *)
