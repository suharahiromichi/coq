From mathcomp Require Import all_ssreflect.

(* 5.11.1 Phantom types *)

Inductive phantom (T : Type) (p : Type) := Phantom.
Arguments phantom : clear implicits.

(* 7. Hierarchies *)
(* 7.4 Parameters and constructors *)

Inductive phant (p : Type) := Phant.

(* *********** *)
(* (1) phantom *)
(* *********** *)
(* {set p} として、p に  eqType にカノニカルプロジェクションできる型だけを書きたい。 *)

Definition set_of'' (T : eqType) (_ : phantom Type (Equality.sort T)) := seq T.

Notation "{ 'set' p }" := (set_of'' _ (Phantom _ p))
                            (at level 0, format "{ 'set' p }") : type_scope.

Check set_of'' nat_eqType (Phantom Type nat_eqType).
Check set_of'' _          (Phantom _ nat_eqType).
Check {set nat_eqType}.

(* (1.1) *)
Print Canonical Projections.
(* nat <- Equality.sort ( nat_eqType ) である。 *)
(* nat を書くことかできる。 *)
Check set_of'' nat_eqType (Phantom Type nat).
Check set_of'' _          (Phantom _ nat).
Check {set nat}.

(* (1.2) *)
(* windrose 型は、カノニカルプロダクションが無いので、それを書くことができない。 *)
Inductive windrose : predArgType := N | S | E | W.
Fail Check set_of'' _ (Phantom _ windrose).
Fail Check {set windrose}.

(* (1.3) ユニフィケーションの説明 *)
(* set_of'' の最後の引数 *)
Check Phantom _ nat : phantom Type nat.               (* 実引数 *)
Check _             : phantom Type (Equality.sort _). (* 仮引数 *)
(* カノニカルストラクチャで、nat_eqType が見つかる。 *)
Check phantom Type (Equality.sort nat_eqType).


(* ********* *)
(* (2) phant *)
(* ********* *)
(* {set p} として、p に  eqType にカノニカルプロジェクションできる型だけを書きたい。 *)

Definition set_of (T : eqType) (_ : phant (Equality.sort T)) := seq T.

Notation "{ 'set' p }" := (set_of _ (Phant p))
                            (at level 0, format "{ 'set' p }") : type_scope.

Check set_of nat_eqType (Phant nat_eqType).
Check set_of _          (Phant nat_eqType).
Check {set nat_eqType}.

(* (2.1) *)
Print Canonical Projections.
(* nat <- Equality.sort ( nat_eqType ) である。 *)
(* nat を書くことかできる。 *)
Check set_of nat_eqType (Phant nat).
Check set_of _          (Phant nat).
Check {set nat}.

(* (2.2) *)
(* windrose 型は、カノニカルプロダクションが無いので、それを書くことができない。 *)
Fail Check set_of _ (Phant _ windrose).
Fail Check {set windrose}.

(* (2.3) ユニフィケーションの説明 *)
(* set_of の最後の引数 *)
Check Phant nat : phant nat.               (* 実引数 *)
Check _         : phant (Equality.sort _). (* 仮引数 *)
(* カノニカルストラクチャで、nat_eqType が見つかる。 *)
Check phant (Equality.sort nat_eqType).


(* ******************************* *)
(* (3) ファントムタイプを使わない例 *)
(* ******************************* *)
(* カノニカルストラクチャが機能しないので、nat を引数にとれない。 *)
Definition set_of' (T : eqType) := seq T.
Check set_of' nat_eqType.
Fail Check set_of' nat.

(* END *)
