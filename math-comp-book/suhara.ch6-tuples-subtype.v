From mathcomp Require Import all_ssreflect.

(* 6. Sub-Types Terms with properties *)
(* 6.2.1 The sub-type kit *)

Check [tuple of [:: 1; 2; 3]] : 3.-tuple nat.

Check @tval 3 nat [tuple of [:: 1; 2; 3]] : seq nat.
Check tval        [tuple of [:: 1; 2; 3]] : seq nat.

Compute @tval 3 nat [tuple of [:: 1; 2; 3]]. (* [:: 1; 2; 3] *)

Print Graph.
(* [tval] : tuple_of >-> list *)

Check             [tuple of [:: 1; 2; 3]] : seq nat. (* コアーション *)


(* カノニカルが有効な例 *)
Print Canonical Projections.
(*
tuple_of <- sub_sort ( tuple_subType )      (* SubType *)
tuple_of <- Equality.sort ( tuple_eqType )
 *)

(* insub - 引数をサブタイプのoption型に変換する。変換できなければNONEとする。 *)
Print insub.
(* fun (T : Type) (P : pred T) (sT : subType (T:=T) P) (x : T) =>
match idP with
| ReflectT Px => Some (Sub x Px)
| ReflectF _ => None
end
 *)

Check insub : _ -> option _.
Check @insub : forall (T : Type) (P : pred T) (sT : subType (T:=T) P), T -> option sT.

Check @insub (seq nat) (fun s => size s == 3) (tuple_subType 3 nat)
      [::1;2;3] : option (tuple_subType 3 nat).

                                              (* ↓これは3.-tuple natにならない。 *)
Check @insub (seq nat) [pred s | size s == 3] (tuple_subType 3 nat)
      [::1;2;3] : option (3.-tuple nat).

Check insub [::1;2;3] : option (tuple_subType 3 nat).
Check insub [::1;2;3] : option (3.-tuple nat).


(* The insubd constructor takes a default sub-type value which it
returns if the tests fails. *)
Print insubd.

Check insubd : _ -> _ -> _.
Check @insubd : forall (T : Type) (P : pred T) (sT : subType (T:=T) P), sT -> T -> sT.

Check @insubd (seq nat) [pred s | size s == 3] (tuple_subType 3 nat)
      [tuple of [::1;1;1]] [::1;2;3] : 3.-tuple nat.
Check insubd [tuple of [::1;1;1]] [::1;2;3] : 3.-tuple nat.

(* END *)
