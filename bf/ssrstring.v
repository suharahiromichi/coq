From mathcomp Require Import all_ssreflect.
Require Import Ascii String.
Export Ascii String.

(**
https://coq.inria.fr/library/Coq.Strings.Ascii.html
 *)
(* Open Scope char_scope.                   (* "a" : ascii *) *)
Definition ascii_eqMixin := EqMixin Ascii.eqb_spec.
Canonical ascii_eqType := EqType ascii ascii_eqMixin.


(**
https://coq.inria.fr/library/Coq.Strings.String.html
 *)
(* Open Scope string_scope.                    (* "a" : string *) *)
Definition string_eqMixin := EqMixin String.eqb_spec.
Canonical string_eqType := EqType string (EqMixin String.eqb_spec).

(* END *)
