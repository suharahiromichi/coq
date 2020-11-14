From mathcomp Require Import all_ssreflect.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Set Print All.

Require Import Ascii.
Require Import String.
Export Ascii.
Export String.

Section SSRAscii.

  Definition eqAscii (a b : ascii) : bool :=
    match ascii_dec a b with
    | left _ => true
    | right _ => false
    end.

  Compute eqAscii "a" "a".                  (* true *)
  Compute eqAscii "a" "b".                  (* false *)
  
  Lemma ascii_eqP (a b : ascii) : reflect (a = b) (eqAscii a b).
  Proof.
    rewrite /eqAscii.
    (* reflect (a = b) (if ascii_dec a b then true else false) *)
    apply: (iffP idP); by case: (ascii_dec a b).
  Qed.
  
  Fail Canonical ascii_eqType := [eqType of ascii].

  Definition ascii_eqMixin := @EqMixin ascii eqAscii ascii_eqP.
  Canonical ascii_eqType := @EqType ascii ascii_eqMixin.

  Canonical ascii_eqType' := [eqType of ascii].
End SSRAscii.

Check ascii_eqType : eqType.
Check "a"%char : ascii.
Check "a"%char : ascii_eqType.

Check true : bool.
Check true : bool_eqType.

Check 1 : nat.
Check 1 : nat_eqType.
  
Section SSRString.
  
  Definition eqString (s t : string) : bool :=
    match string_dec s t with
    | left _ => true
    | right _ => false
    end.
  
  Compute eqString "aaaa"%string "aaaa"%string. (* true *)
  Compute eqString "aaaa"%string "aa"%string.   (* false *)
  
  Lemma string_eqP (x y : string) : reflect (x = y) (eqString x y).
  Proof.
    rewrite /eqString.
    apply: (iffP idP); by case: (string_dec x y).
  Qed.        
  
  Definition string_eqMixin := @EqMixin string eqString string_eqP.
  Canonical string_eqType := @EqType string string_eqMixin.

End SSRString.

Check "aaa"%string = "aaa"%string : Prop.
Check "aaa"%string == "aaa"%string : bool.
Check "aaa"%string == "aaa"%string : Prop.

(* END *)
