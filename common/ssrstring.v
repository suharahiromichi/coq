From HB Require Import structures.          (* MathComp2 *)
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

  HB.instance Definition _ := hasDecEq.Build ascii ascii_eqP. (* MathComp2 *)
End SSRAscii.

Check "a"%char : ascii : eqType.

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
  
  HB.instance Definition _ := hasDecEq.Build string String.eqb_spec. (* MathComp2 *)
End SSRString.

Check "aaa"%string : string : eqType.

Check "aaa"%string = "aaa"%string : Prop.
Check "aaa"%string == "aaa"%string : bool.
Check "aaa"%string == "aaa"%string : Prop.

(* END *)
