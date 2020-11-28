From mathcomp Require Import all_ssreflect.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Set Print All.

(* csm_5_set_theory.v は不使用である。 *)

Section ライブラリfinsetの利用.
  Variable M : finType.

  Lemma demorgan (A B C : {set M}) : (A :&: B) :|: C = (A :|: C) :&: (B :|: C).
  Proof.
    apply/setP => x.
    rewrite !inE.                          (* || と && に変換する。 *)
    Check orb_andl.
    by rewrite -orb_andl.         (* || と && の ド・モルガンの定理 *)
  Qed.

End ライブラリfinsetの利用.

(* END *)
