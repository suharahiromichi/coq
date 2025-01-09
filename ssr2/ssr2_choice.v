From elpi Require Import elpi.
From HB Require Import structures.
From mathcomp Require Import all_ssreflect.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(**
Coq/SSReflect の choiceType とは何か

http://www.a-k-r.org/d/2024-12.html#a2024_12_22
*)

(**
# choice operator を使う。
*)
Section a.

  Lemma ex8 : exists n, 2 < n.
  Proof.
    exists 8.
    done.
  Qed.

  Lemma ex42 : exists n, 2 < n.
  Proof.
    exists 42.
    done.
  Qed.
  
  Check @xchoose : forall (T : choiceType) (P : pred T), (exists x : T, P x) -> T.

(**
ex8 からそれを満たす n を取り出す。それは ``2 < n`` である。
*)
  Goal 2 < xchoose ex8.
  Proof.
    by apply: xchooseP.
  Qed.
  
(**
ex8 と ex42 を満たす n は等しい。
*)
  Goal xchoose ex8 = xchoose ex42.
  Proof.
    by apply: eq_xchoose.
  Qed.

End a.

(* END *)
