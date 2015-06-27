Require Import ssreflect ssrbool ssrfun eqtype ssrnat div seq choice fintype.
Require Import finfun bigop finset.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Goal FinSet [ffun x : 'I_3 => true] = setT.
apply/setP => /= x.
rewrite {1}SetDef.pred_of_setE /=.
rewrite {1}/in_mem.
rewrite {1}/mem.
rewrite /=.
rewrite ffunE.
rewrite in_setT.
done.
Qed.

(* おまけ。 *)
Goal [set: 'I_3] = setT.
apply/setP.
by case => /=.
Qed.

Section finset_example.

Variable T : finType.
Variables A B C : {set T}.

(* use setP *)
Lemma exo20 : (A :&: B) :|: C = (A :|: C) :&: (B :|: C).
Proof.
  Search (_ :&: _ :|: _).
  by rewrite setUIl.
Qed.

End finset_example.
