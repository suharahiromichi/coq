(**
Dependent if-then-else を Coq/MathComp で定義してみた。
 *)
From mathcomp Require Import all_ssreflect.
From mathcomp Require Import all_classical.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(**
Dependent if-then-else
 *)
Definition dite {a : Type} (c : Prop) (t : c -> a) (e : ~ c -> a) : a.
Proof.
  case: (pselect c).
  - by apply: t.
  - by apply: e.
Defined.
Arguments dite {a} c t e.
Notation "'if' h '|' c 'then' t 'else' e" := (dite c (fun h => t) (fun h => e)) (at level 200).

Definition linv {A B : Type} {hnonempty : inhabited A} (b : B) (f : A -> B) :=
  dite (exists a, f a = b)
    (fun h => projT1 (cid h))    (* lean の Classical.choose_spec h *)
    (fun h => inhabited_witness hnonempty). (* default *)
Arguments linv {A B hnonempty} b f.

Definition linv' {A B : Type} {hnonempty : inhabited A} (b : B) (f : A -> B) :=
  if h | exists a, f a = b then projT1 (cid h) else inhabited_witness hnonempty.

Section d.
  Variable A B : Type.
  Variable hnonempty : inhabited A.
  Variable f : A -> B.
  Variable y : B.

  Check @linv A B  hnonempty y f.
  Check linv y f.
End d.

Section c.
  Variable A B : Type.
  Variable hnonempty : inhabited A.
  
  (*                                                         ここを linv y f と書きたい。 *)
  Lemma linv_spec (y : B) (f : A -> B) : (exists x, f x = y) -> f (@linv A B hnonempty y f) = y.
  Proof.
    case=> x fx_y.
    rewrite /linv /dite.
    case: pselect => H //=.
    - by rewrite (projT2 (cid H)). (* lean の Classical.choose_spec h *)
    (* default のほうは、前提矛盾で使われない。 *)
    - exfalso.
      apply: H.
      by exists x.
  Qed.

End c.

(* END *)
