(**
Dependent if-then-else を Coq/MathComp で定義してみた。
 *)
From mathcomp Require Import all_ssreflect.
From mathcomp Require Import all_classical.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(**
Dependent if-then-else の定義
 *)
Definition dite {a : Type} (c : Prop) (t : c -> a) (e : ~ c -> a) : a.
Proof.
  case: (pselect c).
  - by apply: t.
  - by apply: e.
Defined.
Arguments dite {a} c t e.
Notation "'if' h 'of' c 'then' t 'else' e" := (dite c (fun h => t) (fun h => e)) (at level 200).

(**
使用例
*)
Section a.
  Variable A B : Type.
  Variable hnonempty : inhabited A.
  
(**
左逆関数の定義
*)
  Definition linv (b : B) (f : A -> B) :=
    dite (exists a, f a = b)
      (fun h => projT1 (cid h))    (* lean の Classical.choose_spec h *)
      (fun h => inhabited_witness hnonempty). (* default *)
  
(**
Notationのif-then-elseを使った例
*)
  Definition linv' (b : B) (f : A -> B) :=
    if h of exists a, f a = b then projT1 (cid h) else inhabited_witness hnonempty.

  Section d.
    Variable f : A -> B.
    Variable y : B.
    
    Check linv y f.
    Check linv' y f.
  End d.
  
(**
左逆関数が仕様を満たすことの証明
*)
  Lemma linv_spec (y : B) (f : A -> B) : (exists x, f x = y) -> f (linv y f) = y.
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

End a.

(**
補足

Lean にあるこの補題は証明できなさそう。左辺のcのインスタンスがhcと限らないため。
*)
Lemma dif_pos {a : Type} (c : Prop) (hc : c) (t : c -> a) (e : ~ c -> a) : dite c t e = t hc.
Proof.
  rewrite /dite.
  case: pselect => //=.
  Abort.

(* END *)
