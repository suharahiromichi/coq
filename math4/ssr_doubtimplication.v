From mathcomp Require Import all_ssreflect.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section DoubtImplication.
  
  (** 含意が満たすべき性質を満たす「何か」 *)
  Variable Imp : bool -> bool -> bool.

  (** 含意っぽい記法の導入 `v` は `virtual` の略 *)
  Notation "x ->v y" := (Imp x y) (at level 98, left associativity).

  Section a.
    
    Variable p q r : bool.
    
    (** 含意は反射的。前提 p が真だろうと偽だろうと「p ならば p」は正しい。 *)
    Axiom imp_reflexive : p ->v p.
    
    (** 含意は推移的 *)
    Axiom imp_transitive : p ->v q -> q ->v r -> p ->v r.
    
    (** モーダスポネンス。「p ならば q」は、p が正しければ q が成り立つことを意味する。 *)
    Axiom imp_elim : p ->v q -> p ==> q.
    
    (** 結論が無条件に正しいなら、仮定をつけても正しい *)
    Axiom imp_intro : q -> p ->v q.
    
    (** ある前提から `q` と `r` が導出できるなら、`q ∧ r` も導出できる *)
    Axiom intro_and : p ->v q -> p ->v r -> p ->v (q && r).
    
    (** ある前提から `q ∧ r` が導出できるなら、`q` も導出できる *)
    Axiom elim_and_left : p ->v (q && r) -> p ->v q.
    
    (** ある前提から `q ∧ r` が導出できるなら、`r` も導出できる *)
    Axiom elim_and_right : p ->v (q && r) -> p ->v r.
    
    (** ある前提から `q` が導出できるなら、`q ∨ r` が導出できる *)
    Axiom intro_or_left : p ->v q -> p ->v (q || r).
    
    (** ある前提から `r` が導出できるなら、`q ∨ r` が導出できる *)
    Axiom intro_or_right : p ->v r -> p ->v (q || r).
    
  End a.

  (* 爆発定理を証明する。 *)
  Lemma imp_explosion (p : bool) : false ->v p.
  Proof.
    apply: (@elim_and_left false p false).
    rewrite andbF.
    apply: imp_reflexive.
  Qed.
  
  (* 証明したいもの。 *)
  Theorem imp_valid (p q : bool) : (p ->v q) <-> (p ==> q).
  Proof.
    split.
    - by apply: imp_elim.
    - rewrite /implb.
      case: ifP.
      + move=> HP.
        by apply: imp_intro.
      + move=> HnP _.
        by apply: imp_explosion.
  Qed.
  
End DoubtImplication.

(* END *)
