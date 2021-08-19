From mathcomp Require Import all_ssreflect.
Require Import ssrstring.                   (* Ascii String *)
(* Require Import Recdef. *)                (* Function *)
Require Import ssrinv.                      (* inv: *)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section CPL.
  
  Inductive object :=
  | I
  | dot of object & object
  | pair of (object * object)
  | pi1
  | pi2
  | pr of (object * object)
  | O
  | S
  | cur of object
  | ev
  .

  Notation "a \; b" := (dot a b).           (* 左結合 *)
  Notation "a \o b" := (dot a b).           (* 右結合 *)
  Check pi1 \; (pi1 \; pi1).
  Check (pi1 \o pi1) \o pi1.
  
(*
ev . pair (pr (curry(π2), 
               curry(s.ev)) . π1,
           π2)
 .
 pair (s.0, s.0)
*)
(*
  Definition add :=
    ev \o pair (pr (cur pi2,
                    cur (S \o ev)) \o pi1,
                pi2).
*)  
  Definition add :=
    ev \o pair (pr (cur pi2,
                    cur (S \o ev)) \o pi1,
                pi2).
  Definition one := S \o O.
  Definition two := S \o S \o O.
  
(*
  Inductive simp : object -> object -> Prop :=
  | s_l    a b c : simp a b -> simp (a \o c) (b \o c)
  | s_r    a b c : simp b c -> simp (a \o b) (a \o c)
  | dot_al a b c : simp ((a \o b) \o c) (a \o (b \o c))
  | dot_ar a b c : simp (a \o (b \o c)) ((a \o b) \o c)
  | pair_c a b c : simp (pair (a, b) \o c)
                        (pair (a \o c, b \o c))
  | pair_l a b   : simp (pi1 \o pair (a, b)) a
  | pair_r a b   : simp (pi2 \o pair (a, b)) b
  | pr_l   a b c : simp (     pr (a, b) \o (S \o c))
                        (b \o pr (a, b) \o c)
  | pr_r   a b :   simp (     pr (a, b) \o O) a
  | ev_a   a b :   simp (ev \o pair (cur(a), b)) (a \o b)
  .
*)
(*
add . pair (s.0, s.0)
ev . pair (pr (curry(π2), curry(s.ev)).π1, π2) . pair (s.0, s.0)
ev . pair (pr (curry(π2), curry(s.ev)).π1. pair (s.0, s.0), π2. pair (s.0, s.0))
          ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
pr (curry(π2), curry(s.ev)).π1. pair (s.0, s.0)
pr (curry(π2), curry(s.ev)).s.0
curry(s.ev) . pr (curry(π2), curry(s.ev)).0            -- pr の展開
curry(s.ev) . curry(π2)                                -- pr の展開

ev . pair (curry(s.ev) . curry(π2), π2. pair (s.0, s.0))
s. ev .  pair (curry(π2), π2. pair (s.0, s.0))        -- evaluate
s. π2 . pair (I,          π2. pair (s.0, s.0))        -- evaluate
s.                         π2. pair (s.0, s.0)
s. s.0
*)

(*
  Inductive simp : object -> object -> Prop :=
  | dot_cl a b c x : simp a b ->
                     simp (a \o c) x -> simp (b \o c) x
  | dot_cr a b c x : simp b c ->
                     simp (a \o b) x -> simp (a \o c) x
  | dot_al a b c x : simp (a \o (b \o c)) x ->
                     simp ((a \o b) \o c) x
  | dot_ar a b c x : simp ((a \o b) \o c) x ->
                     simp (a \o (b \o c)) x
  | pair_c a b c x : simp (pair (a \o c, b \o c)) x ->
                     simp (pair (a, b) \o c) x
  | pair_c' a b c x : simp (pair (a, b) \o c) x ->
                      simp (pair (a \o c, b \o c)) x
  | pair_l a b   x : simp a x -> simp (pi1 \o pair (a, b)) x
  | pair_r a b   x : simp b x -> simp (pi2 \o pair (a, b)) x
  | pr_l   a b c x : simp (b \o pr (a, b) \o c) x ->
                     simp (     pr (a, b) \o (S \o c)) x
  | pr_r   a b   x : simp a x ->
                     simp (     pr (a, b) \o O) a
  | ev_a   a b   x : simp (a \o b) x ->
                     simp (ev \o pair (cur(a), b)) x
  | same (a : object) : simp a a
  .
  

  Lemma test :
    simp ((pr (cur pi2, cur (S \o ev)) \o pi1) \o pair (S \o O, S \o O))
         (cur (S \o ev) \o cur pi2).
  Proof.
    apply: dot_al.
  Admitted.
  
  Goal simp (add \o pair (one, one)) two.
  Proof.
    rewrite /add /one.
    apply: dot_al.
    apply: (@dot_cr _
                    (pair (pr (cur pi2, cur (S \o ev)) \o pi1 \o pair (S \o O, S \o O),
                           pi2 \o                                pair (S \o O, S \o O)))).
    - apply: pair_c'.
        by apply: same.
 *)
  
  Lemma idL a : a \o I = a.
  Proof.
  Admitted.
  
  Lemma idR a : I \o a = a.
  Proof.
  Admitted.
  
  Lemma dotA a b c : a \o (b \o c) = a \o b \o c. (* 右結合 = 左結合 *)
  Proof.
  Admitted.
    
  Lemma pairC a b c : pair (a, b) \o c = pair (a \o c, b \o c).
  Proof.
  Admitted.

  Lemma pairL a b : pi1 \o pair (a, b) = a.
  Proof.
  Admitted.

  Lemma pairR a b : pi2 \o pair (a, b) = b.
  Proof.
  Admitted.

  Lemma prL a b c : pr (a, b) \o (S \o c) = b \o pr (a, b) \o c.
  Proof.
  Admitted.

  Lemma prR a b : pr (a, b) \o O = a.
  Proof.
  Admitted.
  
  Lemma eval a b c : ev \o pair (cur a \o b, c) = a \o pair (b, c).
  Proof.
  Admitted.

  Lemma eval1 a b : ev \o pair (cur a, b) = a \o pair (I, b).
  Proof.
    rewrite -[cur a]idL.
      by apply: eval.
  Qed.
  
  Goal add \o pair (one, one) = two.
  Proof.
    rewrite /add /one.
    rewrite -!dotA.                         (* 右結合 *)
    rewrite pairC.
    rewrite -!dotA.                         (* 右結合 *)
    rewrite pairL.
    rewrite prL.
    rewrite -!dotA.                         (* 右結合 *)
    rewrite prR.
    rewrite eval.
    rewrite -!dotA.                         (* 右結合 *)
    rewrite eval1.
    rewrite !pairR.
    rewrite /two.
    rewrite -!dotA.                         (* 右結合 *)
    done.
  Qed.

End CPL.


(* END *)
