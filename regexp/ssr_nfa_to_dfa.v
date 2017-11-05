(**
A Constructive Theory of Regular Languages in Coq (pdf)

において

Theorem 4.2 For every NFA (DFA) we can construct a DFA (NFA) accepting the same language.

を証明する箇所を抜粋する。
*)

(** Authors: Christian Doczkal and Jan-Oliver Kaiser *)
(** より抜粋 *)
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype
ssrnat seq choice fintype path fingraph  finfun  finset.

Set Implicit Arguments.

Section FA.
Variable char : finType.
Definition word := seq char.                (* reqexp.word *)

(** * Finite Automata *)

(** ** Deterministic Finite Automata *)

Record dfa : Type :=
  {
    dfa_state :> finType;
    dfa_s : dfa_state;
    dfa_fin : pred dfa_state;
    (* dfa_trans : dfa_state -> char -> dfa_state *)
    dfa_trans (x : dfa_state) (a : char) : dfa_state
    (* dfa_trans : {ffun dfa_state -> char -> dfa_state} *)
  }.

(** For DFAs, we use the direct recursive defintion of acceptance
    as well as a definition in terms of runs. The latter is used
    in the translation of DFAs to regular expressions. *)


Fixpoint dfa_accept {A : dfa} (x : A) w :=
  if w is a :: w' then dfa_accept (dfa_trans A x a) w' else x \in dfa_fin A.

Arguments dfa_trans [d] x a.
Arguments dfa_accept [A] x w.

Section DFA_Acceptance.
Variable A : dfa.

Lemma dfa_accept_cons (x : A) a w :
  a :: w \in dfa_accept x = (w \in dfa_accept (dfa_trans x a)).
Proof.
    by rewrite -simpl_predE /=.
Qed.
(* 必要なものだけ抜粋した。 *)
End DFA_Acceptance.


Definition dfa_lang A := [pred w | dfa_accept (dfa_s A) w].

(** ** Nondeterministic Finite Automata. *)
Record nfa : Type :=
  {
    nfa_state :> finType;
    nfa_s : nfa_state;
    nfa_fin : pred nfa_state;
    (* nfa_trans : nfa_state -> char -> nfa_state -> bool *)
    nfa_trans (x : nfa_state) (a : char) (y : nfa_state) : bool
  }.

(** Non-deterministic acceptance. **)
Fixpoint nfa_accept (A : nfa) (x : A) w :=
  if w is a :: w' then [exists y, nfa_trans A x a y && nfa_accept A y w']
                  else x \in nfa_fin A.

Definition nfa_lang (A : nfa) := [pred w | nfa_accept A (nfa_s A) w].


(** ** Equivalence of DFAs and NFAs *)
(** We use the powerset construction to obtain
   a deterministic automaton from a non-deterministic one. **)
Section PowersetConstruction.

Variable A : nfa.

Definition nfa_to_dfa :=
  {|
    dfa_s := [set nfa_s A];
    dfa_fin X := [exists x: A, (x \in X) && nfa_fin A x];
    dfa_trans X a := \bigcup_(x | x \in X) [set y | nfa_trans A x a y]
  |}.
Section TEST.
  (**
X : dfa ではなく、 A : nfa, X : {set A}、すなわち dfa≡{set A} とみなす。
これが、パワーセット・コンストラクションということなのだろう。
ここで、finSet が出てくるのがポイントである。
   *)
  Variable X : {set A}.
  Variable a : char.

  Check [set nfa_s A] : {set A}.
  Check [exists x: A, (x \in X) && nfa_fin A x] : bool.
  Check \bigcup_(x | x \in X) [set y | nfa_trans A x a y] : {set A}.
End TEST.

Lemma nfa_to_dfa_aux2 (x : A) w (X : nfa_to_dfa) :
  x \in X -> nfa_accept A x w -> dfa_accept X w.
Proof.
  move => H0.
  elim: w X x H0 => [|a w IHw] X x H0 /=.
  - move => H1.
    apply/existsP.
    exists x.
      by rewrite H0.
  - move => /= /existsP [] y /andP [] H1 H2.
    apply: (IHw _ y) => //.
    apply/bigcupP.
    exists x => //=.
      by rewrite in_set.
Qed.

Check @bigcupP : forall (T I : finType) (x : T) (P : pred I) (F : I -> {set T}),
    reflect (exists2 i : I, P i & x \in F i) (x \in \bigcup_(i | P i) F i).

Lemma nfa_to_dfa_aux1 (X : nfa_to_dfa) w :
  dfa_accept X w -> exists2 x, (x \in X) & nfa_accept A x w.
Proof.
  elim: w X => [|a w IHw] X => //=.
  - move/existsP => [x] /andP [] H0 H1.
    exists x; assumption.
  - move/IHw => [] y /bigcupP [x] H0.
    rewrite inE => H1 H2.
    exists x.
    + assumption.
    + apply/existsP.
      exists y.
        by apply/andP.
Qed.

Lemma nfa_to_dfa_correct : nfa_lang A =i dfa_lang nfa_to_dfa.
Proof.
  move => w.
  apply/idP/idP => /=.
  (* w \in nfa_lang A -> w \in dfa_lang nfa_to_dfa *)
  - apply: nfa_to_dfa_aux2.
      by apply/set1P.
  (* w \in dfa_lang nfa_to_dfa -> w \in nfa_lang A *)
  - by move/nfa_to_dfa_aux1 => [x] /set1P ->.
Qed.

End PowersetConstruction.


(** Embedding deterministic automata in non-deterministic automata. **)
Section Embed.

Variable A : dfa.

Definition dfa_to_nfa : nfa := {|
  nfa_s := dfa_s A;
  nfa_fin := dfa_fin A;
  nfa_trans x a y := y == dfa_trans x a |}.

Lemma dfa_to_nfa_correct : dfa_lang A =i nfa_lang dfa_to_nfa.
Proof.
  move => w. rewrite /dfa_lang /nfa_lang /=. move: (dfa_s A) => x.
  elim: w x => [|b w IHw] x //=.
  rewrite dfa_accept_cons IHw !inE /=. apply/idP/existsP.
    move => H0. exists (dfa_trans x b). by rewrite eq_refl.
  by move => [] y /andP [] /eqP ->.
Qed.

End Embed.



(* sample DFA & NFA *)

Definition dfa_char (a : char) :=
  {|
    dfa_s := false ;
    dfa_fin := id ;
    dfa_trans x b := if a == b then ~~ x else x
  |}.

Definition nfa_char a :=
  {|
    nfa_s := false ;
    nfa_fin := id ;
    nfa_trans x b y := [&& (b == a),  ~~ x & y]
  |}.
Print nfa_char.

Lemma nfa_char_correct a : nfa_lang (nfa_char a) =1 pred1 [:: a].
Proof.
 move => [|b w] => //.
 apply/existsP/eqP => [[x] /andP [/and3P [/eqP -> _ Hx]] |[-> ->]].
 - case: w => //= c w /existsP [y] /=. by rewrite Hx andbF.
 - exists true. by rewrite /= eqxx.
Qed.

(* END *)
