From elpi Require Import elpi.

Elpi Tactic show.
Elpi Accumulate lp:{{
  solve (goal Ctx Trigger Type Proof Args) _ :-
  coq.say "Goal:" Ctx "|-" Proof ":" Type.
}}.
Elpi Typecheck.

(**
exists の証明を refine で解いた例
*)
Goal forall (A : Type) (P : A -> Prop) (x : A),
	P x -> exists y, P y.
Proof.
  intros A P x H.
  elpi show.
  Check @ex_intro A P x H.
(* refine (ex_intro _ _ H). *)
(* refine (@ex_intro A P x H). *)
  refine (@ex_intro _ _ x H).
Qed.

(**
Coq-Elpiのサンプルコードを使用した例　exists x, x = 1
https://github.com/LPCIC/coq-elpi/blob/master/tests/test_tactic.v
*)
Elpi Tactic pf_exists.
Elpi Accumulate lp:{{
  solve (goal _ Trigger _ Ev _) GS1 :-
  	Trigger = {{ ex_intro (fun x : nat => x = 1) _ _ }},
    coq.ltac.collect-goals Ev GS Shelved,
    std.append GS Shelved GS1,
    std.assert! (std.length GS1 2) "not 2 goals".
  solve _ _ :-
    coq.ltac.fail _ "cannot pf_exists".
}}.
Elpi Typecheck.

Goal exists x, x = 1.
Proof.
    elpi pf_exists.
    easy.
Qed.

(**
上記のサンプルコードと同じだが A と P を引数で与えた例
*)
Elpi Tactic pf_exists2.
Elpi Accumulate lp:{{
  solve (goal _ Trigger _ Ev [trm A, trm P]) GS1 :-
  	Trigger = {{ ex_intro (fun x : lp:A => lp:P x) _ _ }},
    coq.ltac.collect-goals Ev GS Shelved,
    std.append GS Shelved GS1,
    std.assert! (std.length GS1 2) "not 2 goals".
  solve _ _ :-
    coq.ltac.fail _ "cannot pf_exists".
}}.
Elpi Typecheck.

Goal forall (A : Type) (P : A -> Prop) (x : A),
	P x -> exists y, P y.
Proof.
  intros A P x H.
  elpi pf_exists2 (A) (P).
  apply H.
Qed.

Goal forall (A : Type) (P : A -> Prop) (x : A) (z : A),
	P x -> exists y, P y.
Proof.
  intros A P x z H.   (* A なる変数が複数あってもよい。 *)
  elpi pf_exists2 (A) (P).
  apply H.
Qed.

(*
A と P の指定は不要である。
*)
Elpi Tactic pf_exists0.
Elpi Accumulate lp:{{
  solve (goal _ Trigger _ Ev []) GS1 :-
  	Trigger = {{ ex_intro (fun x : lp:_ => lp:_ x) _ _ }},
    coq.ltac.collect-goals Ev GS Shelved,
    std.append GS Shelved GS1,
    std.assert! (std.length GS1 2) "not 2 goals".
  solve _ _ :-
    coq.ltac.fail _ "cannot pf_exists".
}}.
Elpi Typecheck.

Goal forall (A : Type) (P : A -> Prop) (x : A) (z : A),
	P x -> exists y, P y.
Proof.
  intros A P x z H.   (* A なる変数が複数あってもよい。 *)
  elpi pf_exists0.
  apply H.
Qed.



(* ***** *)
(* 盛田氏 *)
(* ***** *)
Elpi Tactic pf_or.
Elpi Accumulate lp:{{
  solve (goal Ctx Trigger {{ lp:A \/ lp:B }} Proof Args as G) GL :-
    std.mem Ctx (decl HA _ A), coq.say "decl" HA ":" A,
    Trigger = {{ or_introl lp:HA }}.
  solve (goal Ctx Trigger {{ lp:A \/ lp:B }} Proof Args as G) GL :-
    std.mem Ctx (decl HB _ B), coq.say "decl" HB ":" B,
    Trigger = {{ or_intror lp:HB }}.
  solve _ _ :-
   coq.ltac.fail _ "cannot pf_or".
}}.
Elpi Typecheck.

Lemma test13 : forall (P Q : Prop), P -> (P \/ Q).
Proof.
 intros P HP HQ.
 elpi pf_or.
Qed.

Elpi Tactic pf_exists.
Elpi Accumulate lp:{{
  solve (goal Ctx Trigger (X0 c0 c1 c2 c3) Proof [trm P, trm X, trm H] as G) GL :-
    std.mem Ctx (decl c3 _ (app [c1, c2])),
    std.mem Ctx (decl c2 _ c0), 
    std.mem Ctx (decl c1 _ (prod _ c0 c4 \ sort prop)),
    Trigger = ex_intro P X H.
/*  Trigger = ex_intro c1 c2 c3. */
/*  Trigger = {{ ex_intro lp:c1 lp:c2 lp:c3 }}. */
/*  Trigger = {{ ex_intro lp:P lp:X lp:H }}. */
solve _ _ :-
   coq.ltac.fail _ "cannot pf_exists".
}}.
Elpi Typecheck.

Print ex_intro.

Goal forall (A : Type) (P : A -> Prop) (x : A), P x -> exists y, P y.
Proof.
  intros A P x H.
  Check @ex A P.
  refine (ex A P).
(* refine (ex_intro P x H). *)
  elpi pf_exists P x H.
  Print ex_intro.
  Abort.
