(**
末尾再帰判定するコマンド

2023_2_23

@suharahiromichi

see. prolog/elpi/minifp.elpi
*)

From elpi Require Import elpi.

Fixpoint fib (n : nat) : nat :=
	match n with
	| O => O
	| S m => match m with
			 | O => 1
			 | S m' => fib m + fib m'
			 end
	end.
Compute fib 10.							(* 55 *)

Fixpoint trec_fib (n a b : nat) : nat :=
	match n with
	| 0 => a
	| S m => trec_fib m b (a + b)
	end.
Compute trec_fib 10 0 1.				(* 55 *)

Fixpoint fact (n : nat) : nat :=
	match n with
	| O => 1
	| S m => n * fact m
	end.
Compute fact 5.							(* 120 *)

Fixpoint trec_fact (n a : nat) :nat :=
	match n with
	| 0 => a
	| S m => trec_fact m (n * a)
	end.
Compute trec_fact 5 1.					(* 120 *)

(**
fix (f\ M) の f が、match(ネストしてもよい)の節の最外側に限って出現することをチェックする。

ただし、まだ「限って」のチェックはしていない。
*)
Elpi Command tailrec.
Elpi Accumulate lp:{{

pred trec i:term i:term.
trec F M :- coq.say "trec=" F "," M, fail.		% Check
trec F (fun _ _ M) :- pi n\ trec F (M n).
trec F (match _ _ L) :- std.exists L (trec F).	% match節のリストLのどれかひとつが成立する。
%trec F (match _ _ [N, _]) :- trec F N.
%trec F (match _ _ [_, N]) :- trec F N.
trec F (app [F | _]).

main [str Name] :-
	coq.locate Name (const Const),
  	coq.env.const Const (some Bo) Ty,
  	coq.say "tailrec=" Bo,						% Check
	Bo = fix _ _ _ M,
	pi f\ trec f (M f).
main [str Name] :-	
	coq.say Name "IS NOT A RECURCEIVE FUNCTION.",
	!, fail.
}}.
Elpi Typecheck.

Fail Elpi tailrec fib.
Elpi tailrec trec_fib.
Fail Elpi tailrec fact.
Elpi tailrec trec_fact.

(* END *)
