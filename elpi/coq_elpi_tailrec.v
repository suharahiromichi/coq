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
*)
Elpi Command tailrec.
Elpi Accumulate lp:{{
/**
app の先頭に出現するならば、successとする。
*/
pred trec i:term i:term.
%trec F M :- coq.say "trec=" F "," M, fail.		% Check
trec F (fun _ _ M) :- pi n\ trec F (M n).
trec F (match _ _ L) :-	std.exists L (trec F).
trec F (app [F | _]).
trec F (app [N | _]) :- trec F N.

/**
app の先頭以外に出現するならば、successとする。
*/
pred occr i:term i:term.
%occr F M :- coq.say "occr=" F "," M, fail.		% Check
occr F (fun _ _ M) :- pi n\ occr F (M n).
occr F (match _ _ L) :-	std.exists L (occr F).
% appの先頭にFが出現した場合は、それ以外の箇所だけでを見る。
occr F (app [F | L]) :- !, std.exists L (occr F).
occr F (app [N | L]) :- occr F N, !, std.exists L (occr F).
% appの先頭にFが出現ししない場合は、全体を見る。
occr F (app L) :- std.exists L (occr F).
occr F F.

/**
どこにでも出現するならば、successとする。(不使用)
*/
pred in i:term i:term.
%in F M :- coq.say "in=" F "," M, fail.			% Check
in F (fun _ _ M) :- pi n\ in F (M n).
in F (match _ _ L) :- std.exists L (in F).
in F (app L) :- std.exists L (in F).
in F F.

main [str Name] :-
	coq.locate Name (const Const),
  	coq.env.const Const (some Bo) Ty,
  	coq.say "tailrec=" Bo,						% Check
	Bo = fix _ _ _ M,
	pi f\ trec f (M f),
	not (pi f\ occr f (M f)).					% おかしくなったらここを外す！
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
