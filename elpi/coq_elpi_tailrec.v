(**
末尾再帰判定するコマンド

2023_2_23

@suharahiromichi

see. prolog/elpi/minifp.elpi
*)

From elpi Require Import elpi.

(**
% Fibonacci
prog "fib" 
(fix fib\ abs n\
  ite (eq n (i 0)) % if
      (i 0)        % then 
      (ite (eq n (i 1))
           (i 1)
           (sum (app fib (minus n (i 1))) (app fib (minus n (i 2))))
      )
).

% Tail-recursive Fibonattii
prog "trec-fib"
(fix fib\ abs n\ abs a\ abs b\
  ite (eq n (i 0))
      a
%     (app (app (app fib (minus (app fib n) (i 1))) b) (sum a b))   % 無理に末尾
再帰でない例
      (app (app (app fib (minus n (i 1))) b) (sum a b))             % OK
).

% Factorial
prog "fact" 
(fix fact\ abs n\
  ite (gt n (i 0)) 
      (times n (app fact (minus n (i 1))))
      (i 1)
).

% Tail-recursive factorial
prog "trec-fact"
(fix fact\ abs n\ abs m\
  ite (eq n (i 0)) 
      m
      (app (app fact (minus n (i 1))) (times n m))
).
*)

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
trec F M :- coq.say "trec=" F "," M, fail.
trec F (fun _ _ M) :- pi n\ trec F (M n).
trec F (match _ _ [N, _]) :- trec F N.
trec F (match _ _ [_, N]) :- trec F N.
trec F (app [F | _]).

/*
trec F (abs M) :- pi n\ trec F (M n).

% fix (f\ M) の f が、以下の場所に限って出現すること。
trec _ M :- print M, fail.
trec F (ite C N _) :- not (in F C), trec F N.         % then節
trec F (ite C _ N) :- not (in F C), trec F N.         % else節
trec F (app F M) :- not (in F M).                     % apply の第一引数
trec F (app N M) :- trec F N, not (in F M).
*/

main [str Name] :-
	coq.locate Name (const Const),
  	coq.env.const Const (some Bo) Ty,
  	coq.say "tailrec=" Bo,
	Bo = fix _ _ _ M,
	pi f\ trec f (M f).
}}.
Elpi Typecheck.

Fail Elpi tailrec fib.
Elpi tailrec trec_fib.
Fail Elpi tailrec fact.
Elpi tailrec trec_fact.

(* END *)
