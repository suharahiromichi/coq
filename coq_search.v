(**
https://raw.githubusercontent.com/tchajed/coq-tricks/master/src/Search.v
*)

Require Import Arith.

(**
plus 関数を含む定理
*)
Search plus.

(**
plus と minus 関数を同時に含む定理
*)
(* by default search components are AND'd together, so more components results
in a more specific search *)
Search plus minus.

(**
notation で検索する、このときは「"」で囲む。
*)
(* searching for notations - note that this has to be a token corresponding to
exactly one notation (for more general searches, first find the right pattern
with Locate and then search for that) *)
Search "-" "+".

(**
パターンで探す。非線形パターン(1つのパターン内で同じ変数が複数現れる)が使える。
*)
(* search patterns can be non-linear (within one component) *)
Search (_ + ?a - ?a).

Search sumbool (@eq bool _ _).

Search ({_=_} + {_<>_}).

(* Note that there is another theorem if this form in ProofIrrelevance (that
works without decidable equality but requires the axiom of proof irrelevance -
the search will not find it if ProofIrrelevance has not been Require'd. *)
Search (existT ?P ?x _ = existT ?P ?x _).

Search plus inside List.

(**
定理の名前に含まれる文字列でも検索できる。
*)
(* searches use the name of the theorem if the string is an identifier *)
Search "dec" "<".

(**
notationの mod で検索したい場合で検索する。
*)
(* mod is part of a notation, but searching for ["mod"] will look for the string
in the lemma name; to search for the notation search for the keyword with
["'mod'"]. (note that Nat.testbit_eqb, for example, does not have mod in the name) *)
Search "'mod'" 2.
(**
定理の名前に mod を含む場合で検索する。
*)
Search "mod" 2.

(**
上記よりも、こっちのほうがよい。
*)
(* the above search would probably be better done like this: *)
Search (_ mod 2).

(**
MCB のチートシート
*)
From mathcomp Require Import all_ssreflect.
Search (_ > _).

Search _ addn (_ + _) "C" in ssrnat.
(**
```
addnACl: forall m n p : nat, m + n + p = n + (p + m)
addnCAC: forall m n p : nat, m + n + p = p + n + m
subnKC: forall [m n : nat], m <= n -> m + (n - m) = n
addnBAC: forall [m n : nat] (p : nat), n <= m -> m - n + p = m + p - n
addnBCA: forall [m n p : nat], p <= m -> p <= n -> m + (n - p) = n + (m - p)
addnABC: forall [m n p : nat], p <= m -> p <= n -> m + (n - p) = m - p + n
nat_Cauchy: forall m n : nat, 2 * (m * n) <= m ^ 2 + n ^ 2 ?= iff (m == n)
```
*)

(**
Search for all theorems with no constraints on the main conclusion
(conclusion head symbol is the wildcard _), that talk about the addn constant,
matching anywhere the pattern (_ * _) and having a name containing the string "C"
in the module ssrnat caveat in the general form, the iterated operation op
is displayed in pre x form (not in in x form) caveat the string "big" occurs in
every lemma concerning iterated operations.
*)

(**
- 定理の結論から検索します(結論の頭の記号はワイルドカード _ です)。
- addn 定数について検索し
- どこでもパターン (_ * _) に一致し
- モジュール ssrnat で
- 文字列「C」を含む名前を持ちます。
*)

(** 以上 *)
