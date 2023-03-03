(**
群の公理の完備化によって、autorewriteで自動証明をする。

@suharahiromichi
 *)

Variable gp : Type.
Variable addg : gp -> gp -> gp.
Variable oppg : gp -> gp.
Variable O : gp.
 
Notation "a + b" := (addg a b)(at level 50, left associativity).
Notation "a - b" := (addg a (oppg b))(at level 50, left associativity).
Notation "- a" := (oppg a)(at level 35, right associativity).

Section gproup.
  Variable a b c : gp.
  
  (* 公理 *)
  Axiom a1 : O + a = a.
  Axiom a2 : (- a) + a = O.
  Axiom a3 : (a + b) + c = a + (b + c).

  (* Knuth-Bendix 完備化アルゴリズムで追加された等式 *)
  Axiom r1 : -a + (a + b) = b.
  Axiom r2 : a + O = a.
  Axiom r3 : a + -a = O.
  Axiom r4 : a + (-a + b) = b.
  Axiom r5 : -O = O.
  Axiom r6 : - -a = a.
  Axiom r7 : -(b + a) = -a + -b.
End gproup.

Hint Rewrite a1 a2 a3 r1 r2 r3 r4 r5 r6 r7 : group.

Variable a b c d : gp.

Goal -a + (a + b) = b.
Proof.
  (* 公理のみで手動で証明する例。 *)
  rewrite <- a3.
  rewrite a2, a1.
  reflexivity.
  
  (* 完備化された等式を -> だけ使って、自動証明する。 *)
  Restart.
  autorewrite with group.
  reflexivity.
Qed.

Goal a + b + - b = a.
Proof.
  autorewrite with group.
  reflexivity.
Qed.

Goal a - b + c - c + b - a = O.
Proof.
  autorewrite with group.
  reflexivity.
Qed.

(**
# HOAS
*)
From elpi Require Import elpi.

(* Axiom 専用の print コマンド *)

Elpi Command print.
Elpi Accumulate lp:{{
main [str Name] :-
        coq.locate Name (const Const),
        coq.env.const Const none Type,    % 値はなく、型だけ存在する。
        coq.say "Type=" Type.
}}.
Elpi Typecheck.
Elpi print "a1".
(**
```
prod `a` {{gp}}
  c0 \ app [{{@eq}},
            {{gp}},
            app	[{{addg}}, {{O}}, c0],
            c0]
```
*)

(* Axiom を定義する例 *)
Elpi Command new_ax.
Elpi Accumulate lp:{{
main [str Name] :-
        Bo = (prod `a` {{gp}}
              c0 \ app [{{@eq}}, {{gp}},        % @eq としてください。
                        app	[{{addg}}, {{O}}, c0],
                        c0]),
        coq.say "Bo=" Bo,
        coq.env.add-axiom Name Bo Ax,
        coq.say "Ax=" Ax.
}}.
Elpi Typecheck.
Elpi new_ax "a1'".

Check a1.
Check a1'.

(**
# 参考文献

[1] 書き換えと計算機 Jacques gparrigue 2005年8月11～13日

[2] Proof Summit 2017

[3] Tutorial on the HOAS for Coq terms


https://lpcic.github.io/coq-elpi/tutorial_coq_elpi_HOAS.html
*)

(* END *)
