From mathcomp Require Import all_ssreflect.
Require Import ssrstring.                   (* Ascii String *)
(* Require Import Recdef. *)                (* Function *)
Require Import ssrinv.                      (* inv: *)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section CPL_DEF.
  
  Inductive object :=
  | I
  | dot of object & object
  | prod of (object * object)
  | pair of (object * object)
  | pi1
  | pi2
  | pr of (object * object)
  | O
  | S
  | exp of (object * object)
  | cur of object
  | ev
  .

End CPL_DEF.

Notation "a \; b" := (dot a b).             (* 左結合 *)
Notation "a \o b" := (dot a b).             (* 右結合 *)

Check pi1 \; (pi1 \; pi1).
Check (pi1 \o pi1) \o pi1.

Section CPL_SEMANTICS.

  Inductive step : object -> object -> Prop :=
  | id_l   {a}     : step (I \o a) a
  | id_r   {a}     : step (a \o I) a
(*| s_l    {a b c} : step a b -> step (a \o c) (b \o c)
  | s_r    {a b c} : step b c -> step (a \o b) (a \o c) *)
  | dot_al {a b c} : step ((a \o b) \o c) (a \o (b \o c))
  | dot_ar {a b c} : step (a \o (b \o c)) ((a \o b) \o c)

  (* prod : 右関手 *)
  | prod_c {a b}   : step (prod (a, b))
                          (pair (a \o pi1, b \o pi2))
  (* pair : 右仲介射 *)
  | pair_c {a b c} : step (pair (a, b) \o c)
                          (pair (a \o c, b \o c))
  (* pi1 : 右自然変換 *)
  (* pi2 : 右自然変換 *)
  | pair_l {a b}   : step (pi1 \o pair (a, b)) a
  | pair_r {a b}   : step (pi2 \o pair (a, b)) b

  (* pr : 左仲介射 *)
  | pr_l   {a b}   : step (     pr (a, b) \o S)
                          (b \o pr (a, b))
  | pr_r   {a b}   : step (     pr (a, b) \o O) a

  (* ev : 右自然変換 *)
  | ev_d   {a}     : step (ev \o prod (cur a, I)) a
  | ev_a   {a b c} : step (ev \o pair (cur a \o c, b))
                          (a  \o pair (c, b))
  (* exp : 右関手 *)
  | exp_e  {a b}   : step (exp (a, b))
                          (cur b \o ev \o prod (I, a))
  .

(**
```
--------|---------|--------|-------------|------
        | 関手    | 仲介射  | 自然変換    | 型
--------|---------|--------|-------------|------
右      | 1       | !      | -           | -
左      | 0       | !!     | -           | -
右      | prod    | pair   | pi1, pi2    | A, B
左      | coprod  | case   | in1, in2    | A, B
右      | exp     | cur    | ev          | A, B
左      | bool    | if     | true, false | 1
左      | nat     | pr     | O, S        | 1
左      | list    | fold   | nil, cons   | A
右      | inflist | unfold | get, next   | A
--------|---------|--------|-------------|------
```
*)
  
  Axiom AX : forall {a b}, step a b -> a = b.
  
  Lemma ida1 a : a \o I = a.
  Proof.
      by apply: (AX id_r).
  Qed.
  
  Lemma id1a a : I \o a = a.
  Proof.
      by apply: (AX id_l).
  Qed.
  
  Lemma dotA a b c : a \o b \o c = a \o (b \o c). (* 左結合 = 右結合 *)
  Proof.
      by apply: (AX dot_al).
  Qed.
  
  Lemma prodC a b : prod (a, b) = pair (a \o pi1, b \o pi2).
  Proof.
      by apply: (AX prod_c).
  Qed.

  Lemma pairC a b c : pair (a, b) \o c = pair (a \o c, b \o c).
  Proof.
      by apply: (AX pair_c).
  Qed.
  
  Lemma pairL a b : pi1 \o pair (a, b) = a.
  Proof.
      by apply: (AX pair_l).
  Qed.
  
  Lemma pairR a b : pi2 \o pair (a, b) = b.
  Proof.
      by apply: (AX pair_r).
  Qed.
  
  Lemma prL a b : pr (a, b) \o S = b \o pr (a, b).
  Proof.
      by apply: (AX pr_l).
  Qed.
  
  Lemma prR a b : pr (a, b) \o O = a.
  Proof.
      by apply: (AX pr_r).
  Qed.
  
  Lemma eval a b c : ev \o pair (cur a \o b, c) = a \o pair (b, c).
  Proof.
    by apply: (AX ev_a).
  Qed.
  
  (* eval の終了時の特別な形 *)
  Lemma eval1 a b : ev \o pair (cur a, b) = a \o pair (I, b).
  Proof.
    rewrite -[cur a]ida1.
      by apply: eval.
  Qed.

End CPL_SEMANTICS.

(**
sample
*)  
Section Sample.
  
  Definition one := S \o O.
  Definition two := S \o S \o O.

  Definition double := pr (O, S \o S).

  Goal double \o one = two.
  Proof.
    rewrite /double /one.
    rewrite -!dotA.                         (* 左結合 *)
    rewrite prL.
    rewrite !dotA.                          (* 右結合 *)
    rewrite prR.
    rewrite /two.
    rewrite !dotA.                          (* 右結合 *)
    done.
  Qed.
  
(**
add
*)
  Definition add := ev \o pair (pr (cur pi2,
                                    cur (S \o ev)) \o pi1,
                                pi2).
  
  Goal add \o pair (one, one) = two.
  Proof.
    rewrite /add /one.
    rewrite !dotA.                          (* 右結合 *)
    rewrite pairC.
    rewrite !dotA.                          (* 右結合 *)
    rewrite pairL.
    rewrite -!dotA.                         (* 左結合 *)
    rewrite prL.
    rewrite !dotA.                          (* 右結合 *)
    rewrite prR.
    rewrite eval.
    rewrite !dotA.                          (* 右結合 *)
    rewrite eval1.
    rewrite !pairR.
    rewrite /two.
    rewrite !dotA.                          (* 右結合 *)
    done.
  Qed.

  Definition add_alt := ev \o prod (pr (cur pi2, cur (S \o ev)), I).
  
  Goal add_alt \o pair (one, one) = two.
  Proof.
    rewrite /add /one.
    rewrite !dotA.                          (* 右結合 *)
    rewrite prodC.
    rewrite pairC.
    rewrite !dotA.                          (* 右結合 *)
    rewrite pairL.
    rewrite -!dotA.                         (* 左結合 *)
    rewrite prL.
    rewrite !dotA.                          (* 右結合 *)
    rewrite prR.
    rewrite eval.
    rewrite !dotA.                          (* 右結合 *)
    rewrite eval1.
    rewrite !pairR.
    rewrite /two.
    rewrite !dotA.                          (* 右結合 *)
    rewrite id1a.
    done.
  Qed.
  
(**
mult
*)  
  Definition mult := ev \o prod (pr (cur (O \o I),
                                     cur (add \o pair (ev, pi2))),
                                 I).

  Goal mult \o pair (O, O) = O.
  Proof.
    rewrite /mult.
    rewrite prodC.
    rewrite !dotA.
    rewrite pairC.
    rewrite !id1a.
    rewrite !ida1.
    rewrite !dotA.
    rewrite !pairR.
    rewrite !pairL.
    rewrite -!dotA.
    rewrite prR.
    rewrite eval1.
    (* O \o pair (I, O) = O *)
  Admitted.

(**
fact
*)
  Definition fact := pi1 \o pr (pair (S \o O, O),
                                pair (mult \o pair (S \o pi2,
                                                    pi1),
                                      S \o pi2)).

End Sample.


Section NotUsed.

  Fixpoint simp a :=
    match a with
    | I \o a => simp a
    | a \o I => simp a
    | prod (a, b) => pair (simp a \o pi1, simp b \o pi2)
    | pair (a, b) \o c => pair (simp a \o simp c, simp b \o simp c)
    | pi1 \o pair (a, b) => simp a
    | pi2 \o pair (a, b) => simp b
    | pr (a, b) \o S => simp b \o pr (simp a, simp b)
    | pr (a, b) \o O => simp a
    | ev \o prod (cur a, I) => simp a
    | ev \o pair (cur a \o c, b) => simp a \o pair (simp c, simp b)
    | ev \o pair (cur a, b) => simp a \o pair (I, simp b)
    | exp (a, b) => cur (simp b) \o ev \o prod (I, simp a)
    | _ => a
    end.

  Lemma test a b : simp a = b -> a = b.
  Proof.
  Admitted.

End NotUsed.


(* END *)
