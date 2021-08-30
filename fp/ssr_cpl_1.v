From mathcomp Require Import all_ssreflect.
Require Import ssrstring.                   (* Ascii String *)
(* Require Import Recdef. *)                (* Function *)
Require Import ssrinv.                      (* inv: *)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section CPL_DEF.

  Inductive object :=
  | i                                       (* ! *)
  | I                                       (* 恒等射 *)
  | dot of object & object                  (* 合成 *)
  (* *** *)
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

Notation "f \; g" := (dot f g).             (* 左結合 *)
Notation "f \o g" := (dot f g).             (* 右結合 *)

Check pi1 \; (pi1 \; pi1).
Check (pi1 \o pi1) \o pi1.

Section CPL_SEMANTICS.

  Inductive step : object -> object -> Prop :=
  | id_l   {f}     : step (I \o f) f
  | id_r   {f}     : step (f \o I) f
(*| s_l    {f g h} : step f g -> step (f \o h) (b \o h)
  | s_r    {f g h} : step g h -> step (f \o g) (f \o h) *)
  | dot_al {f g h} : step ((f \o g) \o h) (f \o (g \o h))
  | dot_ar {f g h} : step (f \o (g \o h)) ((f \o g) \o h)

  (* prod : 右関手 *)
  | prod_c {f g}   : step (prod (f, g))
                          (pair (f \o pi1, g \o pi2))
  (* pair : 右仲介射 *)
  | pair_c {f g h} : step (pair (f, g) \o h)
                          (pair (f \o h, g \o h))
  (* pi1 : 右自然変換 *)
  (* pi2 : 右自然変換 *)
  | pair_l {f g}   : step (pi1 \o pair (f, g)) f
  | pair_r {f g}   : step (pi2 \o pair (f, g)) g

  (* pr : 左仲介射 *)
  | pr_l   {f g}   : step (     pr (f, g) \o S)
                          (g \o pr (f, g))
  | pr_r   {f g}   : step (     pr (f, g) \o O) f

  (* ev : 右自然変換 *)
  | ev_d   {f}     : step (ev \o prod (cur f, I)) f
  | ev_a   {f g h} : step (ev \o pair (cur f \o h, g))
                          (f  \o pair (h, g))
  (* exp : 右関手 *)
  | exp_e  {f g}   : step (exp (f, g))
                          (cur g \o ev \o prod (I, f))
  .

(**
```
--------|---------|--------|-------------|------
        | 関手 F  | 仲介射ψ | 自然変換α | 型 E
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
  
  Axiom AX : forall {f g}, step f g -> f = g.
  
  Lemma ida1 f : f \o I = f.
  Proof.
      by apply: (AX id_r).
  Qed.
  
  Lemma id1a f : I \o f = f.
  Proof.
      by apply: (AX id_l).
  Qed.
  
  Lemma dotA f b c : f \o b \o c = f \o (b \o c). (* 左結合 = 右結合 *)
  Proof.
      by apply: (AX dot_al).
  Qed.
  
  Lemma prodC f g : prod (f, g) = pair (f \o pi1, g \o pi2).
  Proof.
      by apply: (AX prod_c).
  Qed.

  Lemma pairC f g h : pair (f, g) \o h = pair (f \o h, g \o h).
  Proof.
      by apply: (AX pair_c).
  Qed.
  
  Lemma pairL f g : pi1 \o pair (f, g) = f.
  Proof.
      by apply: (AX pair_l).
  Qed.
  
  Lemma pairR f g : pi2 \o pair (f, g) = g.
  Proof.
      by apply: (AX pair_r).
  Qed.
  
  Lemma prL f g : pr (f, g) \o S = g \o pr (f, g).
  Proof.
      by apply: (AX pr_l).
  Qed.
  
  Lemma prR f g : pr (f, g) \o O = f.
  Proof.
      by apply: (AX pr_r).
  Qed.
  
  Lemma eval f g h : ev \o pair (cur f \o g, h) = f \o pair (g, h).
  Proof.
    by apply: (AX ev_a).
  Qed.
  
  (* eval の終了時の特別な形 *)
  Lemma eval1 f g : ev \o pair (cur f, g) = f \o pair (I, g).
  Proof.
    rewrite -[cur f]ida1.
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
    
    rewrite pairR.

    rewrite prL.
    rewrite !dotA.                          (* 右結合 *)
    rewrite prR.
    rewrite eval.
    rewrite !dotA.                          (* 右結合 *)
    rewrite eval1.
    rewrite pairR.
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
    
    rewrite pairR.
    
    rewrite prR.
    rewrite eval.
    rewrite !dotA.                          (* 右結合 *)
    rewrite eval1.
    rewrite pairR.
    rewrite /two.
    rewrite !dotA.                          (* 右結合 *)
    rewrite id1a.
    done.
  Qed.
  
(**
mult
*)  
  (* O \o ! である。 *)
  Definition mult := ev \o prod (pr (cur (O \o i),
                                     cur (add \o pair (ev, pi2))),
                                 I).

  Goal mult \o pair (O, O) = O.
  Proof.
    rewrite /mult.
    rewrite prodC.
    rewrite !dotA.
    rewrite pairC.
    rewrite !id1a.
(*    rewrite !ida1. *)
    rewrite !dotA.
    rewrite !pairR.
    rewrite !pairL.
    rewrite -!dotA.
    rewrite prR.
    rewrite eval1.
    (* O \o pair (I, O) = O *)
    (* (O \o !) \o pair (I, O) = O *)
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

  Fixpoint simp f :=
    match f with
    | I \o f => simp f
    | f \o I => simp f
    | prod (f, g) => pair (simp f \o pi1, simp g \o pi2)
    | pair (f, g) \o c => pair (simp f \o simp c, simp g \o simp c)
    | pi1 \o pair (f, g) => simp f
    | pi2 \o pair (f, g) => simp g
    | pr (f, g) \o S => simp g \o pr (simp f, simp g)
    | pr (f, g) \o O => simp f
    | ev \o prod (cur f, I) => simp f
    | ev \o pair (cur f \o c, b) => simp f \o pair (simp c, simp b)
    | ev \o pair (cur f, g) => simp f \o pair (I, simp g)
    | exp (f, g) => cur (simp g) \o ev \o prod (I, simp f)
    | _ => f
    end.

  Lemma test f g : simp f = g -> f = g.
  Proof.
  Admitted.
  
End NotUsed.


(* END *)
