From mathcomp Require Import all_ssreflect.

Inductive bird : Set :=
| app : bird -> bird -> bird.

(* ******* *)

Theorem thm1_ssr' :
  (forall (A B : bird),
    exists (C : bird), forall (x : bird), app A (app B x) = app C x) ->
  (exists (M : bird), forall (x : bird), app M x = app x x) ->
  (forall (P : bird),
    exists (x : bird), app P x = x).
Proof.
  move=> Hc Hm P.
  case: Hm => [M Hm'].       (* Hm' は ものまね鳥M についての命題。 *)
  case: (Hc P M) => [PM Hc']. (* Hc' は P と M を合成した、鳥PMについての命題。 *)
  exists (app M PM).          (* 鳥P は、鳥MPMが好き、とする。 *)
  rewrite Hc'.                (* 左辺のP と Mから合成鳥PMを得る。 *)
  rewrite Hm'.            (* 右辺のM PM からものまね鳥 M M を得る。 *)
    by [].
Qed.

(* ******* *)

Section Birds.
  
  Variable M : bird.              (* ものまね鳥 *)
  Variable P : bird.              (* 誰かを好きな鳥、誰かを求めたい *)

  (* ものまね鳥の定義 *)
  Hypothesis mock : forall (x : bird), app M x = app x x. (*  *)

  (* 鳥の合成の定義（合成の作り方） *)
  Hypothesis comp : forall (A B x : bird), app A (app B x) = app (app A B) x. (*  *)

  Goal exists (x : bird), app P x = x.
  Proof.
    move: comp => Hc.
    move: mock => Hm.
    move: (Hc P M) => {Hc} Hc.
    exists (app M (app P M)).
    rewrite Hc.
    rewrite Hm.
      by [].
  Qed.

  (* さらにまとめる。 *)

  Lemma thm1_ssr : exists (x : bird), app P x = x.
  Proof.
    move: (comp P M) => Hc.
    exists (app M (app P M)).               (* M (P M) *)
      by rewrite Hc mock.
  Qed.
  
(* M (P M) は、P の不動点 fixed point である、という。 *)

End Birds.


Check thm1_ssr'
  : (forall A B : bird, exists C : bird, forall x : bird, app A (app B x) = app C x) ->
    (exists M : bird, forall x : bird, app M x = app x x) ->
    forall P : bird, exists x : bird, app P x = x.

Check thm1_ssr
  : forall M P : bird,
    (forall x : bird, app M x = app x x) ->
    (forall A B x : bird, app A (app B x) = app (app A B) x) ->
    exists x : bird, app P x = x.

(* END *)
