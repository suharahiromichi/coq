(**
   GEB の TNT で証明された定理を Coq で証明する。
   2011_10_22
   *)


(** s と 「+」を定義する。*)
Inductive Nat : Set :=
| O : Nat
| s : Nat -> Nat.
Variable add : Nat -> Nat -> Nat.
Infix ".+" := add (at level 61, left associativity).


(** 公理 *)
Axiom a_2 : forall a, a .+ O = a.                (* 公理(2) *)
Axiom a_3 : forall a b, a .+ (s b) = s (a .+ b). (* 公理(3) *)


(**
   「S入れ」は、推論規則とされているが、補題として証明しておく。
   *)
Lemma s_in : forall r t, r = t -> (s r) = (s t).
Proof.
  intros.
  induction r.
  rewrite H.
  reflexivity.
  rewrite H.
  reflexivity.
Qed.


(**
   [GEB白1985] p.232で証明された定理を証明する。
   *)
Theorem t232 : forall a, (O .+ a) = a.
Proof.
  intro a.                              (* 特殊化 *)
  induction a as [|b IH].               (* 機能規則 *)
  Check (a_2 O).                        (* 「ピラミッドの最初の式」 *)
  apply (a_2 O).                        (* 帰納の二番目の前提 *)
  Check (a_3 O b).                      (* 式(7) *)
  rewrite (a_3 O b).                    (* 推移性 *)
  apply s_in.                           (* S入れ *)
  apply IH.                             (* 帰納の一番目の前提 *)
Qed.


(**
   補題、式(18)
   *)
Lemma l18 : forall c,
  (forall d, d .+ s c = s d .+ c) ->
  (forall d, d .+ s (s c) = s d .+ s c).
Proof.
  intros c H d.                             (* 特殊化 *)
  Check (a_3 d (s c)).                      (* 式(3) *)
  Check (a_3 (s d) c).                      (* 式(5) *)
  rewrite (a_3 (s d) c).                    (* 推移性、式(6) *)
  rewrite (a_3 d (s c)).                    (* 推移性、式(3) *)
  apply s_in.                               (* S入れ *)
  apply H.                                  (* 前提 *)
Qed.
    
(**
   補題、式(28)
   Sは加法において、前や後ろに移動できる。
   *)
Lemma l28 : forall c d, d .+ s c = s d .+ c.
Proof.
  induction c as [|c IH].                   (* 帰納規則 *)
  intros d.                                 (* 特殊化 *)
  Check (a_3 d O).                          (* 式(19) *)
  Check (a_2 (s d)).                        (* 式(26) *)
  rewrite (a_3 d O).                        (* 推移性、式(19) *)
  rewrite (a_2 (s d)).                      (* 推移性、式(26) *)
  apply s_in.                               (* S入れ *)
  apply a_2.                                (* 帰納の前提 *)
  Check (l18 c).                            (* *** *)
  apply (l18 c).                            (* *** *)
  apply IH.                                 (* 帰納の前提 *)
Qed.


(**
   補題、式(49)
   もしdが任意のcと交換可能なら、同じことがs dについてもいえる。
   *)
Lemma l49 : forall d,
  (forall c, c .+ d = d .+ c) ->
  (forall c, c .+ s d = s d .+ c).
Proof.
  intros d H.                             (* 特殊化 *)
  intros c.                               (* 特殊化 *)
  Check (a_3 c d).                        (* 式(30) *)
  Check (a_3 d c).                        (* 式(33) *)
  Check (l28 c d).                        (* 式(35) *)
  rewrite <- (l28 c d).                   (* 推移性、式(35) *)
  rewrite (a_3 d c).                      (* 推移性、式(33) *)
  rewrite (a_3 c d).                      (* 推移性、式(30) *)
  apply s_in.                             (* S入れ。 *)
  apply H.                                (* 前提 *)
Qed.


(**
   定理、[GEB白1985] p.234
   *)
Theorem geb_tnt_1 : forall d c, c .+ d = d .+ c.
Proof.
  intros d.                                 (* 特殊化 *)
  induction d as [|d H].                    (* 帰納規則 *)
  intros c.                                 (* 特殊化 *)
  Check (t232 c).                           (* 式(52) *)
  rewrite (t232 c).                         (* 推移性、式(52) *)
  apply a_2.                                (* 帰納の前提 *)
  apply l49.                                (* *** *)
  apply H.                                  (* 帰納の前提 *)
Qed.


(* END *)