From mathcomp Require Import all_ssreflect.
Require Import Omega.

(*
(* https://github.com/affeldt-aist/seplog/blob/master/lib/ssrnat_ext.v *)
Require Import ssrnat_ext.                  (* ssromega *)
*)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
(* Set Printing All. *)

Ltac ssromega :=
  (repeat ssrnat2coqnat_hypo ;
   ssrnat2coqnat_goal ;
   omega)
with ssrnat2coqnat_hypo :=
  match goal with
    | H : context [?L < ?R] |- _ => move/ltP: H => H
    | H : context [?L <= ?R] |- _ => move/leP: H => H
    | H : context [?L < ?M < ?R] |- _ => let H1 := fresh in case/andP: H => H H1
    | H : context [?L <= ?M < ?R] |- _ => let H1 := fresh in case/andP: H => H H1
    | H : context [?L <= ?M <= ?R] |- _ => let H1 := fresh in case/andP: H => H H1
    | H : context [addn ?L ?R] |- _ => rewrite <- plusE in H
    | H : context [muln ?L ?R] |- _ => rewrite <- multE in H
    | H : context [subn ?L ?R] |- _ => rewrite <- minusE in H
    | H : ?x == _ |- _ => match type of x with nat => move/eqP in H end; idtac x
    | H : _ == ?x |- _ => match type of x with nat => move/eqP in H end; idtac x
    | H : _ != ?x |- _ => match type of x with nat => move/eqP in H end
  end
with ssrnat2coqnat_goal :=
  rewrite -?plusE -?minusE -?multE;
  match goal with
    | |- is_true (_ < _)%nat => apply/ltP
    | |- is_true (_ <= _)%nat => apply/leP
    | |- is_true (_ && _) => apply/andP; split; ssromega
    | |- is_true (?x != _) => match type of x with nat => apply/eqP end
    | |- is_true (_ != ?x) => match type of x with nat => apply/eqP end
    | |- is_true (?x == _) => match type of x with nat => apply/eqP end
    | |- is_true (_ == ?x) => match type of x with nat => apply/eqP end
    | |- _ /\ _ => split; ssromega
    | |- _ \/ _ => (left; ssromega) || (right; ssromega)
    | |- _ => idtac
  end.

Goal forall x y : nat, x + 4 - 2 > y + 4 -> (x + 2) + 2 >= y + 6.
Proof.
  move=> x y H.
    by ssromega.
Qed.

(* FRAP の linear_arithmetic *)
(* min と max を扱う。 *)

(* どちらも、m < n での場合分けで良い。 *)
Print maxn.            (* = fun m n : nat => if m < n then n else m *)
Print minn.            (* = fun m n : nat => if m < n then m else n *)

Ltac linear_arithmetic' :=
  intros;
  repeat match goal with
         | [ |- context[maxn ?a ?b] ] =>
           rewrite {1}/maxn; case: (leqP b a); intros

         | [ H : context[maxn ?a ?b] |- _ ] =>
           let H' := fresh in
           rewrite {1}/maxn in H; case: (leqP b a) => H'; try rewrite H' in H

         | [ |- context[minn ?a ?b] ] =>
           rewrite {1}/minn; case: (leqP b a); intros

         | [ H : context[minn ?a ?b] |- _ ] =>
           let H' := fresh in
           rewrite {1}/minn in H; case: (leqP b a) => H';
           try (rewrite leqNgt in H'; move/Bool.negb_true_iff in H'; rewrite H' in H)

         | _ => idtac
         end.
(* case H' : (a < b) の H' が展開できないため、それを使うのを避ける。 *)
(* destruct (a < b) eqn:H' としてもよい。 *)
(*
           let H' := fresh in
           rewrite {1}/maxn; destruct (a < b) eqn: H'; intros
*)

Ltac linear_arithmetic :=
  linear_arithmetic';
  try ssromega;
  rewrite //=.

(* sample *)

Goal forall n m, maxn n m = n <-> m <= n.
Proof.
  split.
  - move=> H.
    rewrite {1}/maxn in H.
    case: (leqP m n) => H'.
    + done.
    + rewrite H' in H.
      by ssromega.
  - move=> H.
    rewrite {1}/maxn.
    case: (leqP m n) => H'.
    + done.
    + by ssromega.

  Restart.
  
  split.
  - by linear_arithmetic.
  - by linear_arithmetic.

  Restart.
  by split; linear_arithmetic.
Qed.

(* 必要な補題を証明する。 leq_gtF はあるので、そっちを使う。 *)
(*
Lemma leq_ltF m n : m <= n <-> (n < m) = false.
Proof.
  rewrite leqNgt.
  split.
  - by move/Bool.negb_true_iff.
  - by move=> H; apply/Bool.negb_true_iff.
Qed.
*)

Goal forall n m, minn n m = n <-> n <= m.
Proof.
  split.
  - move=> H.
    rewrite {1}/minn in H.
    case: (leqP m n) => H'.
    + move/leq_gtF in H'.
      rewrite H' in H.
      by ssromega.
    + by ssromega.

  - move=> H.
    rewrite {1}/minn.
    case: (leqP m n) => H'.
    + by ssromega.
    + done.
    
  Restart.
  split.
  - by linear_arithmetic.
  - by linear_arithmetic.
Qed.

Goal forall m1 n1 m2 n2, m1 <= m2 -> n1 <= n2 -> maxn m1 n1 <= m2 + n2.
Proof.
  move=> m1 n1 m2 n2.
  rewrite /maxn.
  Check leqP n1 m1.
  case: (leqP n1 m1) => H1 H2 H'.
  - by ssromega.
  - by ssromega.

  Restart.
  linear_arithmetic'.
  - by ssromega.
  - by ssromega.

  Restart.
    by linear_arithmetic.
Qed.

(* ####################################################### *)
(* ####################################################### *)
(* SF のサンプルコード *)
(* ####################################################### *)
(* ####################################################### *)

(** * 決定性のある手続き  *)
(* * Decision Procedures *)

(* ####################################################### *)
(** ** Omega *)

(** 例を示します: [x]と[y]を2つの自然数(負にはならない)とする。
    [y]は4以下と仮定し、[x+x+1]は[y]以下と仮定し、
    そして[x]はゼロではないと仮定する。
    すると、[x]は1でなければならない。*)

Lemma omega_demo_1 : forall (x y : nat),
  (y <= 4) -> (x + x + 1 <= y) -> (x <> 0) -> (x = 1).
Proof.
  move=> x y H1 H2 H3.
    by ssromega.
Qed.

(** 別の例: もし[z]が[x]と[y]の間で、[x]と[y]の差が高々[4]である場合、
    [x]と[z]の間は高々2である。*)

Lemma omega_demo_2 : forall (x y z : nat),
  (x + y = z + z) -> (x - y <= 4) -> (x - z <= 2).
Proof.
  move=> x y z H1 H2.
    by ssromega.
Qed.

(** コンテキストの数学的事実が矛盾している場合、[omega]を使って[False]
    を証明することができます。次の例では、[x]と[y]の制約をすべて同時に
    満たすことはできません。*)

Lemma omega_demo_3 : forall (x y : nat),
  (x + 5 <= y) -> (y - x < 3) -> False.
Proof.
  move=> x y H1 H2.
    by ssromega.
Qed.

(** 注意: [omega]が矛盾によってゴールを証明できるのは、
    ゴールの結論部が[False]に簡約されるときだけです。
    [False]から([ex_falso_quodlibet]によって)任意の命題[P]が導出されますが、
    タクティック[omega]は、ゴールの結論部が任意の命題[P]であるときは常に失敗します。*)
(* 実際には、成功する。 *)

Lemma omega_demo_4 : forall (x y : nat) (P : Prop),
  (x + 5 <= y) -> (y - x < 3) -> P.
Proof.
  move=> x y P H1 H2.
  (* Calling [omega] at this point fails with the message:
    "Omega: Can't solve a goal with proposition variables" *)
  (* So, one needs to replace the goal by [False] first. *)
  
    by ssromega.                            (* 成功する。 *)
Qed.


(* ####################################################### *)
(* ** Ring *)
(** ** Ring(環) *)

(** [omega]と比較して、タクティック[ring]は積算を対象としていますが、
    不等式についての推論は放棄しています。 *)

(* ring の使用例は csm_2_4_natural_number.v 参照のこと。 *)

(* ####################################################### *)
(* ** Congruence *)
(** ** Congruence(合同) *)

(** タクティック [congruence] は、証明コンテキストの等式を使って、
    ゴールに至るための書き換えを自動実行することができます。
    タクティック [subst] が扱える等式は変数 [x] と式 [e] について [x = e] 
    という形のものだけですが、
    [congruence] は [subst] より若干強力です。 *)

Lemma congruence_demo_1 :
   forall (f : nat->nat->nat) (g h : nat->nat) (x y z : nat),
   f (g x) (g y) = z ->
   2 = g x ->
   g y = h z ->
   f 2 (h z) = z.
Proof.
  congruence.
  Undo 1.

  move=> f g h x y z H1 H2 H3.
  subst.
  congr (f _ _).
  - done.
  - done.
Qed.

(** さらに[congruence]は、例えば [forall a, g a = h a] 
    のように全称限量された等式を扱えます。*)

Lemma congruence_demo_2 :
  forall (f : nat->nat->nat) (g h : nat->nat) (x y z : nat),
    (forall a, g a = h a) ->
    f (g x) (g y) = z ->
    g x = 2 ->
    f 2 (h y) = z.
Proof.
  congruence.
  Undo 1.

  move=> f g h x y z H1 H2 H3.
  subst.
  congr (f _ _).
  - done.
  - done.
Qed.

(** 次は[congruence]がとても有効な例です。*)

Lemma congruence_demo_4 : forall (f g : nat->nat),
  (forall a, f a = g a) ->
  f (g (g 2)) = g (f (f 2)).
Proof.
  congruence.
  Undo 1.

  move=> f g H.
  rewrite !H.
  done.
Qed.

(** タクティック[congruence]は、
    証明コンテキストで等しくない関係にある両辺についての等式をゴールが前提とするとき、
    矛盾を証明できます。*)

Lemma congruence_demo_3 :
   forall (f g h : nat->nat) (x : nat),
   (forall a, f a = h a) ->
   g x = f x ->
   g x <> h x ->
   False.
Proof.
  congruence.
  Undo 1.
  
  move=> f g h x H1 H2 H3.
  rewrite H1 in H2.
  done.
Qed.

(** [congruence]の強みの1つはとても速いタクティックだということです。
    このため、役立つかもしれないときはいつでも、試すことをためらう必要はありません。*)

(* END *)
