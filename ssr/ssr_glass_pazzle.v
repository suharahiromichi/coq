(**
グラス置き換えバズル
 *)

(**
文献[1]の「グラス置き換えパズル」の合流性の証明を文献[2]に沿っておこなう。
文献[1]では、Kunth-Bendixの方法で書き換え規則を追加することを説明しているが、
ここでは、文献[2]の並列簡約をもちいる方法を使う。
文献[2]同様に、Coq/SSReflectを使用する。

文献[1] 外山、証明は計算できる。数学セミナー2014_11
文献[2] 坂口、Coqによる定理証明 コンビネータ論理 C83版
*)

Require Import Coq.Arith.Arith
        Coq.Relations.Relations
        Coq.Relations.Relation_Operators    (* rt1n_trans の別名問題 *)
        ssreflect.

(**
GL項：

Sake, Whisky, Beerのグラス、その組み合わせを示す「@」および変数を GL項と呼ぶ。
 *)
Reserved Notation "x '@' y" (at level 50, left associativity).
Inductive glterm : Set :=
| glvar of nat                              (* 変数 *)
| glapp of glterm & glterm                  (* x @ y *)
| gls                                       (* Sake *)
| glw                                       (* Whisky *)
| glb.                                      (* Beer *)
Notation "x @ y" := (glapp x y).
Check gls @ glw @ glb.                      (* glterm *)

(**
二項関係：

GL項の間の以下の二項関係を考える。
*)
Check relation.                             (* R *)
Check reflexive.                            (* R x x *)
Check transitive.                           (* R x y -> R y z -> R x z *)
Check symmetric.                            (* R x y -> R y x *)

(**
反射推移閉包：
 *)
Notation inglusion R R' := (forall t1 t2, R t1 t2 -> R' t1 t2).
Notation same_relation R R' := (forall t1 t2, R t1 t2 <-> R' t1 t2).
Notation "R *" := (clos_refl_trans_1n _ R) (at level 25, left associativity).
Print clos_refl_trans_1n.

(**
注意：

Relations/Operators_Properties.v の中で定義されている、
Notation rt1n_trans := clos_rt1n_rt (only parsing)
によって、rt1n_trans が、clos_rt1n_rt の別名になっている。
Require Import Coq.Relations.Relation_Operators を外して、
次のCheckを実行すると納得できる。
*)
Check clos_rt1n_rt.
Check rt1n_trans.             (* これが、clos_rt1n_rt の別名になっている *)
Check Relation_Operators.rt1n_trans.
(* そのため、Relations.Relation_Operators で定義されている、
clos_refl_trans_1n のコンストラクタが使えなかった。

対策として、ここでは、Coq.Relations.Relations のあとに再び、
Coq.Relations.Relation_Operators をimportする。
 *)

(* (R * ) x y -> (R * ) y z -> (R * ) x z *)
Lemma rt1n_trans' :
  forall (A : Type) (R : relation A), transitive A (R * ).
Proof.
  move=> A R t1 t2 t3.
  rewrite -!clos_rt_rt1n_iff.
  by apply rt_trans.
Qed.

(* R ∈ R' -> (R * ) ∈ (R * ) *)
Lemma clos_rt_map :
  forall (A : Type) (R R' : relation A),
    inglusion R R' -> inglusion (R * ) (R' * ).
Proof.
  move=> A R R' H t1 t2.
  (* ((R * ) t1 t2) で場合分けする。  *)
  elim.
  (* ((R' * ) x x) のとき、 *)
  apply: rt1n_refl.
  (* R x y -> (R * ) y z -> (R' * ) y z -> (R' * ) x z のとき、 *)
  move=> x y z H1 H2 H3.
  apply: (rt1n_trans A R' x y z).           (* 注意参照 *)
    by auto.
    by auto.
Qed.

(* ((R * ) * ) = (R * ) *)
Lemma rt1n_nest_elim :
  forall (A : Type) (R R' : relation A),
    same_relation (R * * ) (R * ).
Proof.
  move=> A R t1 t2; split.
  (* (R * * ) t2 t0 -> (R * ) t2 t0 の場合、 *)
  - elim=> [t3 | t3 t4 t5 H H0 H1].
    apply rt1n_refl.
      by apply (rt1n_trans' A R _ t4 _).
  (* (R * ) t2 t0 -> (R * * ) t2 t0 の場合、 *)
  - by apply clos_rt1n_step.
Qed.

Notation confluent R :=                     (* 合流性 *)
  (forall t1 t2 t3, R t1 t2 -> R t1 t3 ->
                    exists t4, R t2 t4 /\ R t3 t4).

Lemma rt1n_confluent_sub :
  forall (A : Type) (R : relation A),
         confluent R ->
         (forall t1 t2 t3,
            R t1 t2 -> (R * ) t1 t3 ->
            exists t4, (R * ) t2 t4 /\ (R * ) t3 t4).
Proof.
  move=> A R H t1 t2 t3 H0 H1. move: H1 t2 H0.
  (* H1にはt2がないので入れ替えられる。 *)
  (* (R * ) t1 t3 で帰納する。 *)
  elim=> [t4 t2 H0 | t4 t5 t6 H0 H1 IH t2 H2].
  (* t1n_stepの場合、 R x y -> (R * ) x y *)
    by exists t2; do !constructor; apply clos_rt1n_step.
              
  (* t1n_transの場合、R x y -> (R * ) y z -> (R * ) x z *)
  Check H t4 t5 t2 H0 H2.
  elim (H t4 t5 t2 H0 H2) => t7 [H3 H4].
  Check (IH t7 H3).
  elim (IH t7 H3) => t8 [H5 H6].
  exists t8. split.
  (* /\の左、(R * ) t2 t7 *)
  Check (rt1n_trans A R t2 t7 t8).
  by apply (rt1n_trans A R t2 t7 t8).
  (* /\の右、(R * ) t6 t7 *)
  by [].
Qed.

Lemma rt1n_confluent :
  forall (A : Type) (R : relation A), confluent R -> confluent (R * ).
Proof.
  move=> A R H.
  have := (rt1n_confluent_sub A R H).
  clear H => H t1 t2 t3 H0; move: H0 t3.
  (* (R * ) t1 t2 で帰納する。 *)
  elim=> [t4 t3 H1 | t4 t5 t6 H0 H1 IH t3 H2].
  (* t1n_stepの場合、 R x y -> (R * ) x y *)
  by exists t3; do !constructor.
  
  (* t1n_transの場合、R x y -> (R * ) y z -> (R * ) x z *)
  Check (H t4 t5 t3 H0 H2).
  elim (H t4 t5 t3 H0 H2) => t7 [H3 H4].
  elim (IH t7 H3) => t8 [H5 H6].
  exists t8. split.
    (* /\の左、(R * ) t6 t8 *)
  by [].
    (* /\の右、(R * ) t3 t8 *)
  Check (rt1n_trans' A R t3 t7 t8).
  by apply (rt1n_trans' A R t3 t7 t8).
Qed.

(*
証明の概要：

1w ∈ R' ∈ w であり、R' が合流性をもつならば、
rt1n_confluent によって、R' が合流性をもてば、R'* も合流性をもつ。
glose_rt_map によって、1w ∈ R' -> w ∈ R'*、ただし 1w* = w。
ゆえに、wも合流性をもつ。
 *)

(*
R ∈ R' ∈ R* で、R'が合流性をもつならば、R*も合流性をもつ。
その証明：
(1) rt1n_confluent によって、R' が合流性をもてば、R'* も合流性をもつ。

(2) R ∈ R' ∈ R* より、
close_rt_map によって、R ∈ R' -> R* ∈ R'*。
close_rt_map によって、R'∈ R* -> R'* ∈ R** = R*
ふたつを合わせると、
R ∈ R' -> R' ∈ R* -> R* ∈ R'* -> R'* ∈ R*
R ∈ R' ∈ R* -> R* = R'*

(1)(2)から、R*も合流性をもつ。
 *)
Lemma rt1n_confluent' :
  forall  (A : Type) (R R' : relation A),
    inclusion _ R R' -> inclusion _ R' (R * ) ->
    confluent R' -> confluent (R * ).
Proof.
  move=> A R R' H H0 H1 t1 t2 t3 H2 H3.
  elim (rt1n_confluent _ _ H1 _ _ _
                       (clos_rt_map _ _ _ H _ _ H2)
                       (clos_rt_map _ _ _ H _ _ H3))
       => t4 [H4 H5].
  exists t4.
  split;
    by rewrite -rt1n_nest_elim; [apply (clos_rt_map _ R') |].
Qed.

(* 弱簡約 weak red *)
Reserved Notation "x '--1w->' y" (at level 70, no associativity).
Reserved Notation "x '--w->' y" (at level 70, no associativity).

Inductive gl_weakred : relation glterm :=
| weakred_left : forall (t1 t2 t3 : glterm),
                   gl_weakred t1 t2 -> gl_weakred (t1 @ t3) (t2 @ t3)
| weakred_right : forall (t1 t2 t3 : glterm),
                    gl_weakred t1 t2 -> gl_weakred (t3 @ t1) (t3 @ t2)
| weakred_sw : gl_weakred (gls @ glw) glw
| weakred_wb : gl_weakred (glw @ glb) gls.
                           
Infix "--1w->" := gl_weakred.
Infix "--w->" := (gl_weakred * ).

Lemma weakred_rtc_left : forall t1 t2 t3,
                           (t1 --w-> t2) -> (t1 @ t3 --w-> t2 @ t3).
Proof.
  move=> t1 t2 t3; elim; econstructor.
  apply weakred_left, H.
  auto.
Qed.

Lemma weakred_rtc_right : forall t1 t2 t3,
                            (t1 --w-> t2) -> (t3 @ t1 --w-> t3 @ t2).
Proof.
  move=> t1 t2 t3; elim; econstructor.
  apply weakred_right, H.
  auto.
Qed.

Hint Resolve weakred_rtc_left weakred_rtc_right.

Lemma weakred_rtc_app : forall t1 t1' t2 t2',
                          (t1 --w-> t1') -> (t2 --w-> t2') ->
                          (t1 @ t2 --w-> t1' @ t2').
Proof.
  move=> t1 t1' t2 t2' H H0; apply rt1n_trans' with (t1 @ t2'); auto.
Qed.
Hint Resolve weakred_rtc_app.

(* 並列簡約 parallel red *)
Reserved Notation "x '--p->' y" (at level 70, no associativity).

Inductive gl_parred : relation glterm :=
| parred_app : forall (t1 t1' t2 t2' : glterm),
                 gl_parred t1 t1' -> gl_parred t2 t2' ->
                 gl_parred (t1 @ t2) (t1' @ t2')
| parred_sw : gl_parred (gls @ glw) glw
| parred_wb : gl_parred (glw @ glb) gls
| parred_var : forall (n : nat), gl_parred (glvar n) (glvar n)
| parred_atoms : gl_parred gls gls
| parred_atomw : gl_parred glw glw
| parred_atomb : gl_parred glb glb.

Infix "--p->" := gl_parred.

(* 並列簡約が、反射関係であることを証明する。 *)
Lemma gl_parred_refl : reflexive _ gl_parred.
Proof.
    by elim; constructor.
(* gl_parredのコンストラクタ *)
Qed.
Hint Resolve gl_parred_refl.

(* 簡約関数 parallel red all *)
(* 項Xの中の簡約できる部分をすべて簡約した項をX*と書く。X*を求める関数は以下である。 *)
Fixpoint gl_parred_all (t : glterm) : glterm :=
  match t with
    | gls @ glw => glw
    | glw @ glb => gls
    | t1 @ t2 => gl_parred_all t1 @ gl_parred_all t2
    | _ => t
  end.

(* 合流性の証明 *)
Lemma gl_parred_all_lemma :
  forall t1 t2, (t1 --p-> t2) -> (t2 --p-> gl_parred_all t1).
Proof.
  intros t1 t2 H; induction H; try by do ?constructor.
  (* 第一のゴール、
     t1' @ t2' ->p gl_parred_all (t1 @ t2) だけが残る。 *)
  - destruct t1; try by constructor.
    + destruct t2; try by constructor.
      * inversion H. subst.
      * inversion H0. subst.
          by constructor.                   (*  parred_sw  *)
    + destruct t2; try by constructor.
      * inversion H. subst.
      * inversion H0. subst.
          by constructor.                   (* parred_wb *)
Qed.

(* --p-> が合流性をもつ。((1) R'が合流性をもつ。) *)
Theorem gl_parred_confluent : confluent gl_parred.
Proof.
  move=> t1. exists (gl_parred_all t1).
  (* (t2 --p-> gl_parred_all t1) /\ (t3 --p-> gl_parred_all t1) *)
  split.
  - apply (gl_parred_all_lemma t1 t2). done.
  - apply (gl_parred_all_lemma t1 t3). done.
Qed.

(* --1w-> ∈ --p-> ((2) R ∈ R') *)
Theorem gl_weakred_in_parred : inclusion _ gl_weakred gl_parred.
Proof.
  move=> t1 t2.
  (* t1 --1w-> t2 で場合分けする。
     ついで、--p->のコンストラクタで証明する。 *)
    by elim; try constructor.
Qed.

(* --p-> ∈ --w-> ((3) R' ∈ R* ) *)
Theorem gl_parred_in_weakred_rtc : inclusion _ gl_parred (gl_weakred * ).
Proof.
  intros t1 t2 H.
  (* t1 --p-> t2 で場合分けする。
     ついで、後半のいくつかをapply rt1n_reflで証明する *)
  induction H; try constructor.
  (* 残りのゴールを個々に証明する。 *)
  (* t1 @ t2 --w-> t1' @ t2' *)
  - by auto.
  (* gls @ glw --w-> glw *)
  - apply clos_rt1n_step. by constructor.
  (* glw @ glb --w-> gls *)
  - apply clos_rt1n_step. by constructor.
Qed.

(* --w-> は合流性をもつ。(R *は合流性をもつ(4)。) *)
(* rt1n_confluent' を使って (2) -> (3) -> (1) -> (4) を証明する。 *)
Theorem gl_weakred_confluent : confluent (gl_weakred * ).
Proof.
    by apply (rt1n_confluent' _
                              gl_weakred               (* R *)
                              gl_parred                (* R' *)
                              gl_weakred_in_parred     (* (2) *)
                              gl_parred_in_weakred_rtc (* (3) *)
                              gl_parred_confluent).    (* (1) *)
Qed.

(* 唯一正規形性の証明 *)

(* tは正規形である。 *)
Definition gl_weaknf (t : glterm) : Prop :=
  ~ (exists t' : glterm, t --1w-> t').        (* 簡約できる項はない。 *)

(* t1はt2の正規形である。 *)
Definition gl_weaknf_of (t1 t2 : glterm) : Prop :=
  t2 --w-> t1 /\ gl_weaknf t1.

Corollary gl_weaknf_uniqueness :
  forall t1 t2 t3, gl_weaknf_of t2 t1 ->
                   gl_weaknf_of t3 t1 ->
                   t2 = t3.
Proof.
  move=> t1 t2 t3.
  (* gl_weaknf_of t2 t1 で場合分けする。 *)
  elim=> H H0.
  (* gl_weaknf_of t3 t1 で場合分けする。 *)
  elim=> H1 H2.
  
  Check (gl_weakred_confluent t1 t2 t3 H H1).
  elim (gl_weakred_confluent t1 t2 t3 H H1) => [t4 [H3 H4]].
  inversion H3.
  inversion H4.
  (* t4 = t4 *)
  auto.
  (* t4 = t3 *)
  apply False_ind. apply H2. exists y. done. (* eauto *)
  (* t2 = t3 *)
  apply False_ind. apply H0. exists y. done. (* eauto *)
Qed.

(* END *)
