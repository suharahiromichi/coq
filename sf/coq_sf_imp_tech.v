(* ソフトウエアの基礎 Benjamin C. Pierceさん他、梅村さん他訳
   単純な命令型プログラミング言語 Imp を扱う技法のまとめ。
   2013_02_03
   @suharahiromichi
   *)

Require Export Imp_J.

Definition aequiv (a1 a2 : aexp) : Prop :=
  forall (st:state),
    aeval st a1 = aeval st a2.

Definition bequiv (b1 b2 : bexp) : Prop :=
  forall (st:state),
    beval st b1 = beval st b2.

Definition cequiv (c1 c2 : com) : Prop :=
  forall (st st':state),
    (c1 / st || st') <-> (c2 / st || st').

(* (1)
   前提のImp文を分解する。
   [inversion H; subst; clear H.]
   *)
(* (2)
   ゴールのImp文を分解する。
   [apply E_Seq with st'.]
   E_Seqの場合はwithで（以下のst'を）指定する必要がある。E_WhileLoopも同じ。
   c1 / st || st' -> c2 / st' || st'' -> (c1; c2) / st || st''
   他の場合は、指定はいらない。
   E_Skip
   E_Ass
   E_Seq
   E_IfTrue
   E_IfFalse
   E_WhileEnd
   E_WhileLoop
   *)

Theorem seq_assoc : forall c1 c2 c3,
  cequiv ((c1;c2);c3) (c1;(c2;c3)).
Proof.
  intros c1 c2 c3.
  split; intros H.
  (* -> *)
  inversion H; subst; clear H.
  inversion H2; subst; clear H2.
  apply (E_Seq c1 (c2;c3) st st'1).
  apply H1.
  apply (E_Seq c2 c3 st'1 st'0 st').
  apply H6.
  apply H5.
  (* <- *)
  inversion H; subst; clear H.
  inversion H5; subst; clear H5.
  apply E_Seq with st'1.                    (* 省略形 *)
  apply E_Seq with st'0.                    (* 省略形 *)
  apply H2.
  apply H1.
  apply H6.
Qed.

(* (3)
   場合わけのもとの式を覚えておく。
   [remember e as e'. destruct e'.]
   destruct (beq_id k1 k2) とすると、
   (beq_id k1 k2) が trueとfalseに置き換えられて前提から消えてしまう。
   remember (beq_id k1 k2) as b. destruct b. とすると、
   前提に、true = beq_id k1 k2 と false = beq_id k1 k2 が残る。
   *)
Theorem update_same : forall x1 k1 k2 (f : state),
  f k1 = x1 ->
  (update f k1 x1) k2 = f k2.
Proof.
  intros x1 k1 k2 f H.
  unfold update.
  subst.
  remember (beq_id k1 k2) as b.
  destruct b.
  (* f k1 = f k2 *)
  apply beq_id_eq in Heqb.
  subst.
  reflexivity.
  
  (* f k2 = f k2 *)
  reflexivity.
Qed.

(* (4)
   ゴールの状態を書き換えて、後でその書き換えの正しさを証明する。
   [replace (update st X (st X)) with st.]
   ゴールの (update st X (st X)) を st を置き換えて、
   st = update st X (st X) というゴールを追加する。
   これ（X ::= X）をしても、状態は実質同じなことは、次の「公理」で決める。
 *)
(* (5)
   ゴールの st = st' を st x = st' x に書き換える。
   [apply functional_extensionality. intro.]
   関数としての状態、つまりupdateのネスト具合は違っていても、
   任意のxに対して同じ結果なら、同じ状態であるとみなす。
   st x = st' x は、以降別途証明する。
*)

Axiom functional_extensionality : forall {X Y: Type} {f g : X -> Y},
    (forall (x: X), f x = g x) ->  f = g.

Theorem identity_assignment : forall (X:id),
  cequiv
    (X ::= AId X)
    SKIP.
Proof.
   intros. split; intro H.
       (* (X ::= AId X) -> SKIP *)
       inversion H; subst. simpl.
       replace (update st X (st X)) with st.
       apply E_Skip.
       apply functional_extensionality. intro.
       rewrite update_same; reflexivity.
       (* SKIP -> (X ::= AId X) *)
       inversion H; subst.
       assert (st' = (update st' X (st' X))).
          apply functional_extensionality. intro.
          rewrite update_same; reflexivity.
       rewrite H0 at 2.
       apply E_Ass. reflexivity.
Qed.

(* (6)
   前提の名前を変更する。
   [rename st' into st''.]
   前提の名前を変更する。必須ではないが、
   rememberを使う前に前提のラベルを整理するときに使うようだ。
 *)

(* subtract_slowly （ゆっくり引き算）の仕様を証明する。 *)

Definition subtract_slowly_invariant (z:nat) (x:nat) (st:state) :=
  minus (st Z) (st X) = z - x.

(* st Z <> 0 の条件は要らないようだ。 *)
Theorem subtract_slowly_body_preserves_invariant' : forall st st' z x,
  subtract_slowly_invariant z x st ->
  st X <> 0 -> st Z <> 0 ->
  subtract_slowly_body / st || st' ->
    subtract_slowly_invariant z x st'.
Proof.
  unfold subtract_slowly_invariant, subtract_slowly_body.
  intros st st' z x Hm HXn0 HZn0 He.        (* Hm ループ不変式 *)
  (* st' Z - st' X = z - x *)
  inversion He; subst; clear He.
  inversion H1; subst; clear H1.
  inversion H4; subst; clear H4.
  unfold update. simpl.
  (* (st Z - 1) - (st X - 1) = z - x *)
  omega.
Qed.

Theorem subtract_slowly_body_preserves_invariant : forall st st' z x,
  subtract_slowly_invariant z x st ->
  st X <> 0 ->
  subtract_slowly_body / st || st' ->
    subtract_slowly_invariant z x st'.
Proof.
  unfold subtract_slowly_invariant, subtract_slowly_body.
  intros st st' z x Hm HXn0 He.             (* Hm ループ不変式 *)
  (* st' Z - st' X = z - x *)
  inversion He; subst; clear He.
  inversion H1; subst; clear H1.
  inversion H4; subst; clear H4.
  unfold update. simpl.
  (* (st Z - 1) - (st X - 1) = z - x *)
  omega.
Qed.

Definition subtract_slowly_loop : com :=
  subtract_slowly.

Theorem subtract_slowly_loop_preserves_invariant : forall st st' z x,
     subtract_slowly_invariant z x st ->
     subtract_slowly_loop / st || st' ->
     subtract_slowly_invariant z x st'.
Proof.
  intros st st' z x H Hce.
  remember subtract_slowly_loop as c.
  induction Hce; inversion Heqc; subst; clear Heqc.
  (* subtract_slowly_invariant z x st *)
  assumption.

  (* subtract_slowly_invariant z x st'' *)
  apply IHHce2.

  (* subtract_slowly_invariant z x st' *)
  apply subtract_slowly_body_preserves_invariant with st;
    try assumption.

  (* st X <> 0 *)
  intros Contra. simpl in H0; subst.
  rewrite Contra in H0. inversion H0.
  
  (* (WHILE BNot (BEq (AId X) (ANum 0)) DO subtract_slowly_body END) =
   subtract_slowly_loop *)
  unfold subtract_slowly_loop.
  unfold subtract_slowly.
  reflexivity.
Qed.

Definition subtract_slowly_com : com :=
  subtract_slowly.

Theorem subtract_slowly_correct : forall st st' z x,
  st Z = z -> st X = x ->
  subtract_slowly_com / st || st' ->
    st' Z = z - x.
Proof.
  intros st st' z x HZ HX Hce.
  inversion Hce; subst; clear Hce.
  inversion H3; subst; clear H3.
  SearchAbout negb.
  apply negb_false_iff in H0.
  SearchAbout beq_nat.
  apply beq_nat_true in H0.
  rewrite H0.
  omega.

  inversion H1; subst; clear H1.
  inversion H2; subst; clear H2.
  inversion H3; subst; clear H3.
  inversion H7; subst; clear H7.
  apply negb_true_iff in H0.                (* これ大事！ *)
  apply beq_nat_false in H0.

  rename st' into st''. simpl in H5.
  (* The invariant is true before the loop runs... *)
  (* ループの実行前では、不変式は成立する。 *)
  remember
  (update (update st Z (st Z - 1)) X (st X - 1))
  as st'.
  assert (subtract_slowly_invariant (st Z) (st X) st').
  subst. unfold subtract_slowly_invariant, update.
  simpl.
  omega.

  (* ...so when the loop is done running, the invariant is maintained *)
  (* …なので、ループの実行中は、不変式は更新される。 *)
  assert (subtract_slowly_invariant (st Z) (st X) st'').
  apply subtract_slowly_loop_preserves_invariant with st'; subst;
    assumption.

  unfold subtract_slowly_invariant in H.
  unfold subtract_slowly_invariant in H1.
  (* Finally, if the loop terminated, then X is 0; so Z must be z - x *)
  (* 最後に、もしループが終了するなら、Xは0で、Zには(z - x)の答え。 *)
  apply guard_false_after_loop in H5. simpl in H5.
  apply negb_false_iff in H5.               (* これ大事！ *)
  apply beq_nat_true in H5.
  omega.
Qed.

(* END *)
