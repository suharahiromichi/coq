(** * Hoare_J: ホーア論理 *)
(* * Hoare: Hoare Logic *)

Require Export ImpList_J.                   (* BIsNullを追加した版 *)

(** ** 表明 *)
Definition Assertion := state -> Prop.

(** ** ホーアの三つ組 *)
Definition hoare_triple (P:Assertion) (c:com) (Q:Assertion) : Prop :=
  forall st st',
       c / st || st'  ->
       P st  ->
       Q st'.

Notation "{{ P }}  c" :=          (hoare_triple P c (fun st => True)) (at level 90)
                                  : hoare_spec_scope.
Notation "{{ P }}  c  {{ Q }}" := (hoare_triple P c Q) (at level 90, c at next level)
                                  : hoare_spec_scope.
Open Scope hoare_spec_scope.

Definition assn_sub V a Q : Assertion :=
  fun (st : state) =>
    Q (update st V (aeval st a)).

(* ####################################################### *)
(** *** 代入 *)
Theorem hoare_asgn : forall Q V a,
  {{assn_sub V a Q}} (V ::= a) {{Q}}.
Proof.
  unfold hoare_triple.
  intros Q V a st st' HE HQ.
(*
   補足説明：
   [V::=a] を実行すると、
   V=aを加えるとQの成立する(もとの)状態(st)から、
   (V=aを加えなくても)Qの成立する状態(st')に、移行する。
   
  HQ : assn_sub V a Q st
  HE : (V ::= a) / st || st'
  ============================
   Q st'
*)
  inversion HE. subst.
(*
   補足説明：
   [V::=a] を実行すると、
   stから、
   stにV=aを加えた状態[update st V (aeval st a)]に、移行する。
   (この書き方のほうが解りやすいが、その分、表している意味が少ない、のか）
   
  HQ : assn_sub V a Q st
  HE : (V ::= a) / st || update st V (aeval st a)
  ============================
   Q (update st V (aeval st a))
*)
  unfold assn_sub in HQ. assumption.
Qed.

(* Here's a first formal proof using this rule. *)
(** この規則を使った最初の形式的証明が次のものです。*)

Theorem hoare_asgn_eq : forall Q Q' V a,
     Q' = assn_sub V a Q ->
     {{Q'}} (V ::= a) {{Q}}.
Proof.
  intros Q Q' V a H.
  rewrite H.
(*
   補足説明
   V=aを加えるとQの成立する(もとの)状態(st)では、Q'が成立する。
   (V=aを加えなくても)Qの成立する状態(st')では、Qが成立する。あたりまえ。
   [V::=a] を実行すると、st' から st に移行する。
   
   感覚的にいうと、
   Q' st で、Q st' のとき、stはst'からV=aを取り去ったもの。
   このQ'とQの関係を以下で示す。
   Q' = assn_sub V a Q
   取り去るというより、不問にする、というべきだろうか。
   より重要なのは、取り去られているのはV=aという、Vとaeval(a)の関係であって、
   aeval(a)を実行するための状態は、取り去られていないことである、だろうか。
   
   H : Q' = assn_sub V a Q
   ============================
   {{assn_sub V a Q}} V ::= a {{Q}}
*)
  apply hoare_asgn.
Qed.

(* 事前条件を強め、事後条件を弱める。 *)
Theorem hoare_consequence : forall (P P' Q Q' : Assertion) c,
  {{P'}} c {{Q'}} ->
  (forall st, P st -> P' st) ->
  (forall st, Q' st -> Q st) ->
  {{P}} c {{Q}}.
Proof.
  intros P P' Q Q' c Hht HPP' HQ'Q.
  intros st st' Hc HP.
  apply HQ'Q.  apply (Hht st st'). assumption.
  apply HPP'. assumption.  Qed.

(* 事前条件を強める。 *)
Theorem hoare_consequence_pre : forall (P P' Q : Assertion) c,
  {{P'}} c {{Q}} ->
  (forall st, P st -> P' st) ->
  {{P}} c {{Q}}.
Proof.
  intros P P' Q c Hhoare Himp.
  apply hoare_consequence with (P' := P') (Q' := Q);
    try assumption.
  intros st H. apply H.  Qed.

(* 事後条件を弱める。 *)
Theorem hoare_consequence_post : forall (P Q Q' : Assertion) c,
  {{P}} c {{Q'}} ->
  (forall st, Q' st -> Q st) ->
  {{P}} c {{Q}}.
Proof.
  intros P Q Q' c Hhoare Himp.
  apply hoare_consequence with (P' := P) (Q' := Q');
    try assumption.
  intros st H. apply H.  Qed.

(* ####################################################### *)
(** *** Skip *)
(** [SKIP]は状態を変えないことから、任意の性質 P を保存します:
[[
      --------------------  (hoare_skip)
      {{ P }} SKIP {{ P }}
]]
*)

Theorem hoare_skip : forall P,
     {{P}} SKIP {{P}}.
Proof.
  intros P st st' H HP. inversion H. subst.
  assumption.  Qed.

(* ####################################################### *)
(** *** コマンド合成 *)
(** より興味深いことに、コマンド[c1]が、[P]が成立する任意の状態を[Q]が成立する状態にし、
    [c2]が、[Q]が成立する任意の状態を[R]が成立する状態にするとき、
    [c1]に続いて[c2]を行うことは、[P]が成立する任意の状態を[R]が成立する状態にします:
[[
        {{ P }} c1 {{ Q }}
        {{ Q }} c2 {{ R }}
       ---------------------  (hoare_seq)
       {{ P }} c1;c2 {{ R }}
]]
*)

Theorem hoare_seq : forall P Q R c1 c2,
     {{Q}} c2 {{R}} ->
     {{P}} c1 {{Q}} ->
     {{P}} c1;c2 {{R}}.
Proof.
  intros P Q R c1 c2 H1 H2 st st' H12 Pre.
  inversion H12; subst.
  apply (H1 st'0 st'); try assumption.
  apply (H2 st st'0); try assumption. Qed.

(** 形式的規則[hoare_seq]においては、
    前提部分が「逆順」である([c1]の前に[c2]が来る)ことに注意してください。
    この順は、規則を使用する多くの場面で情報の自然な流れにマッチするのです。*)

(** 非形式的には、この規則を利用した証明を記録する良い方法は、
    [c1]と[c2]の間に中間表明[Q]を記述する"修飾付きプログラム"の様にすることです:
[[
      {{ a = n }}
    X ::= a;
      {{ X = n }}      <---- 修飾 Q
    SKIP
      {{ X = n }}
]]
*)

(* ####################################################### *)
(** *** 条件分岐 *)

(** しかし、実際には、より詳しいことを言うことができます。
   "then"の枝では、ブール式[b]の評価結果が[true]になることがわかっています。
   また"else"の枝では、それが[false]になることがわかっています。
   この情報を補題の前提部分で利用できるようにすることで、
   [c1]と[c2]の振舞いについて(つまり事後条件[Q]が成立する理由について)推論するときに、
   より多くの情報を使うことができるようになります。
[[
              {{P /\  b}} c1 {{Q}}
              {{P /\ ~b}} c2 {{Q}}
      ------------------------------------  (hoare_if)
      {{P}} IFB b THEN c1 ELSE c2 FI {{Q}}
]]
*)

(** この規則を形式的に解釈するために、もう少しやることがあります。

    厳密には、上述の表明において、表明とブール式の連言[P /\ b]は、型チェックを通りません。
    これを修正するために、ブール式[b]を形式的に「持ち上げ」て、表明にしなければなりません。
    このために[bassn b]と書きます。
    これは"ブール式[b]の評価結果が(任意の状態で)[true]になる"という表明です。*)

Definition bassn b : Assertion :=
  fun st => (beval st b = true).

(** [bassn]についての2つの便利な事実です: *)

Lemma bexp_eval_true : forall b st,
  beval st b = true -> (bassn b) st.
Proof.
  intros b st Hbe.
  unfold bassn. assumption.  Qed.

Lemma bexp_eval_false : forall b st,
  beval st b = false -> ~ ((bassn b) st).
Proof.
  intros b st Hbe contra.
  unfold bassn in contra.
  rewrite -> contra in Hbe. inversion Hbe.  Qed.

(** いよいよ条件分岐についてのホーア証明規則を形式化し、正しいことを証明できます。*)

Theorem hoare_if : forall P Q b c1 c2,
  {{fun st => P st /\ bassn b st}} c1 {{Q}} ->
  {{fun st => P st /\ ~(bassn b st)}} c2 {{Q}} ->
  {{P}} (IFB b THEN c1 ELSE c2 FI) {{Q}}.
Proof.
  intros P Q b c1 c2 HTrue HFalse st st' HE HP.
  inversion HE; subst.
  Case "b is true".
    apply (HTrue st st').
      assumption.
      split. assumption.
             apply bexp_eval_true. assumption.
  Case "b is false".
    apply (HFalse st st').
      assumption.
      split. assumption.
             apply bexp_eval_false. assumption. Qed.

(* ####################################################### *)
(** *** ループ *)

(** 最後に、ループについての推論規則が必要です。
    次のループを考えます:
[[
      WHILE b DO c END
]]
    そして、次の三つ組が正しくなる事前条件[P]と事後条件[Q]を探します:
[[
      {{P}} WHILE b DO c END {{Q}}
]]
    まず、[b]が最初から偽であるときを考えましょう。
    このときループの本体はまったく実行されません。
    この場合は、ループは[SKIP]と同様の振舞いをしますので、
    次のように書いても良いかもしれません。
[[
      {{P}} WHILE b DO c END {{P}}.
]]
    しかし、条件分岐について議論したのと同様に、最後でわかっていることはもう少し多いのです。
    最終状態では[P]であるだけではなく[b]が偽になっているのです。
    そこで、事後条件にちょっと付け足すことができます:
[[
      {{P}} WHILE b DO c END {{P /\ ~b}}
]]
    それでは、ループの本体が実行されるときはどうなるでしょう？
    ループを最後に抜けるときには[P]が成立することを確実にするために、
    コマンド[c]の終了時点で常に[P]が成立することを確認する必要があるのは確かでしょう。
    さらに、[P]が[c]の最初の実行の前に成立しており、[c]を実行するたびに、
    終了時点で[P]の成立が再度確立されることから、
    [P]が[c]の実行前に常に成立していると仮定することができます。
    このことから次の規則が得られます:
[[
                   {{P}} c {{P}}
        -----------------------------------
        {{P}} WHILE b DO c END {{P /\ ~b}}
]]
    命題[P]は不変条件(_invariant_)と呼ばれます。ループ不変式

    これで求める規則にかなり近付いたのですが、もうちょっとだけ改良できます。
    ループ本体の開始時点で、[P]が成立しているだけでなく、
    ガード[b]が現在の状態で真であるということも言えます。
    このことは、[c]についての推論の際にいくらかの情報を与えてくれます。
    結局、規則の最終バージョンはこうなります:
[[
               {{P /\ b}} c {{P}}
        -----------------------------------  [hoare_while]
        {{P}} WHILE b DO c END {{P /\ ~b}}
]]
*)

Lemma hoare_while : forall P b c,
  {{fun st => P st /\ bassn b st}} c {{P}} ->
  {{P}} WHILE b DO c END {{fun st => P st /\ ~ (bassn b st)}}.
Proof.
  intros P b c Hhoare st st' He HP.
  remember (WHILE b DO c END) as wcom.
  induction He;                             (* wcom / st || st' に対する帰納法。 *)
    inversion Heqwcom; subst.

  (* "E_WhileEnd". *)
  (* 
     HP : P st
     H : beval st b = false
     ============================
     P st /\ ~ bassn b st
 *)
  split. 
  apply HP.
  apply bexp_eval_false. apply H.

  (* "E_WhileLoop". *)
  (* 
     HP : P st
     He1 : c / st || st'
     IHHe1 : c = (WHILE b DO c END) -> P st -> P st' /\ ~ bassn b st'
     H : beval st b = true
     He2 : (WHILE b DO c END) / st' || st''
     IHHe2 : (WHILE b DO c END) = (WHILE b DO c END) ->
     P st' -> P st'' /\ ~ bassn b st''
     ============================
     P st'' /\ ~ bassn b st''
     *)
  apply IHHe2.  reflexivity.
  apply (Hhoare st st').
  apply He1.
  (* P st /\ bassn b st *)
  split.
  apply HP.
  apply bexp_eval_true. apply H.
Qed.


(* ####################################################### *)
(* ####################################################### *)
(* ####################################################### *)
(** リストの最大値を求めるプログラム *)
Module Maximum.

Definition max a b :=
  if ble_nat a b then b else a.

Definition maximum l := fold_right max 0 l.

Eval compute in maximum [].
Eval compute in maximum [1, 2, 3, 1].

Definition max_program :=
  Y ::= ANum 0;
  (* 説明用に、BIsConstをBNot BIsNullにしてみた。 *)
  WHILE (BNot (BIsNull (AId X))) DO          (* ImpList_J.vo の修正・再コンパイルが要る。 *)
    IFB (BLe (AId Y) (AHead (AId X))) THEN
      Y ::= AHead (AId X)
    ELSE
      SKIP
    FI;
    X ::= ATail (AId X)
  END.

(* ループ不変式 *)
Definition max_prog_inv l : Assertion :=
  fun st =>
    max (asnat (st Y)) (maximum (aslist (st X))) = maximum l.

Definition max_prog_spec := forall l,
  {{ fun st => aslist (st X) = l }}
  max_program
  {{ fun st => asnat (st Y) = maximum l }}.

Lemma eq_comm : forall A : Type, forall a b : A,
  a = b -> b = a.
Proof.
  intros A a b H.
  rewrite <- H. reflexivity.
Qed.

Lemma max0r : forall a,
  max a 0 = a.
Proof.
  intros a.
  unfold max.
  induction a; (simpl; reflexivity).
Qed.

Lemma max0l : forall a,
  max 0 a = a.
Proof.
  intros a.
  unfold max.
  induction a; (simpl; reflexivity).
Qed.

Lemma maxS : forall a b,
  max (S a) (S b) = S (max a b).
Proof.
  intros a b.
  unfold max. simpl.
  destruct (ble_nat a b); reflexivity.
Qed.  

Lemma max_assoc : forall a b c,
  max a (max b c) = max (max a b) c.
Proof.
  intros a b c.
  unfold max.
  remember (ble_nat a b) as ab.
  remember (ble_nat b c) as bc.
  remember (ble_nat a c) as ac.

  destruct ab.
  destruct bc.
  destruct ac.
  (* a ≦ b /\ b ≦ c /\ a ≦ c *)
  rewrite <- Heqac. rewrite <- Heqbc. reflexivity.

  (* a ≦ b /\ b ≦ c /\ a > c *)
  rewrite <- Heqac. rewrite <- Heqbc.
  apply eq_comm in Heqab. apply ble_nat_true in Heqab.
  apply eq_comm in Heqbc. apply ble_nat_true in Heqbc.
  apply eq_comm in Heqac. apply ble_nat_false in Heqac.
  omega.

  destruct ac.
  (* a ≦ b /\ b > c /\ a ≦ c *)
  rewrite <- Heqab. rewrite <- Heqbc. reflexivity.

  (* a ≦ b /\ b > c /\ a > c *)
  rewrite <- Heqab. rewrite <- Heqbc. reflexivity.

  destruct bc.
  destruct ac.
  (* a > b /\ b ≦ c /\ a ≦ c *)
  rewrite <- Heqac. reflexivity.

  (* a > b /\ b ≦ c /\ a > c *)
  rewrite <- Heqac. reflexivity.

  destruct ac.
  (* a > b /\ b > c /\ a ≦ c *)
  rewrite <- Heqab.
  apply eq_comm in Heqab. apply ble_nat_false in Heqab.
  apply eq_comm in Heqbc. apply ble_nat_false in Heqbc.
  apply eq_comm in Heqac. apply ble_nat_true in Heqac.
(*
  apply ex_falso_quodlibet.
  apply Heqab.
*)
  omega.

  (* a > b /\ b > c /\ a > c *)
  rewrite <- Heqab. rewrite <- Heqac. reflexivity.
Qed.

Lemma max_hdtl_equation : forall l,
  max (head l) (maximum (tail l)) = maximum l.
Proof.
  intros l.
  induction l; simpl.
  apply max0r.
  reflexivity.
Qed.

Lemma max_nil : 
  maximum [] = 0.
Proof.
  simpl. reflexivity.
Qed.

(*
[[
{X = l}
=>                                                  修飾(1)
{X = l /\ 0 = 0}
  Y ::= ANum 0;
{X = l /\ Y = 0}
=>                                                  修飾(2)
{max Y (maximum X) = maximum l}                     ループ不変式
  WHILE (BNot (BIsNull (AId X))) DO
{max Y (maximum X) = maximum l /\ ~isNull X}        ループ不変式かつループ実行条件
=>                                                  修飾(3)
{max (max Y (head X)) (maximum (tail X)) = maimum l}    ... head-tail分解、maxの結合
    IFB (BLe (AId Y) (AHead (AId X))) THEN
{max (max Y (head X)) (maximum (tail X)) = maximum l /\ Y <= head X}  THEN条件
=>                                                  修飾(4)
{max (head X)         (maximum (tail X)) = maximum}     ... max Y (head X) = (head X)
      Y ::= AHead (AId X)
{max Y                (maximum (tail X)) = maximum}
    ELSE
{max (max Y (head X)) (maximum (tail X)) = maximum l /\ Y > head X}  ELSE条件
=>                                                  修飾(5)
{max Y                (maximum (tail X)) = maximum l}   ... max Y (head X) = Y
      SKIP
{max Y                (maximum (tail X)) = maximum l}
    FI;
{max Y (maximum (tail X)) =  maximum l}
    X ::= ATail (AId X)
{max Y (maximum X) =  maximum l}                    ループ不変式
  END
{max Y (maximum X) =  maximum l /\ isNull X}        ループ不変式かつループ終了条件
=>                                                  修飾(6)
{Y = max l}                                              ... maximum X = maximum [] = 0
]]
*)

Theorem max_prog_correct : 
  max_prog_spec.
Proof.
  unfold max_prog_spec, max_program.
  intros l.
  eapply hoare_consequence_post.            (* 修飾(6) *)
  eapply hoare_consequence_pre.             (* 修飾(1) *)
  apply hoare_seq
    with (Q := fun st => aslist (st X) = l /\ asnat (st Y) = 0).
  eapply hoare_consequence_pre.             (* 修飾(2) *)
  apply hoare_while with (P := max_prog_inv l).
  eapply hoare_consequence_pre.             (* 修飾(3) *)
  eapply hoare_seq.
  apply hoare_asgn.                         (* X := tail X *)
  apply hoare_if
    with (P := fun st =>
      max (max (asnat (st Y)) (head (aslist (st X))))
          (maximum (tail (aslist (st X)))) = maximum l).
  eapply hoare_consequence_pre.             (* 修飾(4) *)
  apply hoare_asgn.                         (* Y := head X *)

(* 
   修飾(4)
   {max (max Y (head X)) (maximum (tail X)) = maximum l /\ Y <= head X}
   =>
   {max (head X)         (maximum (tail X)) = maximum}
   *)
   unfold max_prog_inv, assn_sub, update, bassn. simpl.
   intros st [H1 H2].
   unfold max in *.
   rewrite H2 in H1. apply H1.

   eapply hoare_consequence_pre.            (* 修飾(5) *)
   apply hoare_skip.

(*
   修飾(5)
   {max (max Y (head X)) (maximum (tail X)) = maximum l /\ Y > head X}
   =>
   {max Y                (maximum (tail X)) = maximum l}
   *)
   unfold max_prog_inv, assn_sub, update, bassn. simpl.
   intros st [H1 H2].
   unfold max in *.   
   apply not_true_is_false in H2.
   rewrite H2 in H1. apply H1.

(*
   修飾(3)
   {max Y (maximum X) = maximum l /\ ~isNull X}
   =>
   {max (max Y (head X)) (maximum (tail X)) = maimum l}
   *)
   unfold max_prog_inv, assn_sub, update, bassn.
   intros st [H1 H2].
   rewrite <- max_assoc.
   rewrite max_hdtl_equation.
   apply H1.

(*
   修飾(2)
   {X = l /\ Y = 0}
   =>
   {max Y (maximum X) = maximum l}
   *)
   unfold max_prog_inv, assn_sub, update, bassn.
   intros st [H1 H2].   
   rewrite H1. rewrite H2.
   unfold max. simpl. reflexivity.

   apply hoare_asgn.                        (* Y := 0 *)
(*
   修飾(1)
   {X = l}
   =>
   {X = l /\ 0 = 0}
   *)
   unfold assn_sub, update. simpl.
   intros st H.
   split. apply H. reflexivity.

(*
   修飾(6)
   {max Y (maximum X) =  maximum l /\ isNull X}
   =>
   {Y = maximum l}
   *)
   unfold max_prog_inv, update, bassn.
   intros st [H1 H2].
   remember (aslist (st X)) as x'.
   destruct x'.
   (* X = [] のとき *)
   rewrite max_nil in H1. rewrite max0r in H1.
   apply H1.
   (* X = n :: x' のとき *)
   apply ex_falso_quodlibet.
   apply H2.
   unfold beval, aeval.
   rewrite <- Heqx'.
   reflexivity.
Qed.
End Module.                                 (* Maximum *)

(* [] *)
(* END *)
