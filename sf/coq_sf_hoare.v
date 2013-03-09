(** * Hoare_J: ホーア論理 *)
(* * Hoare: Hoare Logic *)

Require Export ImpList_J.

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

Theorem always_loop_hoare : forall P Q,
  {{P}} WHILE BTrue DO SKIP END {{Q}}.
Proof.
  unfold hoare_triple. intros P Q st st' contra.
  apply loop_never_stops in contra.  inversion contra.
Qed.

(* ####################################################### *)
(* ####################################################### *)
(* ####################################################### *)
(* ** Exercise: Reduce to Zero *)
(** ** 練習問題: ゼロへの簡約 *)

(** 次の while ループは、非常にシンプルなため、不変条件が必要ありません:
[[
          {{ True }}
        WHILE X <> 0 DO
            {{ True /\ X <> 0 }} =>
            {{ True }}
          X ::= X - 1
            {{ True }}
        END
          {{ True /\ X = 0 }} =>
          {{ X = 0 }}
]]
   この証明を Coq に変換しなさい。[slow_subtraction]の証明がアイデアの参考になるでしょう。
*)

(* **** Exercise: 2 stars (reduce_to_zero_correct) *)
(** **** 練習問題: ★★ (reduce_to_zero_correct) *)
Definition reduce_to_zero : com :=
  WHILE BNot (BEq (AId X) (ANum 0)) DO
    X ::= AMinus (AId X) (ANum 1)
  END.

Theorem reduce_to_zero_correct :
  {{fun st => True}}
  reduce_to_zero
  {{fun st => asnat (st X) = 0}}.
Proof.
  unfold reduce_to_zero.
  (* 
     {{ True }}
     WHILE X <> 0 DO
     X ::= X - 1
     END
     {{ X = 0 }}
 *)
  eapply hoare_consequence_post.            (* (1) *)
  (* 
     {{ True }}
     WHILE X <> 0 DO
     X ::= X - 1
     END
     {{ True /\ X = 0 }}
 *)
  apply hoare_while.
  (* 
     {{ True /\ X <> 0 }}
     X ::= X - 1
     {{ True }}
 *)
  eapply hoare_consequence_pre.             (* (2) *)
  (* 
     {{ True }}
     X ::= X - 1
     {{ True }}
     *)
  apply hoare_asgn.
  (* (2)の後始末。
     {{True /\ X <> 0}} => {{True}}
     *)
  intros st H. apply H.
  (* (1)の後始末。
     {{True /\ X = 0}} => {{X=0}}
     *)
  intros st H. simpl in H.
  destruct H.
  unfold bassn, beval in H0. simpl in H0.
  apply eq_true_not_negb in H0.  
  rewrite negb_involutive in H0.
  apply beq_nat_true in H0.
  apply H0.
Qed.
(** [] *)

(* ####################################################### *)
(* ####################################################### *)
(* ####################################################### *)
(* ** Exercise: Slow Addition *)
(** ** 練習問題: 遅い足し算 *)

(** 次のプログラムは変数Xを変数Zに足します。
    そのために、Xを減らしてZを増やすということを繰り返します。*)

Definition add_slowly : com :=
  WHILE BNot (BEq (AId X) (ANum 0)) DO
    Z ::= APlus (AId Z) (ANum 1);
    X ::= AMinus (AId X) (ANum 1)
  END.

(* **** Exercise: 3 stars (add_slowly_decoration) *)
(** **** 練習問題: ★★★ (add_slowly_decoration) *)
(*
   [[
   {{ X = x /\ Z = z }} => (1)
   {{ Z + X = z + x }}        ：ループ不変式
   WHILE X <> 0 DO
   {{ Z + X = z + x /\ X <> 0 }} => (2)
   {{ (Z + 1) + (X - 1) = z + x }}
   Z ::= Z + 1;
   {{ Z + (X - 1) = z + x }}
   X ::= X - 1
   {{ Z + X = z + x }}
   END
   {{ Z + X = z + x /\ ~ (X <> 0) }} => (3)
   {{ Z = z + x }}
   ]]
*)
(** [] *)

(* **** Exercise: 3 stars (add_slowly_formal) *)
(** **** 練習問題: ★★★ (add_slowly_formal) *)
(* Now write down your specification of [add_slowly] formally, as a
    Coq [Hoare_triple], and prove it valid. *)
(** Coq の [Hoare_triple]のように、[add_slowly]の仕様を形式的に記述しなさい。
    そして正しさを証明しなさい。*)

Definition add_slowly_invariant x z :=
  fun st => (asnat (st Z)) + (asnat (st X)) = z + x.

Theorem add_slowly_correct : forall x z,
  {{fun st => asnat (st X) = x /\ asnat (st Z) = z}}
  add_slowly
  {{fun st => asnat (st Z) = z + x}}.
Proof.
  (* subtract_slowly を add_slowly に書き換えただけ。 *)
  intros x z. unfold add_slowly.
(*
   {{ X = x /\ Z = z }}
   WHILE X <> 0 DO
   Z ::= Z + 1;
   X ::= X - 1
   END
   {{ Z = z + x }}
]]
*)
  eapply hoare_consequence with (P' := add_slowly_invariant x z). (* pre:(1)、 post:(2) *)
(*
   {{ X + Z = x + z }} (1)
   WHILE X <> 0 DO
   Z ::= Z + 1;
   X ::= X - 1
   END
   {{ Z + X = z + x /\ ~ (X <> 0) }} (2)
]]
*)
  apply hoare_while.
(*
   {{ Z + X = z + x /\ X <> 0 }}
   Z ::= Z + 1;
   X ::= X - 1
   {{ Z + X = z + x }}
*)
  eapply hoare_seq.
(*
   SEQの後の文。
   {{ Z + (X - 1) = z + x }}
   X ::= X - 1
   {{ Z + X = z + x }}
*)
  apply hoare_asgn.
(*
   SEQの前の文。
   {{ Z + X = z + x /\ X <> 0 }} 
   Z ::= Z + 1;
   {{ Z + (X - 1) = z + x }}
*)
  eapply hoare_consequence_pre.             (* (3) *)
(*
   {{ (Z + 1) + (X - 1) = z + x }}
   Z ::= Z + 1;
   {{ Z + (X - 1) = z + x }}
*)
  apply hoare_asgn.

(* (3)の後始末。
   {{ Z + X = z + x /\ X <> 0 }} => {{ (Z + 1) + (X - 1) = z + x }}
*)
  unfold add_slowly_invariant, assn_sub, update, bassn. simpl.
  intros st [Inv GuardTrue].
  remember (beq_nat (asnat (st X)) 0) as Q; destruct Q.
  inversion GuardTrue.
  symmetry in HeqQ.  apply beq_nat_false in HeqQ.
  omega.

(* (1)の後始末。
   {{ X = x /\ Z = z }} => {{ Z + X = z + x }}
   *)
  unfold add_slowly_invariant.
  intros st [HX HZ]. omega.

(* (2)の後始末。
   {{ Z + X = z + x /\ ~ (X <> 0) }} => {{ Z = z + x }}
 *)
  intros st [Inv GuardFalse].
  unfold add_slowly_invariant in Inv.
  unfold add_slowly_invariant.
  unfold bassn in GuardFalse. simpl in GuardFalse.
  destruct (asnat (st X)).
  omega.
  apply ex_falso_quodlibet.   apply GuardFalse. reflexivity.
Qed.

(* hoare_consequence_pre とhoare_consequence_postに分けてみた。
   後始末のゴールの順番が変わることに注意するだけ。
*)
Theorem add_slowly_correct' : forall x z,
  {{fun st => asnat (st X) = x /\ asnat (st Z) = z}}
  add_slowly
  {{fun st => asnat (st Z) = z + x}}.
Proof.
  intros x z. unfold add_slowly.
(*
   {{ X = x /\ Z = z }}
   WHILE X <> 0 DO
   Z ::= Z + 1;
   X ::= X - 1
   END
   {{ Z = z + x }}
]]
*)
   eapply hoare_consequence_pre.            (* (1) *)
(*  with (P' := add_slowly_invariant x z). *)
(*
   {{ X + Z = x + z }}
   WHILE X <> 0 DO
   Z ::= Z + 1;
   X ::= X - 1
   END
   {{ Z = z + x }}
]]
*)
   eapply hoare_consequence_post.           (* (2) *)
(*    with (Q' :=
      fun st : state =>                     (* (2) *)
        add_slowly_invariant x z st /\ ~ bassn (BNot (BEq (AId X) (ANum 0))) st).*)
(*
   {{ X + Z = x + z }} (1)
   WHILE X <> 0 DO
   Z ::= Z + 1;
   X ::= X - 1
   END
   {{ Z + X = z + x /\ ~ (X <> 0) }} (2)
]]
*)
  apply hoare_while
    with (P := add_slowly_invariant x z).
  (* whileの分解にループ不変式を使うのが、筋だと思う。 *)
(*
   {{ Z + X = z + x /\ X <> 0 }}
   Z ::= Z + 1;
   X ::= X - 1
   {{ Z + X = z + x }}
*)
  eapply hoare_seq.
(*
   SEQの後の文。
   {{ Z + (X - 1) = z + x }}
   X ::= X - 1
   {{ Z + X = z + x }}
*)
  apply hoare_asgn.
(*
   SEQの前の文。
   {{ Z + X = z + x /\ X <> 0 }} 
   Z ::= Z + 1;
   {{ Z + (X - 1) = z + x }}
*)
  eapply hoare_consequence_pre.             (* (3) *)
(*
   {{ (Z + 1) + (X - 1) = z + x }}
   Z ::= Z + 1;
   {{ Z + (X - 1) = z + x }}
*)
  apply hoare_asgn.

(* (3)の後始末。
   {{ Z + X = z + x /\ X <> 0 }} => {{ (Z + 1) + (X - 1) = z + x }}
*)
  unfold add_slowly_invariant, assn_sub, update, bassn. simpl.
  intros st [Inv GuardTrue].
  remember (beq_nat (asnat (st X)) 0) as Q; destruct Q.
  inversion GuardTrue.
  symmetry in HeqQ. apply beq_nat_false in HeqQ.
  omega.

(* (2)の後始末。
   {{ Z + X = z + x /\ ~ (X <> 0) }} => {{ Z = z + x }}
 *)
  intros st [Inv GuardFalse].
  unfold add_slowly_invariant in Inv.
  unfold add_slowly_invariant.
  unfold bassn in GuardFalse. simpl in GuardFalse.
  destruct (asnat (st X)).
  omega.
  apply ex_falso_quodlibet. apply GuardFalse. reflexivity.

(* (1)の後始末。
   {{ X = x /\ Z = z }} => {{ Z + X = z + x }}
   *)
  unfold add_slowly_invariant.
  intros st [HX HZ]. omega.
Qed.
(** [] *)

(* ####################################################### *)
(* ####################################################### *)
(* ####################################################### *)
(* ** Example: Parity *)
(** ** 例: パリティ *)
(**
[[
    {{ X = x }} =>
    {{ X = x /\ 0 = 0 }}
  Y ::= 0;
    {{ X = x /\ Y = 0 }} =>
    {{ (Y=0 <-> ev (x-X)) /\ X<=x }}
  WHILE X <> 0 DO
      {{ (Y=0 <-> ev (x-X)) /\ X<=x /\ X<>0 }} =>
      {{ (1-Y)=0 <-> ev (x-(X-1)) /\ X-1<=x }}
    Y ::= 1 - Y;
      {{ Y=0 <-> ev (x-(X-1)) /\ X-1<=x }}
    X ::= X - 1
      {{ Y=0 <-> ev (x-X) /\ X<=x }}
  END
    {{ (Y=0 <-> ev (x-X)) /\ X<=x /\ ~(X<>0) }} =>
    {{ Y=0 <-> ev x }}
]]
*)

Definition find_parity : com :=
  Y ::= (ANum 0);
  WHILE (BNot (BEq (AId X) (ANum 0))) DO
    Y ::= AMinus (ANum 1) (AId Y);
    X ::= AMinus (AId X) (ANum 1)
  END.

Definition find_parity_invariant x :=
  fun st =>
       asnat (st X) <= x
    /\ (asnat (st Y) = 0 /\ ev (x - asnat (st X)) \/ asnat (st Y) = 1 /\ ~ev (x - asnat (st X))).

Lemma not_ev_ev_S_gen: forall n,
  (~ ev n -> ev (S n)) /\
  (~ ev (S n) -> ev (S (S n))).
Proof.
  induction n as [| n'].
  Case "n = 0".
    split; intros H.
    SCase "->".
      apply ex_falso_quodlibet. apply H. apply ev_0.
    SCase "<-".
      apply ev_SS. apply ev_0.
  Case "n = S n'".
    inversion IHn' as [Hn HSn]. split; intros H.
    SCase "->".
      apply HSn. apply H.
    SCase "<-".
      apply ev_SS. apply Hn. intros contra.
      apply H. apply ev_SS. apply contra.  Qed.

Lemma not_ev_ev_S : forall n,
  ~ ev n -> ev (S n).
Proof.
  intros n.
  destruct (not_ev_ev_S_gen n) as [H _].
  apply H.
Qed.

(* より修飾に忠実な判 *)
(*
[[
    {{ X = x }} =>                                (1)
    {{ X = x /\ 0 = 0 }}
  Y ::= 0;
    {{ X = x /\ Y = 0 }} =>                       (2)
    {{ (Y=0 <-> ev (x-X)) /\ X<=x }}
  WHILE X <> 0 DO
      {{ (Y=0 <-> ev (x-X)) /\ X<=x /\ X<>0 }} => (3)
      {{ (1-Y)=0 <-> ev (x-(X-1)) /\ X-1<=x }}
    Y ::= 1 - Y;
      {{ Y=0 <-> ev (x-(X-1)) /\ X-1<=x }}
    X ::= X - 1
      {{ Y=0 <-> ev (x-X) /\ X<=x }}
  END
    {{ (Y=0 <-> ev (x-X)) /\ X<=x /\ ~(X<>0) }} => (4)
    {{ Y=0 <-> ev x }}
]]
*)
Theorem find_parity_correct'' : forall x,
  {{fun st => asnat (st X) = x}}
  find_parity
  {{fun st => asnat (st Y) = 0 <-> ev x}}.
Proof.
  intros x. unfold find_parity.
(*
[[
{{ X = x }}
  Y ::= 0;
  WHILE X <> 0 DO
    Y ::= 1 - Y;
    X ::= X - 1
  END
  {{ Y=0 <-> ev x }}
]]
*)
 eapply hoare_consequence_post.             (* (4) *)
(*
[[
{{ X = x }}
  Y ::= 0;
  WHILE X <> 0 DO
    Y ::= 1 - Y;
    X ::= X - 1
  END
    {{ (Y=0 <-> ev (x-X)) /\ X<=x /\ ~(X<>0) }}
]]
*)
  apply hoare_seq with (Q := find_parity_invariant x). (* (2) *)
  (* 修飾の証明は増えない。つまり(2)の修飾の証明はいらない。 *)
(*
[[
{{ (Y=0 <-> ev (x-X)) /\ X<=x }} ： ループ不変式
  WHILE X <> 0 DO
    Y ::= 1 - Y;
    X ::= X - 1
  END
  {{ (Y=0 <-> ev (x-X)) /\ X<=x /\ ~(X<>0) }}
]]
*)
  apply hoare_while with (P := find_parity_invariant x). (* ゴールは増えない。 *)
(*
[[
{{ (Y=0 <-> ev (x-X)) /\ X<=x /\ X<>0 }}
Y ::= 1 - Y;
X ::= X - 1
{{ Y=0 <-> ev (x-X) /\ X<=x }}
]]
*)
    eapply hoare_seq.
(*
[[
{{ Y=0 <-> ev (x-(X-1)) /\ X-1<=x }}
X ::= X - 1
{{ Y=0 <-> ev (x-X) /\ X<=x }}
]]
*)
    apply hoare_asgn.                       (* X ::= X - 1 *)
(*
[[
{{ (Y=0 <-> ev (x-X)) /\ X<=x /\ X<>0 }}
Y ::= 1 - Y;
{{ Y=0 <-> ev (x-(X-1)) /\ X-1<=x }}
]]
*)
    eapply hoare_consequence_pre.           (* (3) *)
(*
[[
{{ (1-Y)=0 <-> ev (x-(X-1)) /\ X-1<=x }}
Y ::= 1 - Y;
{{ Y=0 <-> ev (x-(X-1)) /\ X-1<=x }}
]]
*)
    apply hoare_asgn.                       (* Y ::= 1 - Y *)
(* (3)の修飾の証明。
   {{ (Y=0 <-> ev (x-X)) /\ X<=x /\ X<>0 }} =>
   {{ (1-Y)=0 <-> ev (x-(X-1)) /\ X-1<=x }}
   *)
    intros st [[Inv1 Inv2] GuardTrue].
    unfold find_parity_invariant, bassn, assn_sub, aeval in *. (* GoalとGuardTrue *)
    rewrite update_eq.
    rewrite (update_neq Y X); auto.
    rewrite (update_neq X Y); auto.
    rewrite update_eq.
    simpl in GuardTrue. destruct (asnat (st X)).
      inversion GuardTrue. simpl.
    split. omega.
    inversion Inv2 as [[H1 H2] | [H1 H2]]; rewrite H1;
                     [right|left]; (split; simpl; [omega |]).
    apply ev_not_ev_S in H2.
    replace (S (x - S n)) with (x-n) in H2 by omega.
    rewrite <- minus_n_O. assumption.
    apply not_ev_ev_S in H2.
    replace (S (x - S n)) with (x - n) in H2 by omega.
    rewrite <- minus_n_O. assumption.
(*
[[
{{ X = x }}
Y ::= 0;
{{ (Y=0 <-> ev (x-X)) /\ X<=x }}
]]
*)
    eapply hoare_consequence_pre.           (* (1) *)
(*
[[
{{ X = x /\ 0 = 0 }}
Y ::= 0;
{{ (Y=0 <-> ev (x-X)) /\ X<=x }}
]]
*)
    apply hoare_asgn.                       (* Y ::= 0 *)
(* (1) の修飾の証明
   {{ X = x }} => {{ X = x /\ 0 = 0 }}
*)
    intros st H.
    unfold assn_sub, find_parity_invariant, update. simpl.
    subst.
    split.
    omega.
    replace (asnat (st X) - asnat (st X)) with 0 by omega.
    left. split. reflexivity.
    apply ev_0. 

(* (4) の修飾の証明。
   {{ (Y=0 <-> ev (x-X)) /\ X<=x /\ ~(X<>0) }} => {{ Y=0 <-> ev x }}
*)
    unfold bassn, find_parity_invariant. simpl.
    intros st [[Inv1 Inv2] GuardFalse].
    destruct (asnat (st X)).
      split; intro.
        inversion Inv2.
           inversion H0 as [_ H1]. replace (x-0) with x in H1 by omega.
           assumption.
           inversion H0 as [H0' _]. rewrite H in H0'. inversion H0'.
        inversion Inv2.
           inversion H0. assumption.
           inversion H0 as [_ H1]. replace (x-0) with x in H1 by omega.
           apply ex_falso_quodlibet. apply H1. assumption.
      apply ex_falso_quodlibet. apply GuardFalse. reflexivity.
Qed.

(* ####################################################### *)
(* ####################################################### *)
(* ** Example: Finding Square Roots *)
(** ** 例: 平方根の探索 *)
(*
{{Treu}} => {{x = x}}              修飾(0)
  X ::= ANum x; 
{{X = x}} => {{X = x /\ 0 = 0}}    修飾(1)
  Z ::= ANum 0;
{{X = x /\ Z = 0}}                 修飾(2)
=> {{X = x /\ Z * Z <= x}}         ループ不変式
  WHILE BLe (AMult (APlus (ANum 1) (AId Z))
                   (APlus (ANum 1) (AId Z)))
            (AId X) DO
{{X = x /\ Z * Z <= x /\ (Z+1)*(Z+1) <= x}}  ループ不変式かつループ実行条件
=> {{X = x /\ (Z+1)*(Z+1) <= x}}   修飾(3)
    Z ::= APlus (ANum 1) (AId Z)
{{X = x /\ Z * Z <= x}}            ループ不変式
END
{{X = x /\ Z * Z <= x /\ (Z+1)*(Z+1) > x}}   ループ不変式かつ終了条件
=> {{Z * Z <= x /\ (Z+1)*(Z+1) > x}}  要求仕様、 修飾(4)
*)

Definition sqrt_loop : com :=
  WHILE BLe (AMult (APlus (ANum 1) (AId Z))
                   (APlus (ANum 1) (AId Z)))
            (AId X) DO
    Z ::= APlus (ANum 1) (AId Z)
  END.

Definition sqrt_com : com :=
  Z ::= ANum 0;
  sqrt_loop.

Definition sqrt_spec (x : nat) : Assertion :=
  fun st =>
       ((asnat (st Z)) * (asnat (st Z))) <= x
    /\ ~ (((S (asnat (st Z))) * (S (asnat (st Z)))) <= x).

Definition sqrt_inv (x : nat) : Assertion :=
  fun st =>
       asnat (st X) = x
    /\ ((asnat (st Z)) * (asnat (st Z))) <= x.

Theorem random_fact_1 : forall st,
     (S (asnat (st Z))) * (S (asnat (st Z))) <= asnat (st X) ->
     bassn (BLe (AMult (APlus (ANum 1) (AId Z))
                       (APlus (ANum 1) (AId Z)))
                (AId X)) st.
Proof.
  intros st Hle.  unfold bassn. simpl.
  destruct (asnat (st X)) as [|x'].
  Case "asnat (st X) = 0".
    inversion Hle.
  Case "asnat (st X) = S x'".
    simpl in Hle. apply le_S_n in Hle.
    remember (ble_nat (plus (asnat (st Z))
                      ((asnat (st Z)) * (S (asnat (st Z))))) x')
      as ble.
    destruct ble. reflexivity.
    symmetry in Heqble. apply ble_nat_false in Heqble.
    unfold not in Heqble. apply Heqble in Hle. inversion Hle.
Qed.

Theorem random_fact_2 : forall st,
     bassn (BLe (AMult (APlus (ANum 1) (AId Z))
                       (APlus (ANum 1) (AId Z)))
                (AId X)) st ->
       asnat (aeval st (APlus (ANum 1) (AId Z)))
     * asnat (aeval st (APlus (ANum 1) (AId Z)))
     <= asnat (st X).
Proof.
  intros st Hble. unfold bassn in Hble. simpl in *.
  destruct (asnat (st X)) as [| x'].
  Case "asnat (st X) = 0".
    inversion Hble.
  Case "asnat (st X) = S x'".
    apply ble_nat_true in Hble. omega. Qed.

(* 修飾を注釈版 *)
Theorem sqrt_com_correct' : forall x,
  {{fun st => True}} (X ::= ANum x; sqrt_com) {{sqrt_spec x}}.
Proof.
  intros x.
(*
{{Treu}}
  X ::= ANum x; 
  Z ::= ANum 0;
  WHILE BLe (AMult (APlus (ANum 1) (AId Z))
                   (APlus (ANum 1) (AId Z)))
            (AId X) DO
    Z ::= APlus (ANum 1) (AId Z)
END
{{Z * Z <= x /\ (Z+1)*(Z+1) > x}} 要求仕様
*)
  apply hoare_seq with (Q := fun st => asnat (st X) = x).
(*
{{X = x}}
  Z ::= ANum 0;
  WHILE BLe (AMult (APlus (ANum 1) (AId Z))
                   (APlus (ANum 1) (AId Z)))
            (AId X) DO
    Z ::= APlus (ANum 1) (AId Z)
END
{{Z * Z <= x /\ (Z+1)*(Z+1) > x}} 要求仕様
*)
  Case "sqrt_com".
    unfold sqrt_com.
    apply hoare_seq with (Q := fun st => asnat (st X) = x
                                      /\ asnat (st Z) = 0).

(*
{{X = x /\ Z = 0}}
  WHILE BLe (AMult (APlus (ANum 1) (AId Z))
                   (APlus (ANum 1) (AId Z)))
            (AId X) DO
    Z ::= APlus (ANum 1) (AId Z)
END
{{Z * Z <= x /\ (Z+1)*(Z+1) > x}} 要求仕様
*)
    SCase "sqrt_loop".
      unfold sqrt_loop.
      eapply hoare_consequence.
(*
{{X = x /\ Z * Z <= x}}         ループ不変式
  WHILE BLe (AMult (APlus (ANum 1) (AId Z))
                   (APlus (ANum 1) (AId Z)))
            (AId X) DO
    Z ::= APlus (ANum 1) (AId Z)
END
{{X = x /\ Z * Z <= x /\ (Z+1)*(Z+1) > x}}   ループ不変式かつ終了条件
*)
      apply hoare_while with (P := sqrt_inv x).
(*
{{X = x /\ Z * Z <= x /\ (Z+1)*(Z+1) <= x}}  ループ不変式かつループ実行条件
    Z ::= APlus (ANum 1) (AId Z)
{{X = x /\ Z * Z <= x}}            ループ不変式
*)
      SSCase "loop preserves invariant".
        eapply hoare_consequence_pre.
(*
{{X = x /\ (Z+1)*(Z+1) <= x}}   修飾(3)
    Z ::= APlus (ANum 1) (AId Z)
{{X = x /\ Z * Z <= x}}            ループ不変式
*)
        apply hoare_asgn.                   (* Z := 1 + Z *)
(*
   修飾(3)の証明
{{X = x /\ Z * Z <= x /\ (Z+1)*(Z+1) <= x}}  ループ不変式かつループ実行条件
=> {{X = x /\ (Z+1)*(Z+1) <= x}}
*)
        intros st H.
        unfold assn_sub. unfold sqrt_inv in *.
        inversion H as [[HX HZ] HP]. split.
        SSSCase "X is preserved".
          rewrite update_neq; auto.
        SSSCase "Z is updated correctly".
          rewrite (update_eq (aeval st (APlus (ANum 1) (AId Z))) Z st).
          subst. apply random_fact_2. assumption.
(*  修飾(3)終わり *)
(*
   修飾(2)の証明
{{X = x /\ Z = 0}} => {{X = x /\ Z * Z <= x}}   ループ不変式
*)
      SSCase "invariant is true initially".
        intros st H. inversion H as [HX HZ].
        unfold sqrt_inv. split. assumption.
        rewrite HZ. simpl. omega.
(*  修飾(2)終わり *)
(*
   修飾(4)の証明
{{X = x /\ Z * Z <= x /\ (Z+1)*(Z+1) > x}}   ループ不変式かつ終了条件
=> {{Z * Z <= x /\ (Z+1)*(Z+1) > x}}         要求仕様
*)
      SSCase "after loop, spec is satisfied".
        intros st H. unfold sqrt_spec.
        inversion H as [HX HP].
        unfold sqrt_inv in HX.  inversion HX as [HX' Harith].
        split. assumption.
        intros contra. apply HP. clear HP.
        simpl. simpl in contra.
        apply random_fact_1. subst x. assumption.
(*  修飾(4)終わり *)
(*
{{X = x}}
  Z ::= ANum 0;
{{X = x /\ Z = 0}}
*)
    SCase "Z set to 0".
      eapply hoare_consequence_pre.
(*
{{X = x /\ 0 = 0}}
  Z ::= ANum 0;
{{X = x /\ Z = 0}}
*)
(*
   修飾(1)の証明
{{X = x}} => {{X = x /\ 0 = 0}}
 *)
      apply hoare_asgn.                     (* Z := 0 *)
      intros st HX.
      unfold assn_sub. split.
      rewrite update_neq; auto.
      rewrite update_eq; auto.
(*  修飾(1)終わり *)
(*
{{Treu}}
  X ::= ANum x; 
{{X = x}}
*)
  Case "assignment of X".
    eapply hoare_consequence_pre.
(*
{{x = x}}
  X ::= ANum x; 
{{X = x}}
*)
    apply hoare_asgn.                       (* X := x *)
(*
   修飾(0)の証明
{{Treu}} => {{x = x}}
*)
    intros st H.
    unfold assn_sub. rewrite update_eq; auto.
(*  修飾(0)終わり *)
  Qed.
(** [] *)

(* ####################################################### *)
(* ####################################################### *)
(* ####################################################### *)
(* ** Exercise: Factorial *)
(** ** 練習問題: 階乗 *)

Module Factorial.

Fixpoint real_fact (n:nat) : nat :=
  match n with
  | O => 1
  | S n' => n * (real_fact n')
  end.

(* Recall the factorial Imp program: *)
(** 階乗を計算する Imp プログラムを思い出してください: *)

Definition fact_body : com :=
  Y ::= AMult (AId Y) (AId Z);
  Z ::= AMinus (AId Z) (ANum 1).

Definition fact_loop : com :=
  WHILE BNot (BEq (AId Z) (ANum 0)) DO
    fact_body
  END.

Definition fact_com : com :=
  Z ::= (AId X);
  Y ::= ANum 1;
  fact_loop.

(* **** Exercise: 3 stars, optional (fact_informal) *)
(** **** 練習問題: ★★★, optional (fact_informal) *)
(* Decorate the [fact_com] program to show that it satisfies the
    specification given by the pre and postconditions below.  Just as
    we have done above, you may elide the algebraic reasoning about
    arithmetic, the less-than relation, etc., that is (formally)
    required by the rule of consequence:

(* FILL IN HERE *)
[[
    {{ X = x }}
  Z ::= X;
  Y ::= 1;
  WHILE Z <> 0 DO
    Y ::= Y * Z;
    Z ::= Z - 1
  END
    {{ Y = real_fact x }}
]]
*)
(** [fact_com]を修飾して、以下の事前条件、事後条件として与えられる仕様を満たすことを示しなさい。
    帰結規則のために(形式的には)算術式や不等号などについての推論が必要になりますが、
    ここまでと同様、それらは省略して構いません。

回答：
[[
{{True}} => {{ X = x }}  修飾(1)
  Z ::= X;
{{Z = x}} => {{Z = x /\ 1 = 1}} 修飾(2)
  Y ::= 1;
{{Z = x /\ Y = 1}} =>  修飾(3)
{{Y*real_fact(Z) = real_fact(x)}} ループ不変式
  WHILE Z <> 0 DO
{{Y * real_fact(Z) = real_fact(x) /\ Z <> 0}} ループ不変式、かつ、ループ実行条件
=> {{Y * Z * real_fact(Z - 1) = real_fact(x)}} 修飾(4)
    Y ::= Y * Z;
{{Y * real_fact(Z - 1) = real_fact(x)}}
    Z ::= Z - 1
{{Y * real_fact(Z) = real_fact(x)}} ループ不変式
  END
{{Y * real_fact(Z) = real_fact(x) /\ Z = 0}} ループ不変式、かつ、終了条件
=> {{ Y = real_fact x }} 要求仕様、修飾(5)
]]
*)
(** [] *)


(* ####################################################### *)
(* ####################################################### *)
(* **** Exercise: 4 stars, optional (fact_formal) *)
(** **** 練習問題: ★★★★, optional (fact_formal) *)
(* Prove formally that fact_com satisfies this specification,
    using your informal proof as a guide.  You may want to state
    the loop invariant separately (as we did in the examples). *)
(** fact_com がこの仕様を満たすことを、形式的に証明しなさい。
    その際、自分の非形式的な証明をガイドとして使いなさい。
    (例で行ったように)ループ不変条件を分離して主張しても構いません。*)

(* 要求仕様 使ってない *)
Definition fact_spec (x : nat) : Assertion :=
  fun st =>
       asnat (st Z) = real_fact x.

Definition fact_inv (x : nat) : Assertion :=
  fun st =>
       asnat (st Y) * real_fact (asnat (st Z)) = real_fact x.

Theorem fact_com_correct : forall x,
  {{fun st => asnat (st X) = x}} fact_com
  {{fun st => asnat (st Y) = real_fact x}}.
Proof.
  unfold fact_com, fact_loop, fact_body.
  intros x.
  eapply hoare_consequence_post.            (* 修飾(5) *)
  eapply hoare_consequence_pre.             (* 修飾(1) *)
  apply hoare_seq with (Q := fun st => asnat (st Z) = x).
  eapply hoare_consequence_pre.             (* 修飾(2) *)
  apply hoare_seq with (Q := fun st => asnat (st Z) = x /\ asnat (st Y) = 1).
  eapply hoare_consequence_pre.             (* 修飾(3) *)
  apply hoare_while with (P := fact_inv x).
  eapply hoare_consequence_pre.             (* 修飾(4) *)
  eapply hoare_seq.
  apply hoare_asgn.                         (* Z := Z - 1 *)
  apply hoare_asgn.                         (* Y := Y * Z *)
(*
   修飾(4)の証明
   {{Y * real_fact(Z) = real_fact(x) /\ Z <> 0}} ループ不変式、かつ、ループ実行条件
   => {{Y * Z * real_fact(Z - 1) = real_fact(x)}}
 *)
  unfold assn_sub, bassn, fact_inv, update.
  intros st H. simpl.
  destruct H as [H1 H2].
  simpl in H2.
  (* ここの証明は、Imp_J.vの fact_body_preserves_invariant とおなじ。 *)
  destruct (asnat (st Z)) as [| z'].
  apply ex_falso_quodlibet. inversion H2.
  rewrite <- H1. rewrite <- mult_assoc.
  replace (S z' - 1) with z' by omega.
  reflexivity.
(* 修飾(4)の証明、終わり *)

(*
   修飾(3)の証明
   {{Z = x /\ Y = 1}} => {{Y*real_fact(Z) = real_fact(x)}} ループ不変式
*)
  intros st H.
  unfold fact_inv.
  destruct H as [H1 H2].
  rewrite H1. rewrite H2. omega.
(* 修飾(3)の証明、終わり *)

  apply hoare_asgn.                         (* Y := 1 *)
(*
   修飾(2)の証明
   {{Z = x}} => {{Z = x /\ 1 = 1}}
*)
  unfold assn_sub, update.
  intros st H.
  split; try(rewrite <- H); simpl; reflexivity.
(* 修飾(2)の証明、終わり *)

  apply hoare_asgn.                         (* Z := X *)
(*
   修飾(1)の証明
   {{True}} => {{ X = x }}
*)
  unfold assn_sub, update. simpl.
  intros st H.
  apply H.
(* 修飾(1)の証明、終わり *)

(*
   修飾(5)の証明
   {{Y * real_fact(Z) = real_fact(x) /\ Z = 0}}
   ループ不変式、かつ、終了条件
   => {{ Y = real_fact x }} 要求仕様
   *)
  unfold assn_sub, bassn, fact_inv, update.
  intros st H. simpl.
  destruct H as [H1 H2].
  simpl in H2.
  destruct (asnat (st Z)) as [| z'].
  rewrite <- H1. simpl. omega.
  apply ex_falso_quodlibet. apply H2.
  reflexivity.
Qed.
(** [] *)

End Factorial.

(* ####################################################### *)
(* ####################################################### *)
(* ** Reasoning About Programs with Lists *)
(** ** リストを扱うプログラムについての推論 *)

(* **** Exercise: 3 stars (list_sum) *)
(** **** 練習問題: ★★★ (list_sum) *)
(* Here is a direct definition of the sum of the elements of a list,
    and an Imp program that computes the sum. *)
(** 以下は、リストの要素の合計の直接的定義と、その合計を計算するImpプログラムです *)

Definition sum l := fold_right plus 0 l.

Definition sum_program :=
  Y ::= ANum 0;
  WHILE (BIsCons (AId X)) DO
    Y ::= APlus (AId Y) (AHead (AId X)) ;
    X ::= ATail (AId X)
  END.

(* ループ不変式 *)
Definition sum_program_inv l : Assertion :=
  fun st =>
    asnat (st Y) + sum (aslist (st X)) = sum l.

(* Provide an _informal_ proof of the following specification of
    [sum_program] in the form of a decorated version of the
    program. *)
(** [sum_program]の以下の仕様の「非形式的な」証明を、
    修飾を付けたバージョンのプログラムの形で与えなさい。*)

Definition sum_program_spec := forall l,
  {{ fun st => aslist (st X) = l }}
  sum_program
  {{ fun st => asnat (st Y) = sum l }}.

(*
[[
{X = 1} => {X = 1 /\ 0 = 0}              修飾(1)
Y := 0;
{X = 1 /\ Y = 0} => {Y + sum X = sum l}  修飾(2)、ループ不変式
WHILE (isCons X) DO
{Y + sum X = sum l /\ isCons X}          ループ不変式かつループ実行条件
=> {Y + head X + sum (tail X) = sum l}   修飾(3)
  Y := Y + head X;
{Y + sum (tail X) = sum l}
  X := tail X;
{Y + sum X = sum l}                      ループ不変式
END
{Y + sum X = sum l /\ ~isCons X}         ループ不変式かつループ終了条件
=> {Y = sum l}                           修飾(4)、要求仕様
]]
*)

Lemma sum_head_tail : forall l,
  head l + sum (tail l) = sum l.
Proof.
  intros l.
  induction l; simpl; reflexivity.
Qed.

Theorem sum_program_correct :
  sum_program_spec.
Proof.
  unfold sum_program_spec.
  intros l.
  eapply hoare_consequence_post.            (* 修飾(4) *)
  eapply hoare_consequence_pre.             (* 修飾(1) *)
  eapply hoare_seq
    with (Q := fun st => aslist (st X) = l /\ asnat (st Y) = 0).
  eapply hoare_consequence_pre.             (* 修飾(2) *)
  apply hoare_while with (P := sum_program_inv l).
  eapply hoare_consequence_pre.             (* 修飾(3) *)
  eapply hoare_seq.
  apply hoare_asgn.                         (* X := tail X *)
  apply hoare_asgn.                         (* Y := Y + head X *)
(*
   修飾(3)
   {Y + sum X = sum l /\ isCons X}
   => {Y + head X + sum (tail X) = sum l}
   *)
  unfold sum_program_inv, assn_sub. simpl.
  intros st [H1 H2].
  unfold bassn in H2.
  unfold update. simpl.
  rewrite plus_assoc_reverse.
  rewrite (sum_head_tail (aslist (st X))).
  apply H1.

(*
   修飾(2)
   {X = 1 /\ Y = 0} => {Y + sum X = sum l}
   *)
  unfold sum_program_inv. simpl.
  intros st [H1 H2].
  rewrite H2. rewrite H1. reflexivity.

  apply hoare_asgn.                         (* Y := 0 *)
(*
   修飾(1)
   {X = l} => {X = l /\ 0 = 0}
   *)
  unfold assn_sub, update. simpl.
  intros st H.
  split. apply H. reflexivity.

(*
   修飾(4)
   {Y + sum X = sum l /\ ~(isCons X)} => {Y = sum l}
   *)
  unfold sum_program_inv, bassn, update.
  intros st [H1 H2].
  remember (aslist (st X)) as x'.
  destruct x'.
  (* X = [] のとき。 *)
  rewrite <- H1. simpl. omega.
  (* X = n :: x' のとき。 *)  
  apply ex_falso_quodlibet.
  apply H2. simpl.
  rewrite <- Heqx'.
  reflexivity.
Qed.
(** [] **)

(* **** Exercise: 4 stars, optional (list_reverse) *)
(** **** 練習問題: ★★★★, optional (list_reverse) *)
(* Recall the function [rev] from Poly.v, for reversing lists. *)
(** Poly_J.vの[rev]を思い出してください。リストを逆順にするものです。*)

Fixpoint snoc {X:Type} (l:list X) (v:X) : (list X) :=
  match l with
  | nil      =>  [ v ]
  | cons h t => h :: (snoc t v)
  end.

Lemma snoc_equation : forall (A : Type) (h:A) (x y : list A),
  snoc x h ++ y = x ++ h :: y.
Proof.
  intros A h x y.
  induction x.
    Case "x = []". reflexivity.
    Case "x = cons". simpl. rewrite IHx. reflexivity.
Qed.

Lemma append_nil : forall (A : Type) (l : list A),
  l ++ [] = l.
Proof.
  induction l.
    reflexivity.
    simpl. rewrite IHl. reflexivity.
Qed.

Fixpoint rev {X:Type} (l:list X) : list X :=
  match l with
  | nil      => []
  | cons h t => snoc (rev t) h
  end.

Lemma rev_equation : forall (A : Type) (h : A) (x y : list A),
  rev (h :: x) ++ y = rev x ++ h :: y.
Proof.
  intros. simpl. apply snoc_equation.
Qed.

Definition rev_program :=
  Y ::= ANil;
  WHILE BIsCons (AId X) DO
    Y ::= ACons (AHead (AId X)) (AId Y);
    X ::= ATail (AId X)
  END.

Definition rev_program_inv l : Assertion :=
  fun st =>
    rev (aslist (st X)) ++ aslist (st Y) = rev l.

Definition rev_program_spec := forall l,
  {{fun st => aslist (st X) = l}}
  rev_program
  {{fun st => aslist (st Y) = rev l}}.

(*
[[
{X = l} => {X = l /\ nil = nil}             修飾(1)
  Y ::= ANil;
{X = l /\ Y = nil} => {rev X ++ Y = rev l}  修飾(2)、ループ不変式
  WHILE BsCons (AId X) DO
{rev X ++ Y = rev l /\ BsCons (AId X)}      ループ不変式かつループ実行条件
=> {rev (tail X) ++ ((head X) :: Y) = rev l}  修飾(3)
    Y ::= ACons (AHead (AId X)) (AId Y);
{rev (tail X) ++ Y = rev l}
    X ::= ATail (AId X)
{rev X ++ Y = rev l}                        ループ不変式
  END.
{rev X ++ Y = rev l /\ ~(isCons X)}         ループ不変式かつループ終了条件
=> {Y = rev l}                              修飾(4)、要求仕様
]]
*)

Theorem rev_program_correct :
  rev_program_spec.
Proof.
  unfold rev_program_spec, rev_program.
  intros l.
  eapply hoare_consequence_post.            (* 修飾(4) *)
  eapply hoare_consequence_pre.             (* 修飾(1) *)
  apply hoare_seq
    with (Q := fun st => aslist (st X) = l /\ aslist (st Y) = []).
  eapply hoare_consequence_pre.             (* 修飾(2) *)
  apply hoare_while
    with (P := rev_program_inv l).
  eapply hoare_consequence_pre.             (* 修飾(3) *)
  eapply hoare_seq.
  apply hoare_asgn.                         (* Y := tail X *)
  apply hoare_asgn.                         (* Y := (head X) :: Y *)
(* 
   修飾(3)
   {rev X ++ Y = rev l /\ BsCons (AId X)}
   => {rev (tail X) ++ ((head X) :: Y) = rev l}
   *)
  unfold rev_program_inv, assn_sub, bassn, update. simpl.
  intros st [H1 H2].
  rewrite <- (rev_equation nat
    (head (aslist (st X)))                  (* h *)
    (tail (aslist (st X)))                  (* x *)
    (aslist (st Y))).                       (* y *)
   (* (head X) :: (tail X) = X にならない。
      （(head []) :: (tail []) = 0 :: [] = [0] だから。）
      だから、Xをnilとconsに分けて証明する。
      *)
   remember (aslist (st X)) as x'.
   destruct x'.
(* X = [] *)
   simpl.
   (* 0 :: aslist (st Y) = rev l 、、、これは変 *)
   apply ex_falso_quodlibet.
   inversion H2.
(* X = n :: x' *)
   rewrite <- H1.
   simpl.
   reflexivity.

(*
   修飾(2)
   {X = l /\ Y = nil} => {rev X ++ Y = rev l}
   *)
   unfold rev_program_inv.
   intros st [H1 H2].
   rewrite H1. rewrite H2.
   apply append_nil.

   apply hoare_asgn.                        (* Y := nil *)
(*
   修飾(1)
   {X = l} => {X = l /\ nil = nil}
   *)
   unfold assn_sub, update. simpl.
   intros st H.
   split. apply H. reflexivity.

(* 
   修飾(4)
   {rev X ++ Y = rev l /\ ~(isCons X)} => {Y = rev l}
   *)
   unfold rev_program_inv, bassn, update.
   intros st [H1 H2].
   rewrite <- H1.
   remember (aslist (st X)) as x'.
   destruct x'.
(* X = [] のとき。 *)
   simpl. reflexivity.
(* X = n :: x' のとき *)
   apply ex_falso_quodlibet.
   apply H2. simpl. rewrite <- Heqx'.
   reflexivity.
Qed.
(** [] *)

(* ####################################################### *)
(* ####################################################### *)
(** リストの最大値を求めるプログラム
   *)

Definition max a b :=
  if ble_nat a b then b else a.

Definition maximum l := fold_right max 0 l.

Eval compute in maximum [].
Eval compute in maximum [1, 2, 3, 1].

Definition max_program :=
  Y ::= ANum 0;
  WHILE (BIsCons (AId X)) DO
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
  WHILE (BIsCons (AId X)) DO
{max Y (maximum X) = maximum l /\ isCons X}         ループ不変式かつループ実行条件
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
{max Y (maximum X) =  maximum l /\ ~(isCons X)}     ループ不変式かつループ終了条件
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
   {max Y (maximum X) = maximum l /\ isCons X}
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
   {max Y (maximum X) =  maximum l /\ ~(isCons X)}
   =>
   {Y = max l}
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

(* ####################################################### *)
(* ####################################################### *)
(* 次節の問題だが、ここ方法で解いて見る。 *)
(** [X]に現在設定されている値を変数[Y]に代入する遠回りの方法は、
    [Y]を[0]から始め、
    [X]を[0]になるまで減らしていきながら、その各ステップで[Y]を増やしていくことです。
    com の方法で解いてみる *)
(*
[[
      {{ X = x }} => {0 = 0}                                   (1)
    Y ::= 0;
      {{ X = x /\ Y = 0 }} => {{ X + Y = x }}      ループ不変式 (2)
    WHILE X <> 0 DO
        {{ X + Y = x /\ X > 0 }}
        => {{ (X - 1) + (Y + 1) = x }}                         (3)
      X ::= X - 1;
        {{ X + Y + 1 = x }}
      Y ::= Y + 1;
        {{ X + Y = x }}
    END
      {{ X + Y = x /\ X = 0 }} => {{ Y = x }}                   (4)
]]
*)

Definition slow_asgn_prog :=
  Y ::= (ANum 0);
  WHILE (BNot (BEq (AId X) (ANum 0))) DO
    X ::= AMinus (AId X) (ANum 1);
    Y ::= APlus (AId Y) (ANum 1)
  END.

Definition slow_asgn_prog_inv x : Assertion :=
  fun st =>
    asnat (st X) + asnat (st Y) = x.

Definition slow_asgn_prog_spec := forall x,
  {{ fun st => asnat (st X) = x }}
  slow_asgn_prog
  {{ fun st => asnat (st Y) = x }}.

Lemma negb_not_true_iff : forall b, negb b <> true <-> b = true.
Proof.
  intros b.
  split.
  intros H.
  apply eq_true_negb_classical.             (* XXX *)
  apply H.
  intros H.
  
  rewrite H. simpl.
  unfold not.
  intros. inversion H0.
Qed.

Lemma pp : forall x y, x + y = (x - 1) + (y + 1). (* XXX *)
Proof.
   intros x y.
  SearchAbout plus.
  rewrite (plus_assoc (x - 1) y 1).
Admitted.

Theorem slow_asgn_prog_correct :
  slow_asgn_prog_spec.
Proof.
  unfold slow_asgn_prog_spec.
  intros x.
  eapply hoare_consequence_post.            (* 修飾(4) *)
  eapply hoare_consequence_pre.             (* 修飾(1) *)
  eapply hoare_seq
    with (Q := fun st => asnat (st X) = x /\ asnat (st Y) = 0).
  eapply hoare_consequence_pre.             (* 修飾(2) *)
  apply hoare_while with (P := slow_asgn_prog_inv x).
  eapply hoare_consequence_pre.             (* 修飾(3) *)
  eapply hoare_seq.
  apply hoare_asgn.                         (* Y := Y + 1 *)
  apply hoare_asgn.                         (* X := X - 1 *)
(*
   修飾(3)
   {{ X + Y = x /\ X > 0 }}
   => {{ (X - 1) + (Y + 1) = x }}                         (3)
*)
  unfold slow_asgn_prog_inv, assn_sub. simpl.
  intros st [H1 H2].
  unfold bassn in H2.
  unfold update. simpl.
  rewrite <- pp.                            (* XXXX *)
  apply H1.

(*
   修飾(2)
   {{ X = x /\ Y = 0 }} => {{ X + Y = x }}
   *)
  unfold slow_asgn_prog_inv.
  intros st [H1 H2].
  rewrite H2. rewrite H1. omega.

  apply hoare_asgn.                         (* X := x *)
(*
   修飾(1)
   {{ X = x }} => {0 = 0}                                   (1)
   *)
  unfold assn_sub, update. simpl.
  intros st H.
  split. apply H. reflexivity.

(*
   修飾(4)
   {{ X + Y = x /\ X = 0 }} => {{ Y = x }}                  (4)
   *)
  unfold slow_asgn_prog_inv, bassn. simpl.
  intros st [H1 H2].
  apply negb_not_true_iff in H2.
  apply beq_nat_true in H2.
  rewrite H2 in H1.
  rewrite plus_O_n in H1.
  apply H1.
Qed.

 (* END *)
