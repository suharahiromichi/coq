(** * Smallstep_J: スモールステップ操作的意味論 からの抜粋 *)

(** 説明が丁寧なぶん、ビッグステップからスモールステップに至る見通しが悪くなっているので、
   おもちゃの言語だけを対象に、説明のテキストを最小に、抜粋した。*)
(* @suharahiromochi 2013_03_09 *)

(* 
   言語とその評価器：
   - おもちゃの言語の定義、tm_constとtm_plus
   - ビックステップ評価器、eval(||)、E_Const、E_Plus
   - スモールステップの最終状態、value、v_const
   - スモールステップ版、step(==>)、ST_PlusConstConst、ST_Plus1、ST_Plus2
   - マルチステップ簡約、stepmany(==>* )、==>の反射推移閉包（refl_step_closure）として定義する。

   定義：
   - 反射推移閉包、refl_step_closure R。関係Rは、Rを含み反射性と推移性の両者を満たす最小の関係である。
   これは、rsc_refl, rsc_step, rsc_trans を満たす。
   - tは正規形、normal_form R t。二項関係Rがない項のこと。
   = tは正規形、step_normal_form t。stepで他の項に進行できない項のこと。
   = t'はtの正規形、step_normal_form_of t t'。tを==>*で進行した果てがt'である。
   - normalizing R。関係R(の反射推移閉包)は正規化性をもつ。
   （normal_form_ofは、stepmanyだけなので、stepを前につけた）

   定理：
   - step_deterministic : 決定性定理。stepは部分関数、つまり、決定性をもつ。
   - strong_progress : 強進行性定理。定数か、stepによって他の項になる。
   - nf_same_as_value : value(t)と、tが正規形であるのは等価である。
   - normal_forms_unique : step_normal_form_ofは決定性をもつ。
   - stepmany_congr_1、stepmany_congr_2 : 項の一部が==>*で簡約できるなら全体も簡約できる。
   - step_normalizing : step(の反射推移閉包)は正規性をもつ。
   - eval__stepmany : forall t v, t || v -> t ==>* v.
   - step__eval : forall t t' v, t ==> t' -> t' || v -> t || v.
   - stepmany__eval : forall t v, step_normal_form_of t v -> t || v.
 *)

Require Export Imp_J.
Require Import Relations.

(** * おもちゃの言語 *)
Inductive tm : Type :=
  | tm_const : nat -> tm
  | tm_plus : tm -> tm -> tm.

Tactic Notation "tm_cases" tactic(first) ident(c) :=
  first;
  [ Case_aux c "tm_const" | Case_aux c "tm_plus" ].

(** 次がこの言語の標準的な評価器です。
   ビッグステップスタイルですが、
   項の最終結果が数値そのものではなく、また項になっています。*)
Inductive eval : tm -> tm -> Prop :=
  | E_Const : forall n1,
        tm_const n1 || tm_const n1
  | E_Plus : forall t1 n1 t2 n2,
        t1 || tm_const n1 ->
        t2 || tm_const n2 ->
        tm_plus t1 t2 || tm_const (plus n1 n2)
  where " t '||' t' " := (eval t t').

Tactic Notation "eval_cases" tactic(first) ident(c) :=
  first;
  [ Case_aux c "E_Const" | Case_aux c "E_Plus" ].

(** 直観的には、機械の最終状態が常に、
    ある[n]についての [tm_const n] という形の項になることは明らかです。
    そのような項を「値」(_values_)と呼びます。*)
Inductive value : tm -> Prop :=
  v_const : forall n, value (tm_const n).

Reserved Notation " t '==>' t' " (at level 40).
Inductive step : tm -> tm -> Prop :=
  | ST_PlusConstConst : forall n1 n2,
       tm_plus (tm_const n1) (tm_const n2) ==> tm_const (plus n1 n2)
  | ST_Plus1 : forall t1 t1' t2,
        t1 ==> t1' ->
        tm_plus t1 t2 ==> tm_plus t1' t2
  | ST_Plus2 : forall v1 t2 t2',
        value v1 ->
        t2 ==> t2' ->
        tm_plus v1 t2 ==> tm_plus v1 t2'
  where " t '==>' t' " := (step t t').

Tactic Notation "step_cases" tactic(first) ident(c) :=
  first;
  [ Case_aux c "ST_PlusConstConst"
  | Case_aux c "ST_Plus1" | Case_aux c "ST_Plus2" ].

(** 注目すること:

    - 定義しているのは簡約のちょうど1ステップです。
      そこでは1つの[tm_plus]ノードがその値に置き換えられます。

    - 各ステップでは「最左」の準備ができている(つまり、引数が両方とも定数である)
      [tm_plus]ノードを探して、それをその場で書き換えます。
      最初の規則は[tm_plus]ノードをどのように書き換えるかを定めます。
      残りの2つの規則は、それをどう探すかを定めます。

    - 定数の項は、ステップを進めません。*)

(** 再び、変数名が重要な情報を担っています:
    慣習として、[v1]は値のみを変域とし、一方[t1]と[t2]は任意の項を変域とします。
    規則のCoqバージョンでは、同じ目的のために明示的な[value]仮定を使います。*)

(** 関係 [==>] のおもしろい性質の1つは、
   Imp プログラムの言語の評価関係と同様、決定性を持つ(_deterministic_)ということです。
*)
Theorem step_deterministic :
  partial_function step.
Proof.
  unfold partial_function.
  intros x y1 y2 Hy1 Hy2.
  generalize dependent y2.
  induction Hy1; intros y2 Hy2.
  (* (1) tm_const (n1 + n2) = y2 *)
  inversion Hy2.
  (* (1.1) tm_const (n1 + n2) = tm_const (n1 + n2) *)
  (* ST_Const vs. ST_Const *)
  reflexivity.
  (* (1.2) tm_const (n1 + n2) = tm_plus t1' (tm_const n2) *)
  (* ST_Const vs. ST_Plus1 *)
  inversion H2.                           (* H2 : tm_const n1 ==> t1' *)
  (* (1.3) tm_const (n1 + n2) = tm_plus (tm_const n1) t2' *)
  (* ST_Const vs. ST_Plus2 *)
  inversion H3.                             (* H3 : tm_const n2 ==> t2' *)

  (* (2) tm_plus t1' t2 = y2 *)
  inversion Hy2.
  (* (2.1) tm_plus t1' (tm_const n2) = tm_const (n1 + n2) *)
  (* ST_Plus1 vs. ST_Const *)
  rewrite <- H0 in Hy1. inversion Hy1.
  (* (2.2) tm_plus t1' t2 = tm_plus t1'0 t2 *)
  (* ST_Plus1 vs. ST_Plus1 *)
  rewrite <- (IHHy1 t1'0).
  reflexivity. assumption.
  (* (2.3) tm_plus t1' t2 = tm_plus t1 t2' （！） *)
  (* ST_Plus1 vs. ST_Plus2 *)
  subst. destruct H1 as [v1].               (* H1 : value v1 *)
(*
  Hy1 : tm_const v1 ==> t1'
  ============================
  tm_plus t1' t2 = tm_plus (tm_const v1) t2'

  左辺は、ST_Plus1
  Hy1:tm_const v1 ==> t1' ->
  Goal:tm_plus (tm_const v1) t2 ==> tm_plus t1' t2
  右辺は、ST_Plus2
  H1:value v1 -> Hy1:tm_const v1 ==> t2' ->
  Goal:tm_plus (tm_const v1) (tm_const v1) ==> tm_plus (tm_const v1) t2'
  たしかに異なる結果になるので、矛盾が導かれ、ゴールの証明が終了する。。。。でよいのか？
*)
  inversion Hy1.
  
  (* (3) tm_plus v1 t2' = y2 *)
  inversion Hy2.
  (* (3.1) tm_plus (tm_const n1) t2' = tm_const (n1 + n2) *)
  (* ST_Plus2 vs. ST_Const *)
  rewrite <- H2 in Hy1. inversion Hy1.
  (* (3.2) tm_plus v1 t2' = tm_plus t1' t2 （！） *)
  (* ST_Plus2 vs. ST_Plus1 *)
  subst. destruct H as [v1].                (* H : value v1 *)
(*
   H3 : tm_const v1 ==> t1'
   ============================
   tm_plus (tm_const v1) t2' = tm_plus t1' t2
*)
  inversion H3.
  (* (3.3) tm_plus v1 t2' = tm_plus v1 t2'0 *)
  (* ST_Plus2 vs. ST_Plus2 *)
  rewrite <- (IHHy1 t2'0). reflexivity. assumption.
Qed.  

(** 「定理(強進行)」(_Strong Progress_):すべての [t:tm] について
    [t]は値であるか、ある項[t']があって [t ==> t'] となる。
*)
(** この重要な性質は「強進行」(_strong progress_)と呼ばれます。
    これは、すべての項が値であるか、別の項に「進行できる」("make progress")
    ことからきた名称です。「強」("strong")という修飾句は、
    後の章のより細分されたバージョン(単に「進行」("progress")と呼ばれる)
    と区別するためのものです。*)

Theorem strong_progress : forall t,
  value t \/ (exists t', t ==> t').
Proof.
  tm_cases (induction t) Case.
    Case "tm_const". left. apply v_const.
    Case "tm_plus". right. inversion IHt1.
      SCase "l". inversion IHt2.
        SSCase "l". inversion H. inversion H0.
          exists (tm_const (plus n n0)).
          apply ST_PlusConstConst.
        SSCase "r". inversion H0 as [t' H1].
          exists (tm_plus t1 t').
          apply ST_Plus2. apply H. apply H1.
      SCase "r". inversion H as [t' H0].
          exists (tm_plus t' t2).
          apply ST_Plus1. apply H0.  Qed.

(** 「進行する」という概念の拡張から、[value](値)についての興味深い性質がわかります:
    値とはこの意味で進行「できない」項のことに他なりません。
    この事実を述べるために、進行できない項に名前をつけましょう。そういう項を「正規形」
    (_normal form_)と呼びます。*)

Definition normal_form {X:Type} (R:relation X) (t:X) : Prop :=
  ~ exists t', R t t'.

(* This definition actually specifies what it is to be a normal form
    for an _arbitrary_ relation [R] over an arbitrary set [X], not
    just for the particular single-step reduction relation over terms
    that we are interested in at the moment.  We'll re-use the same
    terminology for talking about other relations later in the
    course. *)
(** この定義は実際には、任意の集合[X]の上の「任意の」関係[R]について、
    何が正規形であるかを定めています。
    今興味対象としている、項の上の特定の1ステップ簡約関係に限るものではありません。
    このコースで後に、別の関係の議論において同じ用語法を用います。*)

(* We can use this terminology to generalize the observation we made
    in the strong progress theorem: in this language, normal forms and
    values are actually the same thing. *)
(** 強進行定理の洞察を一般化するためにこの用語を使います。
    この言語では、正規形と値とは実質的に同じものです。*)

Lemma value_is_nf : forall t,
  value t -> normal_form step t.
Proof.
  unfold normal_form. intros t H. inversion H.
  intros contra. inversion contra. inversion H1.
Qed.

Lemma nf_is_value : forall t,
  normal_form step t -> value t.
Proof. (* a corollary of [strong_progress]... *)
  unfold normal_form. intros t H.
  assert (G : value t \/ exists t', t ==> t').
    SCase "Proof of assertion". apply strong_progress.
  inversion G.
    SCase "l". apply H0.
    SCase "r". apply ex_falso_quodlibet. apply H. assumption.  Qed.

Corollary nf_same_as_value : forall t,
  normal_form step t <-> value t.
Proof.
  split. apply nf_is_value. apply value_is_nf.
Qed.

(** なぜこれが興味深いのでしょう？ 2つの理由があります:

    - なぜなら[value](値)は構文的概念です。つまり項の形を見ることで定義されます。
      一方[normal_form](正規形)は意味論的なものです。
      つまり項がどのようにステップを進むかによって定義されます。
      この2つの概念が一致することは自明ではないのです!

    - 実際、正規形と値の概念が一致「しない」言語はたくさん存在します。*)

(** マルチステップ簡約(_multi-step reduction_)関係 [==>*] は1ステップ関係
    [==>]の反射推移閉包です。*)

Definition stepmany := refl_step_closure step.

Notation " t '==>*' t' " := (stepmany t t') (at level 40).

(** ** 正規形再び *)

(* If [t] reduces to [t'] in zero or more steps and [t'] is a
    normal form, we say that "[t'] is a normal form of [t]." *)
(** [t]が0以上のステップで[t']に簡約され、[t']が正規形のとき、
    「[t']は[t]の正規形である」と言います。*)

Definition step_normal_form := normal_form step.

Definition step_normal_form_of (t t' : tm) :=
  (t ==>* t' /\ step_normal_form t').

(* **** Exercise: 3 stars, optional (test_stepmany_3) *)
(** **** 練習問題: ★★★, optional (test_stepmany_3) *)
Theorem normal_forms_unique:
  partial_function step_normal_form_of.
Proof.
  unfold partial_function. unfold step_normal_form_of.  intros x y1 y2 P1 P2.
  destruct P1 as [P11 P12]. destruct P2 as [P21 P22].
  generalize dependent y2.
  (* We recommend using this initial setup as-is! *)
  induction P11; intros y2 Hy2 P2.
  (* (1) x = y2 *)
  inversion Hy2.
  (* (1.1) y2 = y2 *)
  reflexivity.
  (* (1.2) z = y2 *)
  induction P12.
  (* (1.2.1) exists t' : tm, x ==> t' *)
  exists y. apply H.
  (* (2) z = y2 *)
  apply IHP11.
  (* (2.1) step_normal_form z *)
  apply P12.
  (* (2.2) y ==>* y2 *)
  admit.                                    (* XXXXX *)
  (* (2.3) step_normal_form y2 *)
  apply P2.
Qed.

(** [] *)

(** 実のところ、この言語については、より強いことが成立します
    (これは他のすべての言語で成立することではありません):
    「任意の」項[t]はいつかは正規形に到達する、ということです。
    つまり [step_normal_form_of] は全関数です。
    形式的には、[step]関係は正規化性を持つ(_normalizing_)と言います。 *)

Definition normalizing {X:Type} (R:relation X) :=
  forall t, exists t',
    (refl_step_closure R) t t' /\ normal_form R t'.

(** [step]が正規化性を持つことを証明するため、二つの補題を必要とします。

    一つは、[t]が[t']に何ステップかで簡約されるならば、
    [t]が [tm_plus] ノードの左側の子ノードとして現れるときには、
    [t]内で同じ簡約ステップ列が可能である、ということ、
    そしてまた同様のことが、
    [t]が(左側の子ノードが値である)[tm_plus]
    の右側の子ノードとして現れるときにも言える、ということです。*)

Lemma stepmany_congr_1 : forall t1 t1' t2,
     t1 ==>* t1' ->
     tm_plus t1 t2 ==>* tm_plus t1' t2.
Proof.
  intros t1 t1' t2 H. rsc_cases (induction H) Case.
    Case "rsc_refl". apply rsc_refl.
    Case "rsc_step". apply rsc_step with (tm_plus y t2).
        apply ST_Plus1. apply H.
        apply IHrefl_step_closure.  Qed.

(* **** Exercise: 2 stars *)
(** **** 練習問題: ★★ *)
Lemma stepmany_congr_2 : forall t1 t2 t2',
     value t1 ->
     t2 ==>* t2' ->
     tm_plus t1 t2 ==>* tm_plus t1 t2'.
Proof.
  intros t1 t2 t2' H H1.
  induction H1.
  apply rsc_refl.
  eapply rsc_step.
  apply ST_Plus2. apply H. apply H0.
(* 
   IHrefl_step_closure : tm_plus t1 y ==>* tm_plus t1 z
   Goal : refl_step_closure step (tm_plus t1 y) (tm_plus t1 z)
   Goalは ==>*の定義より、tm_plus t1 y ==>* tm_plus t1 z、と同じ。
   *)
  apply IHrefl_step_closure.
Qed.
(** [] *)

(** 「定理」: [step] 関数は正規化性を持つ。つまり、
    任意の[t]に対して、ある[t']があって、[t]からステップを進めると[t']に到達し、
    かつ[t']は正規形である、が成立する。
    *)

Theorem step_normalizing :
  normalizing step.
Proof.
  unfold normalizing.
  tm_cases (induction t) Case.
    Case "tm_const".
      exists (tm_const n).
      split.
      SCase "l". apply rsc_refl.
      SCase "r".
        (* We can use [rewrite] with "iff" statements, not
           just equalities: *)
        rewrite nf_same_as_value. apply v_const.
    Case "tm_plus".
      destruct IHt1 as [t1' H1]. destruct IHt2 as [t2' H2].
      destruct H1 as [H11 H12]. destruct H2 as [H21 H22].
      rewrite nf_same_as_value in H12. rewrite nf_same_as_value in H22.
      inversion H12 as [n1]. inversion H22 as [n2].
      rewrite <- H in H11.
      rewrite <- H0 in H21.
      exists (tm_const (plus n1 n2)).
      split.
        SCase "l".
          apply rsc_trans with (tm_plus (tm_const n1) t2).
          apply stepmany_congr_1. apply H11.
          apply rsc_trans with
             (tm_plus (tm_const n1) (tm_const n2)).
          apply stepmany_congr_2. apply v_const. apply H21.
          apply rsc_R. apply ST_PlusConstConst.
        SCase "r".
          rewrite nf_same_as_value. apply v_const.  Qed.

(** ** ビッグステップ簡約とスモールステップ簡約の同値性 *)

(** 小さなプログラミング言語に対して2つの異なったスタイルで操作的意味論を定義したので、
    その2つの定義が本当に同じものを定義しているのかを考えるのは意味があります!
    実際に定義は一致しているのですが、それを示すことはそれほど簡単にはできません。
    というより、それを正確に主張することが難しいのです。
    なぜなら、一方は1回で進むのが小さなステップだけですが、
    もう一方は大きなまとまりで進むからです。*)

Lemma eval__value : forall t1 t2,
  t1 || t2 -> value t2.
Proof.
  intros t1 t2 HE.
  eval_cases (inversion HE) Case; apply v_const.  Qed.

(* **** Exercise: 3 stars (eval__stepmany) *)
(** **** 練習問題: ★★★ (eval__stepmany) *)

Theorem eval__stepmany : forall t v,
  t || v -> t ==>* v.
Proof.
  intros t v HE.
  induction HE.
  (* (1) tm_const n1 ==>* tm_const n1 *)
  apply rsc_refl.
  (* (2) tm_plus t1 t2 ==>* tm_const (n1 + n2) *)
  apply rsc_trans with (tm_plus (tm_const n1) t2).
  (* (2.1) refl_step_closure step (tm_plus t1 t2) (tm_plus (tm_const n1) t2) *)
  apply stepmany_congr_1.
  apply IHHE1.
  (* (2.2) refl_step_closure step (tm_plus (tm_const n1) t2) (tm_const (n1 + n2)) *)
  apply rsc_trans with (tm_plus (tm_const n1) (tm_const n2)).
  apply stepmany_congr_2.
  apply v_const.
  apply IHHE2.
  (* (2.2.1) refl_step_closure step (tm_plus (tm_const n1) (tm_const n2)) (tm_const (n1 + n2)) *)
  apply rsc_step with (tm_const (n1 + n2)).
  apply ST_PlusConstConst.
  apply rsc_refl.
Qed.
(** [] *)

(* **** Exercise: 3 stars (step__eval) *)
(** **** 練習問題: ★★★ (step__eval) *)
Theorem step__eval : forall t t' v,
     t ==> t' ->
     t' || v ->
     t || v.
Proof.
  intros t t' v HS HE.
  generalize dependent v.
  (* ==>についての帰納、step_eval自体を使いたいから。 *)
  induction HS.
  (* tm_plus (tm_const n1) (tm_const n2) || v *)
  intros v HE.
  inversion HE.
  apply E_Plus. apply E_Const. apply E_Const.
  (* tm_plus t1 t2 || v *)
  intros v HE.
  inversion HE.
  apply E_Plus.
  Check (IHHS (tm_const n1)).
  apply (IHHS (tm_const n1)). apply H1. apply H3.
  (* tm_plus v1 t2 || v *)
  intros v HE.
  inversion HE.
  apply E_Plus.
  Check (IHHS (tm_const n2)).
  apply H2. apply (IHHS (tm_const n2)). apply H4.
Qed.
(** [] *)

Theorem stepmany__eval : forall t v,
  step_normal_form_of t v -> t || v.
Proof.
  intros t v Hnorm.
  unfold step_normal_form_of in Hnorm.
  inversion Hnorm as [Hs Hnf]; clear Hnorm.
  (* v is a normal form -> v = tm_const n for some n *)
  Check nf_same_as_value.                   (* 次のrewriteはapplyでもおなじ。 *)
  rewrite nf_same_as_value in Hnf.
  inversion Hnf. clear Hnf.
  rsc_cases (induction Hs) Case; subst.
  Case "rsc_refl".
    apply E_Const.
  Case "rsc_step".
    eapply step__eval. eassumption. apply IHHs. reflexivity.  Qed.

(** 全部まとめることで、[v]が[t]の正規形であるのは、[t]が[v]に評価されるのと同値である、
    とはっきりと言うことができます。*)    

Corollary stepmany_iff_eval : forall t v,
  step_normal_form_of t v <-> t || v.
Proof.
  split.
  Case "->". apply stepmany__eval.
  Case "<-". unfold step_normal_form_of. intros E. split. apply eval__stepmany.
    assumption. rewrite nf_same_as_value. eapply eval__value. eassumption.  Qed.

 (* END *)
