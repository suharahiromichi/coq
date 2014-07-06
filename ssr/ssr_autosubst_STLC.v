(**
STLC

ソフトウェアの基礎 Stlc_J: 単純型付きラムダ計算
http://proofcafe.org/sf/Stlc_J.html

これを Autosubst で解き直してみる。
https://www.ps.uni-saarland.de/autosubst/
https://www.ps.uni-saarland.de/autosubst/doc/toc.html
*)

(*
以下を同じディレクトリに置いて、
Autosubst.v  Lib.v  MMap.v  ssr_autosubst_STLC.v
coq_makefile *.v > Makefile
*)

Require Import Autosubst MMap.
Require Import Relations.
Require Import Relation_Operators.          (* rt1n_trans が上書きされぬよう。 *)
Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq.

(* Set Implicit Arguments. *)
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ## 項と型 *)

(** ### 型 *)
Inductive type : Type :=
| ty_var (x : var)                          (* TyVar System F *)
| ty_arr (A B : type)                       (* Arr System F *)
| ty_all (A : {bind type})                  (* All System F *)
| ty_Bool
| ty_arrow (A B : type).

(** ### 項 *)
Inductive term :=                           (* tm *)
| tm_var (x : var)                          (* TVar *)
| tm_app (s t : term)                       (* App *)
| tm_abs (T : type) (s : {bind term})       (* Lam *)
| tm_true
| tm_false
| tm_if (cc ct ce : term).

(**
Substitution Lemmas

System Fから取ってきたので、STLCには不要のものもあるはず。
*)
Instance VarConstr_type : VarConstr type. derive. Defined.
Instance Rename_type : Rename type. derive. Defined.
Instance Subst_type : Subst type. derive. Defined.

Instance SubstLemmas_type : SubstLemmas type. derive. Qed.

Instance HSubst_term : HSubst type term. derive. Defined.

Instance VarConstr_term : VarConstr term. derive. Defined.
Instance Rename_term : Rename term. derive. Defined.
Instance Subst_term : Subst term. derive. Defined.

Instance HSubstLemmas_term : HSubstLemmas type term. derive. Qed.
Instance SubstHSubstComp_type_term : SubstHSubstComp type term. derive. Qed.

Instance SubstLemmas_term : SubstLemmas term. derive. Qed.

(** ### いくつかの例... *)
(** λa:Bool. a *)
Notation idB :=
  (tm_abs ty_Bool (tm_var 0)).

(** λa:Bool->Bool. a *)
Notation idBB :=
  (tm_abs (ty_arrow ty_Bool ty_Bool) (tm_var 0)).

(** λa:(Bool->Bool)->(Bool->Bool). a *)
Notation idBBBB :=
  (tm_abs (ty_arrow (ty_arrow ty_Bool ty_Bool)
                    (ty_arrow ty_Bool ty_Bool))
          (tm_var 0)).

(** λa:Bool. λb:Bool. a *)
Notation k := (tm_abs ty_Bool (tm_abs ty_Bool (tm_var 0))).

(** (これらを[Definition]ではなく[Notation]とすることで、
    [auto]に扱いやすくしています。) *)

(** ## 操作的意味論 *)
(** ### 値 *)
Inductive value : term -> Prop :=
  | v_abs : forall (T : type) (s : {bind term}),
      value (tm_abs T s)
  | t_true :
      value tm_true
  | t_false :
      value tm_false.
Hint Constructors value.

(** ### 自由変数と置換 *)
(** この節の内容は、Autosubstに依存するため、削除する。
t12 の最初の自由変数をv2で置き換えることを意味する以下は、

    ((λa.t12) v2) = [v2/a]t12

次で表すことができる。

    t12.[beta v2]

de Bruijn Indexなので、t12の中に「最初の自由変数」がなにかが含まれている。
*)

(** ### 簡約 *)

(**
はじめは、Stlc_J.vのST_AppAbsをそのまま、
  | ST_AppAbs : forall T t12 v2,
         value v2 ->
         (tm_app (tm_abs T t12) v2) ==> t12.[beta v2]
としたが、Demo.vの最後の例題が解けなかったので、
Autosubst Demo.v の step_beta に基づく次の定義を使うようにした。

また、Stlc_J.vのST_App2のvalue v1 の前提は削除した。
*)

Inductive step : term -> term -> Prop :=
  | ST_AppAbs : forall T t12 s2 v2,
         s2 = t12.[beta v2] ->
         (tm_app (tm_abs T t12) v2) ==> s2
  | ST_App1 : forall t1 t1' t2,
         t1 ==> t1' ->
         tm_app t1 t2 ==> tm_app t1' t2
  | ST_App2 : forall v1 t2 t2',
         t2 ==> t2' ->
         tm_app v1 t2 ==> tm_app v1  t2'
  | ST_IfTrue : forall t1 t2,
      (tm_if tm_true t1 t2) ==> t1
  | ST_IfFalse : forall t1 t2,
      (tm_if tm_false t1 t2) ==> t2
  | ST_If : forall t1 t1' t2 t3,
      t1 ==> t1' ->
      (tm_if t1 t2 t3) ==> (tm_if t1' t2 t3)
where "t1 '==>' t2" := (step t1 t2).

(**
SfLib の refl_step_closure ではなく Coq標準の rt1n_trans を使うようにする。
Relationを使う前に、rt1n_trans が上書きされていないこと確認する。
 *)
Print clos_refl_trans_1n.
Print rt1n_trans.

Notation stepmany := (clos_refl_trans_1n term step).
Notation "t1 '==>*' t2" := (stepmany t1 t2) (at level 40).

Hint Constructors step.

(** ### Autosubst Demo.v のサンプル
*)
Lemma substitutivity s1 s2 :
  s1 ==> s2 -> forall sigma, s1.[sigma] ==> s2.[sigma].
Proof.
  by elim; intros; autosubst; constructor; trivial; subst; autosubst.
Qed.

Lemma substitutivity' s1 s2 :
  s1 ==> s2 -> forall sigma, s1.[sigma] ==> s2.[sigma].
Proof.
  elim.                                     (* s1 ==> s2 で帰納法 *)
  + move=> T t12 s' v2 Hv2.
    autosubst => sigma.
    Check ST_AppAbs.
    Check ST_AppAbs T (t12.[upn 1 sigma]) (s'.[sigma]) (v2.[sigma]).
    apply (ST_AppAbs T (t12.[upn 1 sigma]) (s'.[sigma]) (v2.[sigma])).
    rewrite Hv2.
    by autosubst.
  + move=> t1 t1' t2 Hs IH sigma.
    autosubst.
    apply ST_App1.
    by [].
  + move=> t1 t1' t2 Hs IH sigma.
    autosubst.
    by apply ST_App2.
  + move=> t1 t2 sigma.
    autosubst.
    by apply ST_IfTrue.
  + move=> t1 t2 sigma.
    autosubst.
    by apply ST_IfFalse.
  + move=> t1 t1' t2 t3 Hs IH sigma.
    apply ST_If.
    by autosubst.
Qed.

(** ### 例 *)
Lemma step_example1 :
  (tm_app idBB idB) ==>* idB.
Proof.
  eapply rt1n_trans.
    apply ST_AppAbs.
    autosubst.                              (* apply v_abs. *)
  simpl.
  apply rt1n_refl.
Qed.

(**
normalize タクティク
http://proofcafe.org/sf/Types_J.html
*)
Tactic Notation "print_goal" := match goal with |- ?x => idtac x end.
Tactic Notation "normalize" :=
   repeat (print_goal; eapply rt1n_trans ;
             [ (eauto 10; fail) | (instantiate; simpl)]);
   apply rt1n_refl.

Lemma step_example1' :
  (tm_app idBB idB) ==>* idB.
Proof.
  normalize.
Qed.

Lemma step_example2 :
  (tm_app idBB (tm_app idBB idB)) ==>* idB.
Proof.
  eapply rt1n_trans.
  + apply ST_App2.
    by auto.
  + eapply rt1n_trans.
    - apply ST_AppAbs. 
      simpl. by auto.
    - simpl.
      by apply rt1n_refl.
Qed.

Lemma step_example2' :
  (tm_app idBB (tm_app idBB idB)) ==>* idB.
Proof.
  normalize.
Qed.

(** autosubst を利用する。
*)
Lemma step_example2'' :
  (tm_app idBB (tm_app idBB idB)) ==>* idB.
Proof.
  eapply rt1n_trans.
  + apply ST_App2.
      apply ST_AppAbs.
      by autosubst.
  + eapply rt1n_trans.
    - autosubst.
      apply ST_AppAbs.
      by autosubst.
    - autosubst.
      by apply rt1n_refl.
Qed.

(** ## 型付け *)
(** ### コンテキスト *)

(** この節の内容は、Autosubstに依存する。*)
(* https://www.ps.uni-saarland.de/autosubst/doc/SystemF.html *)
Definition ctx := seq type.
Local Notation "Gamma `_ i" := (nth (Var 0) Gamma i).
Definition raise (Gamma : ctx) := [seq A.[ren (+1)] | A <- Gamma].

(**
- コンテキストからの取り出しは、Gamma `_ x 。
  あらかじめ、x < size Gamma で取り出せることをテストしておく。
- コンテキストの拡張 extend は、seqのcons。
- 空のコンテキスト empty は、 [::] 。
 *)

Lemma extend_eq : forall (ctxt: ctx) T,
  (T :: ctxt) `_ 0 = T.
Proof.
  by [].
Qed.

(** ### 型付け関係 *)
Inductive has_type : ctx -> term -> type -> Prop :=
  | T_Var : forall (Gamma : ctx) (x : var) (T : type),
      x < size Gamma ->                     (* Some T であるチェックの代わり *)
      Gamma `_ x = T ->                     (* (nth (Var 0) Gamma x) = T *)
      has_type Gamma (tm_var x) T
  | T_Abs : forall Gamma T11 T12 t12,
      has_type (T11 :: Gamma) t12 T12 ->
      has_type Gamma (tm_abs T11 t12) (ty_arrow T11 T12)
  | T_App : forall T11 T12 Gamma t1 t2,
      has_type Gamma t1 (ty_arrow T11 T12) ->
      has_type Gamma t2 T11 ->
      has_type Gamma (tm_app t1 t2) T12
  | T_True : forall Gamma,
       has_type Gamma tm_true ty_Bool
  | T_False : forall Gamma,
       has_type Gamma tm_false ty_Bool
  | T_If : forall t1 t2 t3 T Gamma,
       has_type Gamma t1 ty_Bool ->
       has_type Gamma t2 T ->
       has_type Gamma t3 T ->
       has_type Gamma (tm_if t1 t2 t3) T.
Hint Constructors has_type.

(** ### 例 *)
Example typing_example_1 :
  has_type [::] (tm_abs ty_Bool (tm_var 0)) (ty_arrow ty_Bool ty_Bool).
Proof.
  apply T_Abs; apply T_Var => //=.
Qed.

(** has_typeコンストラクタをヒントデータベースに追加したことから、
    これを auto は直接解くことができることに注意します。*)

Example typing_example_1' :
  has_type [::] (tm_abs ty_Bool (tm_var 0)) (ty_arrow ty_Bool ty_Bool).
Proof.
  auto.
Qed.

(* Hint Unfold beq_id beq_nat extend. *)

Example typing_example_2 :
  has_type [::]
    (tm_abs ty_Bool                         (* a *)
       (tm_abs (ty_arrow ty_Bool ty_Bool)   (* b *)
          (tm_app (tm_var 0) (tm_app (tm_var 0) (tm_var 1)))))
    (ty_arrow ty_Bool (ty_arrow (ty_arrow ty_Bool ty_Bool) ty_Bool)).
Proof with auto using extend_eq.
  apply T_Abs.
  apply T_Abs.
  eapply T_App. apply T_Var...
  eapply T_App. apply T_Var...
  apply T_Var...
Qed.

(**
少し SSReflect 風に書いてみる。
 *)
Example typing_example_2' :
  has_type [::]
    (tm_abs ty_Bool                         (* a *)
       (tm_abs (ty_arrow ty_Bool ty_Bool)   (* b *)
          (tm_app (tm_var 0) (tm_app (tm_var 0) (tm_var 1)))))
    (ty_arrow ty_Bool (ty_arrow (ty_arrow ty_Bool ty_Bool) ty_Bool)).
Proof.
  apply T_Abs.
  apply T_Abs.
  eapply T_App.
(*
  apply (@T_App ty_Bool ty_Bool [:: ty_arrow ty_Bool ty_Bool; ty_Bool]
                (tm_var 0) (tm_app (tm_var 0) (tm_var 1))).
*)
    + by apply T_Var => /=.
    + eapply T_App.
      - by apply T_Var.
      - by apply T_Var.
Qed.

(** #### 練習問題: ★★, optional *)
(** [auto]、[eauto]、[eapply] を使わずに同じ結果を証明しなさい。*)

Example typing_example_2_full :
  has_type [::]
    (tm_abs ty_Bool                         (* a *)
       (tm_abs (ty_arrow ty_Bool ty_Bool)   (* b *)
          (tm_app (tm_var 0) (tm_app (tm_var 0) (tm_var 1)))))
    (ty_arrow ty_Bool (ty_arrow (ty_arrow ty_Bool ty_Bool) ty_Bool)).
Proof.
  apply T_Abs.
  apply T_Abs.
  apply T_App
  with (T11 := ty_Bool)                     (* t1 : T11 -> T12 *)
         (T12 := ty_Bool)                   (* t2 : T11 *)
         (t1 := tm_var 0)
         (t2 := tm_app (tm_var 0) (tm_var 1)).
  by apply T_Var.
  (* Gamma `_ 0 = (ty_arrow ty_Bool ty_Bool) *)

  apply T_App
  with (T11 := ty_Bool)                     (* t1 : T11 -> T12 *)
         (T12 := ty_Bool)                   (* t2 : T11 *)
         (t1 := tm_var 0)
         (t2 := tm_var 1).
  by apply T_Var.
  (* Gamma `_ 0 = (ty_arrow ty_Bool ty_Bool) *)

  by apply T_Var.
  (* Gamma `_ 1 = ty_Bool *)
Qed.
(** [] *)

(** #### 練習問題: ★★ (typing_example_3) *)
(** 次の型付けが成立することを形式的に証明しなさい:
*)
Example typing_example_3 :
  exists T,
    has_type [::]
      (tm_abs (ty_arrow ty_Bool ty_Bool)    (* a *)
         (tm_abs (ty_arrow ty_Bool ty_Bool) (* b *)
            (tm_abs ty_Bool                 (* c *)
               (tm_app (tm_var 1) (tm_app (tm_var 2) (tm_var 0))))))
      T.

Proof.
  exists
    (ty_arrow
       (ty_arrow ty_Bool ty_Bool)           (* a *)
       (ty_arrow
          (ty_arrow ty_Bool ty_Bool)        (* b *)
          (ty_arrow
             ty_Bool                        (* c *)
             ty_Bool))).                    (* 値：b (a c) *)
  eapply T_Abs.
  eapply T_Abs.
  eapply T_Abs.
  eapply T_App.
  + by apply T_Var...
  + eapply T_App.
    - by apply T_Var...
    - by apply T_Var.
Qed.
(** [] *)

(** 項が「型付けできない」ことを証明することもできます。
    例えば [\a:Bool. \b:Bool, a b] に型をつける型付けが存在しないこと、
    を形式的にチェックしましょう。
*)
Example typing_nonexample_1 :
  ~ exists T,
      has_type [::]
        (tm_abs ty_Bool                     (* a *)
            (tm_abs ty_Bool                 (* b *)
               (tm_app (tm_var 1) (tm_var 0))))
        T.
Proof.
  elim => x H.
  inversion H. subst. clear H.
  inversion H4. subst. clear H4.
  inversion H3. subst. clear H3.
  inversion H2. subst. clear H2.
  inversion H5. subst. clear H5.
  inversion H3.
Qed.

(** #### 練習問題: ★★★ (typing_nonexample_3) *)
(** 別の型を持たない例:
*)

Example typing_nonexample_3 :
  ~ (exists S, exists T,
        has_type [::]
          (tm_abs S
             (tm_app (tm_var 0) (tm_var 0)))
          T).
Proof.
  elim=> x H.
  inversion H. subst. clear H.
  inversion H0. subst. clear H0.
  inversion H4. subst. clear H4.
  inversion H5. subst. clear H5.
  inversion H2. subst. clear H2.
  simpl in H4.
  (* H1 : T11 = ty_arrow T11 T12 *)
(*
 inversion H1.
  (* H1 : ty_Bool = ty_arrow ty_Bool T12 *)
 inversion H1.
  (* H1 : ty_arrow T11_1 T11_2 = ty_arrow (ty_arrow T11_1 T11_2) T12 *)
  apply IHT11_1.
  (* Goal : T11_1 = ty_arrow T11_1 T12 *)
  inversion H1.
  rewrite H2 in H0.
  rewrite H0 at 1.
  reflexivity.
*)
Admitted.
(** [] *)

(** ## 性質 *)
(** ### 自由な出現 *)
(** ### 置換 *)

Lemma substitution_preserves_typing : forall Gamma U v t T,
     has_type (U :: Gamma) t T ->
     has_type [::] v U   ->
     has_type Gamma t.[beta v] T.
Proof.
  move=> Gamma U v t.
  elim: v Gamma.
  + move=> x Gamma T H1 H2.
    autosubst.
    admit.
(*
  intros Gamma U v t T Ht Hv.
  generalize dependent Gamma. generalize dependent T.
  induction t; intros T' Gamma H.
*)
Qed.

(** ### 保存 *)
Theorem preservation : forall t t' T,
     has_type [::] t T  ->
     t ==> t'  ->
     has_type [::] t' T.
Proof with eauto.
  remember [::] as Gamma.
  intros t t' T HT. generalize dependent t'.
  induction HT.
  +  intros t' HE; subst; subst.
     inversion HE; subst; auto.
  +  intros t' HE; subst; subst.
     inversion HE; subst; auto.
  +  intros t' HE; subst; subst.
     inversion HE; subst...
     apply substitution_preserves_typing with T11.
       * inversion HT1; subst; auto.
       * apply HT2.
  +  intros t' HE; subst; subst;
     inversion HE; subst; auto.
  +  intros t' HE; subst; subst;
     inversion HE; subst; auto.
  +  intros t' HE; subst; subst;
     inversion HE; subst; auto.
Qed.

(* SSReflect風の証明：まだできていない。 *)
Theorem preservation' : forall t t' T,
     has_type [::] t T  ->
     t ==> t'  ->
     has_type [::] t' T.
Proof with eauto.
  move=> t t' T HT.
  elim: HT t'.
  (* T_Var *)
  +  move=> Gamma x T0 H H0. move=> t' HE.
     by inversion HE.
  (* T_Abs *)
  +  move=> Gamma' T11 T12 t12 H0. move=> t' t'0 HE.
     subst.
     by inversion HE.
  (* T_App *)
  +  move=> T11 T12 Gamma' t1 t2 HT1 IHT1 HT2 IHT2 t' HE.
     inversion HE; subst.
     (* ST_AppAbs *)
     - apply substitution_preserves_typing with T11.
       * by inversion HT1; subst; auto; admit.
       * by admit.
     (* ST_App1 *)
     - inversion HE; subst.
       * by admit.
       * by admit.
       * by admit.
     (* ST_App2 *)
     - inversion HE; subst.
       * by admit.
       * by admit.
       * by admit.
  (* T_True  *)
  +  move=> Gamma t' HE.
     by inversion HE.
  (* T_False *)
  +  move=> Gamma t' HE.
     by inversion HE.
  (* T_If *)
  +  move=> t1 t2 t3 T0 Gamma HT1 IHT1 HT2 IHT2 HT3 IHT3 t' HE.
     by inversion HE; subst; auto.
Qed.

(* END *)
