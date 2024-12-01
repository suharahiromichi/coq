(**
騎士と悪党のパズル

https://lean-ja.github.io/lean-by-example/Tutorial/Exercise/KnightAndKnave.html

https://philosophy.hku.hk/think/logic/knights.php
 *)
From mathcomp Require Import all_ssreflect.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section knight_and_knave.
  (** その島の住民を表す型 *)
  Variable Islander : finType.
  Variable Knight : pred Islander.
  
  Definition islander := [set: Islander].   (* 全集合 *)
  
  (** Islander の部分集合として定義した騎士の全体 *)
  Definition knight := [set x in islander | Knight x].
  Check knight \subset islander.
  
  (** Islander の部分集合として定義した悪党の全体 *)
  Definition knave := [set x in islander | ~~ Knight x].
  Check knave \subset islander.
  
  (** 人は騎士か悪党のどちらか *)
  Lemma knight_or_knave (p : Islander) : (p \in knight) || (p \in knave).
  Proof.
    rewrite !inE.
    by case: (Knight p).
  Qed.
  
  (** 人が騎士かつ悪党であることはない *)
  Lemma knight_ne_knave (p : Islander) : ~~((p \in knight) && (p \in knave)).
  Proof.
    rewrite !inE.
    by case: (Knight p).
  Qed.
  
  (** 騎士でないことと悪党であることは同値 *)
  Lemma of_not_knight {p : Islander} : (p \notin knight) = (p \in knave).
  Proof.
    rewrite !inE.
    by case: (Knight p).
  Qed.
  
  (** 悪党でないことと騎士であることは同値 *)
  Lemma of_not_knave {p : Islander} : (p \notin knave) = (p \in knight).
  Proof.
    rewrite !inE.
    by case: (Knight p).
  Qed.

(**
これでゾーイとメルが島民であり、騎士か悪党かのどちらかであるということは次のように表現できます。
 *)
  (** ゾーイ *)
  Variable zoey : Islander.
  (** メル *)
  Variable mel : Islander.

  Goal zoey \in islander.
  Proof. done. Qed.
  
  Goal mel \in islander.
  Proof. done. Qed.

(**
正直者であるとか嘘つきであるということを表現するために、
誰がなんと発言したかを表現するための関数を用意します。
その上で、それぞれの発言を愚直に形式化していきます。
 *)
  (** p さんが body という命題を話したという事実を表す命題 *)
  Variable islander_say : Islander -> bool -> bool.
  
  (** 騎士の発言内容はすべて真実 *)
  Axiom statement_of_knight
    : forall (p : Islander) (h : p \in knight) (say : bool), islander_say p say = say.

  (** 悪党の発言内容はすべて偽 *)
  Axiom statement_of_knave
    : forall (p : Islander) (h : p \in knave) (say : bool), islander_say p say = ~~say.

  (** ゾーイは「メルは悪党だ」と言った *)
  Axiom zoey_says : islander_say zoey (mel \in knave).

  (** メルは「ゾーイもメルも悪党ではない」と言った *)
  Axiom mel_says : islander_say mel ((zoey \notin knave) && (mel \notin knave)).

  (**`p` が騎士か悪党のどちらなのか知っていることを表す型 *)
  Inductive Solution (p : Islander) : Type :=
  | isKnight : p \in knight -> Solution p
  | isKnave  : p \in knave  -> Solution p.


  Lemma zoey_is_not_knave : zoey \notin knave.
  Proof.
    apply/negP.
    move=> zoey_is_knave.             (* ゾーイが悪党だと仮定する。 *)
    
    (* ゾーイの発言は偽なので、メルは悪党ではない *)
    have mel_is_knight : mel \in knight.
    {
      have H := statement_of_knave zoey_is_knave (mel \in knave).
      by rewrite -of_not_knave -H zoey_says.
    }.
    
    (** メルが騎士なので、メルの発言は真 *)
    have mel_says_truth := statement_of_knight mel_is_knight ((zoey \notin knave) && (mel \notin knave)).
    rewrite mel_says in mel_says_truth.
    rewrite zoey_is_knave in mel_says_truth.
    rewrite of_not_knave in mel_says_truth.
    rewrite mel_is_knight in mel_says_truth.
    simpl in mel_says_truth.
    done.
  Qed.

/-- ゾーイは騎士である -/
theorem zoey_is_knight : knight zoey := by
  have := zoey_is_not_knave
  simpa using this

/-- メルは悪党 -/
theorem mel_is_knave : knave mel := by
  -- ゾーイは騎士なのでゾーイの発言は真であり、
  -- よってメルは悪党
  exact statement_of_knight zoey_is_knight zoey_says
--##--

/-- ゾーイは騎士か悪党か？-/
noncomputable def zoey_which : Solution zoey := by
  -- sorry
  apply Solution.isKnight
  exact zoey_is_knight
  -- sorry

/-- メルは騎士か悪党か？-/
noncomputable def mel_which : Solution mel := by
  -- sorry
  apply Solution.isKnave
  exact mel_is_knave
  -- sorry

--#--
section
/- ## 選択原理を使用していないことを確認するコマンド -/

open Lean Elab Command

elab "#detect_classical " id:ident : command => do
  -- 識別子(ident)を Name に変換
  let constName ← liftCoreM <| realizeGlobalConstNoOverload id

  -- 依存する公理を取得
  let axioms ← collectAxioms constName

  -- 依存公理がなかったときの処理
  if axioms.isEmpty then
    logInfo m!"'{constName}' does not depend on any axioms"
    return ()

  -- Classical で始まる公理があるかどうかチェック
  -- もしあればエラーにする
  let caxes := axioms.filter fun nm => Name.isPrefixOf `Classical nm
  if caxes.isEmpty then
    logInfo m!"'{constName}' is non-classical and depends on axioms: {axioms.toList}"
  else
    throwError m!"'{constName}' depends on classical axioms: {caxes.toList}"

end





  Goal (zoey \in knight).
  Proof.
    move: statement_of_knight zoey => H z.


  Axiom zoey_knight : zoey \in knight.
  Axiom zoey_knave : zoey \in knave.
  Axiom mel_knight : mel \in knight.
  Axiom mel_knave : mel \in knave.

  Check @statement_of_knight zoey zoey_knight (zoey \in knight)
    : islander_say zoey (zoey \in knight).
  
  Check @statement_of_knight mel mel_knight ((zoey \notin knave) && (mel \notin knave))
    : islander_say mel ((zoey \notin knave) && (mel \notin knave)).

  Check @statement_of_knave mel mel_knave (zoey \in knight)
    : ~~ islander_say mel (zoey \in knight).

  Check @statement_of_knave zoey zoey_knave ((zoey \notin knave) && (mel \notin knave))
    : ~~ islander_say zoey ((zoey \notin knave) && (mel \notin knave)).
  
  Lemma zoey_which : zoey \in knight.
  Proof.
    
