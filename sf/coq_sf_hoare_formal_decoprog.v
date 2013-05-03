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
(* ####################################################### *)
(* * Formalizing Decorated Programs *)
(** * 修飾付きプログラムの形式化 *)

(* The informal conventions for decorated programs amount to a way of
    displaying Hoare triples in which commands are annotated with
    enough embedded assertions that checking the validity of the
    triple is reduced to simple algebraic calculations showing that
    some assertions were stronger than others.

    In this section, we show that this informal presentation style can
    actually be made completely formal.  *)
(** ホーアの三つ組を、非形式的な修飾付きプログラムで記述することは結局、
    コマンドに十分な表明を付加することで、三つ組の正しさをチェックすることを、
    ある表明が別のものより強いことを示す簡単な代数的計算に簡約化することになります。

    この節では、この非形式的なスタイルを、実際は完全に形式的に表現できることを示します。*)

(* ** Syntax *)
(** ** 構文 *)

(* The first thing we need to do is to formalize a variant of the
    syntax of commands that includes embedded assertions.  We call the
    new commands _decorated commands_, or [dcom]s. *)
(** 最初にしなければならないことは、表明を埋め込んだコマンド構文を形式化することです。
    この形のコマンドを修飾付きコマンド(_decorated commands_)または[dcom]と呼びます。*)


Inductive dcom : Type :=
  | DCSkip :  Assertion -> dcom
  | DCSeq : dcom -> dcom -> dcom
  | DCAsgn : id -> aexp ->  Assertion -> dcom
  | DCIf : bexp ->  Assertion -> dcom ->  Assertion -> dcom -> dcom
  | DCWhile : bexp -> Assertion -> dcom -> Assertion -> dcom
  | DCPre : Assertion -> dcom -> dcom
  | DCPost : dcom -> Assertion -> dcom.

Tactic Notation "dcom_cases" tactic(first) ident(c) :=
  first;
  [ Case_aux c "Skip" | Case_aux c "Seq" | Case_aux c "Asgn"
  | Case_aux c "If" | Case_aux c "While"
  | Case_aux c "Pre" | Case_aux c "Post" ].

Notation "'SKIP' {{ P }}"
      := (DCSkip P)
      (at level 10) : dcom_scope.
Notation "l '::=' a {{ P }}"
      := (DCAsgn l a P)
      (at level 60, a at next level) : dcom_scope.
Notation "'WHILE' b 'DO' {{ Pbody }} d 'END' {{ Ppost }}"
      := (DCWhile b Pbody d Ppost)
      (at level 80, right associativity) : dcom_scope.
Notation "'IFB' b 'THEN' {{ P }} d 'ELSE' {{ P' }} d' 'FI'"
      := (DCIf b P d P' d')
      (at level 80, right associativity)  : dcom_scope.
Notation "'=>' {{ P }} d"
      := (DCPre P d)
      (at level 90, right associativity)  : dcom_scope.
Notation "{{ P }} d"
      := (DCPre P d)
      (at level 90)  : dcom_scope.
Notation "d '=>' {{ P }}"
      := (DCPost d P)
      (at level 91, right associativity)  : dcom_scope.
Notation " d ; d' "
      := (DCSeq d d')
      (at level 80, right associativity)  : dcom_scope.

Delimit Scope dcom_scope with dcom.

(* To avoid clashing with the existing [Notation] definitions
    for ordinary [com]mands, we introduce these notations in a special
    scope called [dcom_scope], and we wrap examples with the
    declaration [% dcom] to signal that we want the notations to be
    interpreted in this scope.

    Careful readers will note that we've defined two notations for the
    [DCPre] constructor, one with and one without a [=>].  The
    "without" version is intended to be used to supply the initial
    precondition at the very top of the program. *)
(** 既に定義されているコマンド[com]の記法[Notation]との衝突を避けるため、
    [dcom_scope]という特別なスコープを導入します。
    そして、例を宣言[% dcom]で包み、記法をこのスコープ内で解釈したいことを表します。

    注意深い読者は、[DCPre]コンストラクタに対して2つの記法を定義していることに気付くでしょう。
    [=>]を使うものと使わないものです。[=>]を使わないものは、
    プログラムの一番最初の事前条件を与える意図で用意したものです。*)

Example dec_while : dcom := (
    {{ fun st => True }}
  WHILE (BNot (BEq (AId X) (ANum 0)))
  DO
       {{ fun st => ~(asnat (st X) = 0) }}
      X ::= (AMinus (AId X) (ANum 1))
       {{ fun _ => True }}
  END
    {{ fun st => asnat (st X) = 0 }}
) % dcom.

(* It is easy to go from a [dcom] to a [com] by erasing all
    annotations. *)
(** [dcom]から[com]に変換するのは簡単です。アノテーションをすべて消せば良いのです。*)

Fixpoint extract (d:dcom) : com :=
  match d with
  | DCSkip _          => SKIP
  | DCSeq d1 d2       => (extract d1 ; extract d2)
  | DCAsgn V a _      => V ::= a
  | DCIf b _ d1 _ d2  => IFB b THEN extract d1 ELSE extract d2 FI
  | DCWhile b _ d _   => WHILE b DO extract d END
  | DCPre _ d         => extract d
  | DCPost d _        => extract d
  end.

(* The choice of exactly where to put assertions in the definition of
    [dcom] is a bit subtle.  The simplest thing to do would be to
    annotate every [dcom] with a precondition and postcondition.  But
    this would result in very verbose programs with a lot of repeated
    annotations: for example, a program like [SKIP;SKIP] would have to
    be annotated as
[[
        {{P}} ({{P}} SKIP {{P}}) ; ({{P}} SKIP {{P}}) {{P}},
]]
    with pre- and post-conditions on each [SKIP], plus identical pre-
    and post-conditions on the semicolon!

    Instead, the rule we've followed is this:

       - The _post_-condition expected by each [dcom] [d] is embedded in [d]

       - The _pre_-condition is supplied by the context. *)
(** [dcom]の定義のどこに表明を置くかの選択は、ちょっと微妙です。
    一番簡単な方法は、すべての[dcom]に事前条件と事後条件の表明を付けてしまうことかもしれません。
    しかしそうすると、同じアノテーションが繰替えされて、とてもうるさいプログラムになってしまうでしょう。
    例えば、[SKIP;SKIP]は次のように表明が付加されることになります。
[[
        {{P}} ({{P}} SKIP {{P}}) ; ({{P}} SKIP {{P}}) {{P}},
]]
    それぞれの[SKIP]の事前条件、事後条件と、さらにセミコロンの事前条件、
    事後条件として同じものが付加されています!

    この代わりに、次の規則に従うことにします:

       - [dcom] [d]に対する事後条件は[d]に埋め込む

       - 事前条件はコンテキストから与えられるようにする。 *)

(* In other words, the invariant of the representation is that a
    [dcom] [d] together with a precondition [P] determines a Hoare
    triple [{{P}} (extract d) {{post d}}], where [post] is defined as
    follows: *)
(** 言い換えると、この表現での不変条件は、
    [dcom] [d] と事前条件 [P] がホーアの三つ組[{{P}} (extract d) {{post d}}]
    を決定するということです。ここで [post] は次のように定義されます: *)

Fixpoint post (d:dcom) : Assertion :=
  match d with
  | DCSkip P                => P
  | DCSeq d1 d2             => post d2
  | DCAsgn V a Q            => Q
  | DCIf  _ _ d1 _ d2       => post d1
  | DCWhile b Pbody c Ppost => Ppost
  | DCPre _ d               => post d
  | DCPost c Q              => Q
  end.

(* We can define a similar function that extracts the "initial
    precondition" from a decorated program. *)
(** 修飾付きプログラムから「最初の事前条件」を抽出する同様の関数が定義できます。*)

Fixpoint pre (d:dcom) : Assertion :=
  match d with
  | DCSkip P                => fun st => True
  | DCSeq c1 c2             => pre c1
  | DCAsgn V a Q            => fun st => True
  | DCIf  _ _ t _ e         => fun st => True
  | DCWhile b Pbody c Ppost => fun st => True
  | DCPre P c               => P
  | DCPost c Q              => pre c
  end.

(* This function is not doing anything sophisticated like calculating
    a weakest precondition; it just recursively searches for an
    explicit annotation at the very beginning of the program,
    returning default answers for programs that lack an explicit
    precondition (like a bare assignment or [SKIP]).

    Using [pre] and [post], and assuming that we adopt the convention
    of always supplying an explicit precondition annotation at the
    very beginning of our decorated programs, we can express what it
    means for a decorated program to be correct as follows: *)
(** この関数は、最弱事前条件を計算する、というような洗練されたことは何もしません。
    単に、プログラムの一番最初から明示的に付加されたアノテーションを再帰的に探します。
    もし(代入だけのものや[SKIP]のように)明示的事前条件を持たない場合には、
    デフォルトの答えを返します。

    [pre]と[post]を使い、
    修飾付きプログラムの一番最初には常に明示的な事前条件のアノテーションを付ける慣習を守ることを仮定すると、
    修飾付きプログラムが正しいとはどういうことかを以下のように表現できます: *)

Definition dec_correct (d:dcom) :=
  {{pre d}} (extract d) {{post d}}.

(* To check whether this Hoare triple is _valid_, we need a way to
    extract the "proof obligations" from a decorated program.  These
    obligations are often called _verification conditions_, because
    they are the facts that must be verified (by some process looking
    at the decorated program) to see that the decorations are
    logically consistent and thus add up to a proof of correctness. *)
(** このホーアの三つ組が正しい(_valid_)かどうかをチェックするには、
    修飾付きプログラムから「証明課題」("proof obligations")を抽出することが必要となります。
    この課題は、しばしば検証条件(_verification conditions_)と呼ばれます。
    なぜなら、修飾が論理的に整合していて、
    全体として正しさの証明になることを確認するために
    (修飾付きプログラムを調べるプロセスによって)検証されるべき事実だからです。*)

(* ** Extracting Verification Conditions *)
(** ** 検証条件の抽出 *)

(* First, a bit of notation: *)
(** 最初に、記法について少々: *)

Definition assert_implies (P Q : Assertion) : Prop :=
  forall st, P st -> Q st.

(* We will write [P ~~> Q] (in ASCII, [P ~][~> Q]) for [assert_implies
    P Q]. *)
(** [assert_implies P Q]を[P ~~> Q] (ASCIIでは, [P ~][~> Q])と書きます。*)

Notation "P ~~> Q" := (assert_implies P Q) (at level 80).
Notation "P <~~> Q" := (P ~~> Q /\ Q ~~> P) (at level 80).

(* Next, the key definition.  The function [verification_conditions]
    takes a [dcom] [d] together with a precondition [P] and returns a
    _proposition_ that, if it can be proved, implies that the triple
    [{{P}} (extract d) {{post d}}] is valid.  It does this by walking
    over [d] and generating a big conjunction including all the "local
    checks" that we listed when we described the informal rules for
    decorated programs.  (Strictly speaking, we need to massage the
    informal rules a little bit to add some uses of the rule of
    consequence, but the correspondence should be clear.) *)
(** 次に、主要な定義です。
    関数[verification_conditions]は[dcom] [d]と事前条件[P]をとり、
    命題(_proposition_)を返します。
    その命題は、もし証明できたならば、
    三つ組[{{P}} (extract d) {{post d}}]が正しいことになります。
    この関数はその命題を作るために、[d]を調べまわって、
    すべてのローカルチェックの /\ (and)をとります。
    ローカルチェックとは、
    前に修飾付きプログラムについての非形式的規則のところでリストアップしたもののことです。
    (厳密に言うと、帰結規則の使用法を拡げるために非形式的規則をちょっと揉んでやる必要があります。
    ただ、対応関係は明確でしょう。) *)

Fixpoint verification_conditions (P : Assertion) (d:dcom) : Prop :=
  match d with
  | DCSkip Q          =>
      (P ~~> Q)
  | DCSeq d1 d2      =>
      verification_conditions P d1
      /\ verification_conditions (post d1) d2
  | DCAsgn V a Q      =>
      (P ~~> assn_sub V a Q)
  | DCIf b P1 t P2 e  =>
      ((fun st => P st /\ bassn b st) ~~> P1)
      /\ ((fun st => P st /\ ~ (bassn b st)) ~~> P2)
      /\ (post t = post e)
      /\ verification_conditions P1 t
      /\ verification_conditions P2 e
  | DCWhile b Pbody d Ppost      =>
      (* post d is the loop invariant and the initial precondition *)
      (P ~~> post d)
      /\ ((fun st => post d st /\ bassn b st) <~~> Pbody)
      /\ ((fun st => post d st /\ ~(bassn b st)) <~~> Ppost)
      /\ verification_conditions (fun st => post d st /\ bassn b st) d
  | DCPre P' d         =>
      (P ~~> P') /\ verification_conditions P' d
  | DCPost d Q        =>
      verification_conditions P d /\ (post d ~~> Q)
  end.

(* And now, the key theorem, which captures the claim that the
    [verification_conditions] function does its job correctly.  Not
    surprisingly, we need all of the Hoare Logic rules in the
    proof. *)
(** そしてついに、主定理です。この定理は、
    [verification_conditions]関数が正しくはたらくことを主張します。
    当然ながら、その証明にはホーア論理のすべての規則が必要となります。*)
(* We have used _in_ variants of several tactics before to
    apply them to values in the context rather than the goal. An
    extension of this idea is the syntax [tactic in *], which applies
    [tactic] in the goal and every hypothesis in the context.  We most
    commonly use this facility in conjunction with the [simpl] tactic,
    as below. *)
(** これまで、いろいろなタクティックについて、
    ゴールではなくコンテキストの値に適用する別形を使ってきました。
    このアイデアの拡張が構文[tactic in *]です。
    この構文では、[tactic]をゴールとコンテキストのすべての仮定とに適用します。
    このしくみは、下記のように[simpl]タクティックと組み合わせて使うのが普通です。*)

Theorem verification_correct : forall d P,
  verification_conditions P d -> {{P}} (extract d) {{post d}}.
Proof.
  dcom_cases (induction d) Case; intros P H; simpl in *.
  Case "Skip".
    eapply hoare_consequence_pre.
      apply hoare_skip.
      assumption.
  Case "Seq".
    inversion H as [H1 H2]. clear H.
    eapply hoare_seq.
      apply IHd2. apply H2.
      apply IHd1. apply H1.
  Case "Asgn".
    eapply hoare_consequence_pre.
      apply hoare_asgn.
      assumption.
  Case "If".
    inversion H as [HPre1 [HPre2 [HQeq [HThen HElse]]]]; clear H.
    apply hoare_if.
      eapply hoare_consequence_pre. apply IHd1. apply HThen. assumption.
      simpl. rewrite HQeq.
      eapply hoare_consequence_pre. apply IHd2. apply HElse. assumption.
  Case "While".
    rename a into Pbody. rename a0 into Ppost.
    inversion H as [Hpre [Hbody [Hpost Hd]]]; clear H.
    eapply hoare_consequence.
    apply hoare_while with (P := post d).
      apply IHd. apply Hd.
      assumption. apply Hpost.
  Case "Pre".
    inversion H as [HP Hd]; clear H.
    eapply hoare_consequence_pre. apply IHd. apply Hd. assumption.
  Case "Post".
    inversion H as [Hd HQ]; clear H.
    eapply hoare_consequence_post. apply IHd. apply Hd. assumption.
Qed.

(* ** Examples *)
(** ** 例 *)

(* The propositions generated by [verification_conditions] are fairly
    big, and they contain many conjuncts that are essentially trivial. *)
(** [verification_conditions]が生成する命題はかなり大きく、
    /\ でつながれた命題の中には本質的に自明なものも多く含まれます。*)

Eval simpl in (verification_conditions (fun st => True) dec_while).
(* ====>
    ((fun _ : state => True) ~~> (fun _ : state => True)) /\
    ((fun _ : state => True) ~~> (fun _ : state => True)) /\
    ((fun st : state => True /\ bassn (BNot (BEq (AId X) (ANum 0))) st)
     <~~> (fun st : state => asnat (st X) <> 0)) /\
    ((fun st : state => True /\ ~ bassn (BNot (BEq (AId X) (ANum 0))) st)
     <~~> (fun st : state => asnat (st X) = 0)) /\
    (fun st : state => True /\ bassn (BNot (BEq (AId X) (ANum 0))) st)
     ~~> assn_sub X (AMinus (AId X) (ANum 1)) (fun _ : state => True) *)

(* We can certainly work with them using just the tactics we have so
    far, but we can make things much smoother with a bit of
    automation.  We first define a custom [verify] tactic that applies
    splitting repeatedly to turn all the conjunctions into separate
    subgoals and then uses [omega] and [eauto] (a handy
    general-purpose automation tactic that we'll discuss in detail
    later) to deal with as many of them as possible. *)
(** ここまで見てきたタクティックだけを使うことでこれらの命題の証明を進めることは確かにできるのですが、
    いくらか自動化を入れることで、よりスムーズに進められるようにできます。
    最初に自前のタクティック[verify]を定義します。
    このタクティックは、split を繰り返し適用して/\でつながれた命題を個々のサブゴールに分割し、
    その後[omega]と[eauto](便利な一般用途のタクティック。後に詳しく議論します)
    を適用可能な限り使います。*)

Tactic Notation "verify" :=
  try apply verification_correct;
  repeat split;
  simpl; unfold assert_implies;
  unfold bassn in *; unfold beval in *; unfold aeval in *;
  unfold assn_sub; simpl in *;
  intros;
  repeat match goal with [H : _ /\ _ |- _] => destruct H end;
  try eauto; try omega.

(* What's left after [verify] does its thing is "just the interesting
    parts" of checking that the decorations are correct.  For example: *)
(** [verify]適用後残るのは、修飾の正しさをチェックするのに「興味深い部分だけ」です。
    例えば: *)

Theorem dec_while_correct :
  dec_correct dec_while.
Proof.
  verify; destruct (asnat (st X)).
    inversion H0.
    unfold not. intros. inversion H1.
    apply ex_falso_quodlibet. apply H. reflexivity.
    reflexivity.
    reflexivity.
    apply ex_falso_quodlibet. apply H0. reflexivity.
    unfold not. intros. inversion H0.
    inversion H.
Qed.

(* Another example (formalizing a decorated program we've seen
    before): *)
(** 別の例(前に見た修飾付きプログラムを形式化したもの)です: *)

Example subtract_slowly_dec (x:nat) (z:nat) : dcom := (
    {{ fun st => asnat (st X) = x /\ asnat (st Z) = z }}
  WHILE BNot (BEq (AId X) (ANum 0))
  DO   {{ fun st => asnat (st Z) - asnat (st X) = z - x
                 /\ bassn (BNot (BEq (AId X) (ANum 0))) st }}
     Z ::= AMinus (AId Z) (ANum 1)
       {{ fun st => asnat (st Z) - (asnat (st X) - 1) = z - x }} ;
     X ::= AMinus (AId X) (ANum 1)
       {{ fun st => asnat (st Z) - asnat (st X) = z - x }}
  END
    {{ fun st =>   asnat (st Z)
                 - asnat (st X)
                 = z - x
              /\ ~ bassn (BNot (BEq (AId X) (ANum 0))) st }}
    =>
    {{ fun st => asnat (st Z) = z - x }}
) % dcom.

Theorem subtract_slowly_dec_correct : forall x z,
  dec_correct (subtract_slowly_dec x z).
Proof.
  intros. verify.
    rewrite <- H.
    assert (H1: update st Z (VNat (asnat (st Z) - 1)) X = st X).
      apply update_neq. reflexivity.
    rewrite -> H1. destruct (asnat (st X)) as [| X'].
      inversion H0. simpl. rewrite <- minus_n_O. omega.
    destruct (asnat (st X)).
      omega.
      apply ex_falso_quodlibet. apply H0. reflexivity.
Qed.

(* ####################################################### *)
(* ####################################################### *)
(* ####################################################### *)
(* **** Exercise: 3 stars (slow_assignment_dec) *)
(** **** 練習問題: ★★★ (slow_assignment_dec) *)

(* A roundabout way of assigning a number currently stored in [X] to
   the variable [Y] is to start [Y] at [0], then decrement [X] until it
   hits [0], incrementing [Y] at each step.

   Here is an informal decorated program that implements this idea
   given a parameter [x]: *)
(** [X]に現在設定されている値を変数[Y]に代入する遠回りの方法は、
    [Y]を[0]から始め、
    [X]を[0]になるまで減らしていきながら、その各ステップで[Y]を増やしていくことです。

   次が、
   このアイデアを[x]をパラメータとする非形式的な修飾付きプログラムで表したものです: *)

(**
[[
      {{ True }}
    X ::= x
      {{ X = x }} ;
    Y ::= 0
      {{ X = x /\ Y = 0 }} ;
    WHILE X <> 0 DO
        {{ X + Y = x /\ X > 0 }}
      X ::= X - 1
        {{ Y + X + 1 = x }} ;
      Y ::= Y + 1
        {{ Y + X = x }}
    END
      {{ Y = x /\ X = 0 }}
]]
*)

(* Write a corresponding function that returns a value of type [dcom]
    and prove it correct. *)
(** 対応する[dcom]型の値を返す関数を記述し、その正しさを証明しなさい。*)

Example slow_assignment_dec (x:nat) : dcom := (
  {{ fun st => True }} (* => {{ fun st => x = x }} *)
  X ::= (ANum x)
  {{ fun st => asnat (st X) = x }};
  Y ::= (ANum 0)
  {{ fun st => asnat (st X) = x /\ asnat (st Y) = 0 }};
  WHILE (BNot (BEq (AId X) (ANum 0))) DO
    {{ fun st => asnat (st X) + asnat (st Y) = x /\ asnat (st X) <> 0 }} (* ループ不変式かつループ実行条件 *)
    X ::= AMinus (AId X) (ANum 1)
    {{ fun st => asnat (st X) + (asnat (st Y) + 1) = x }};
    Y ::= APlus (AId Y) (ANum 1)
    {{ fun st => asnat (st X) + asnat (st Y) = x }} (* ループ不変式 *)
  END
  {{ fun st => asnat (st Y) + asnat (st X) = x /\ asnat (st X) = 0 }} (* ループ不変式かつループ終了条件 *)
) % dcom.
(* 修飾のなかの (>0)や(=0)を、IMPの式で書いてbassnを通してもよい。 *)

Example slow_assignment_dec' (x:nat) : dcom := (
  {{ fun st => True }}  => {{ fun st => x = x }} 
  X ::= (ANum x)
  {{ fun st => asnat (st X) = x }};
  Y ::= (ANum 0)
  {{ fun st => asnat (st X) = x /\ asnat (st Y) = 0 }}
  => {{ fun st => asnat (st X) + asnat (st Y) = x }};  (* ループ不変式 *)
  WHILE (BNot (BEq (AId X) (ANum 0))) DO
    {{ fun st => asnat (st X) + asnat (st Y) = x /\ asnat (st X) <> 0 }} (* ループ不変式かつループ実行条件 *)
    => {{ fun st => (asnat (st X) - 1) + (asnat (st Y) + 1) = x }} 
    X ::= AMinus (AId X) (ANum 1)
    {{ fun st => asnat (st X) + (asnat (st Y) + 1) = x }};
    Y ::= APlus (AId Y) (ANum 1)
    {{ fun st => asnat (st X) + asnat (st Y) = x }}  (* ループ不変式 *)
  END
  {{ fun st => asnat (st Y) + asnat (st X) = x /\ asnat (st X) = 0 }}  (* ループ不変式かつループ終了条件 *)
  => {{ fun st => asnat (st Y) = x }}
) % dcom.

(* 補題：coq_sf_hoare.v と同じ。 *)
Lemma negb_not_true_iff : forall b, negb b <> true <-> b = true.
Proof.
  intros b.
  split.
  intros H.
  destruct b.
  Case "b = true".
    reflexivity.
  Case "b = false".
    apply ex_falso_quodlibet.
    apply H. unfold negb. reflexivity.
  intros H.
  rewrite H. simpl.
  unfold not.
  intros. inversion H0.
Qed.

Lemma x_plus_y__x_m1_plus_y_p1 : forall x y,
             x <> 0 -> x + y = (x - 1) + (y + 1).
Proof.
  intros x y H.
  induction x as [| x'].
  Case "x = 0".
    apply ex_falso_quodlibet.               (* 単にomegaでもよい *)
    apply H. reflexivity.
  Case "x = Sx'".
    omega.
Qed.

Theorem slow_assignment_dec_correct : forall x,
  dec_correct (slow_assignment_dec x).
Proof.
  intros x.
  verify.
  (* 
     X + Y = x -> ~(X = 0) = true -> X <> 0
     *)
  apply beq_nat_false_iff.
  apply negb_true_iff.
  apply H0.

  (* 
     X + Y = x -> X <> 0 -> ~(X = 0)
     *)
  apply negb_true_iff.
  apply not_eq_beq_false.
  apply H0.

  (*
     X + Y = x -> ~(X = 0) <> true -> X = 0
     *)
  apply beq_nat_true_iff.
  apply negb_not_true_iff.
  apply H0.

  (*
     X + Y = x -> X = 0 -> ~(X = 0) <> true
     *)
  apply negb_not_true_iff.
  apply beq_nat_true_iff.
  apply H0.

  (*
     X + Y = x -> ~(X = 0) = true -> (X - 1) + (Y + 1) = x
     *)
  rewrite <- x_plus_y__x_m1_plus_y_p1.
  apply H.
  (* X <> 0 の証明をする。 *)
  apply beq_nat_false.
  apply negb_true_iff in H0.
  apply H0.
Qed.
(** [] *)

(* ####################################################### *)
(* ####################################################### *)
(* ####################################################### *)
(* **** Exercise: 4 stars, optional (factorial_dec)  *)
(** **** 練習問題: ★★★★, optional (factorial_dec)  *)
(* Remember the factorial function we worked with before: *)
(** 以前に扱った階乗関数を思い出してください: *)

Fixpoint real_fact (n:nat) : nat :=
  match n with
  | O => 1
  | S n' => n * (real_fact n')
  end.

(* Following the pattern of [subtract_slowly_dec], write a decorated
    Imp program that implements the factorial function, and prove it
    correct. *)
(** [subtract_slowly_dec]のパターンに倣って、
    階乗計算の修飾付きImpプログラムを記述し、その正しさを証明しなさい。*)

Example fact_com_dec (x:nat) : dcom :=
  (
    {{ fun st => True }}
    =>                                      (* 導出(1) *)
    {{ fun st => x = x }}
    Z ::= (ANum x)
    {{ fun st => asnat (st Z) = x}}
    =>                                      (* 導出(2) *)
    {{ fun st => asnat (st Z) = x /\ 1 = 1 }};
    Y ::= (ANum 1)
    {{ fun st => asnat (st Z) = x /\ asnat (st Y) = 1 }}
    =>                                      (*  導出(3) *)
    {{ fun st =>
         asnat (st Y) * real_fact (asnat (st Z)) = real_fact x }}; (* ループ不変式 *)
    WHILE (BNot (BEq (AId Z) (ANum 0))) DO
    {{ fun st =>
         asnat (st Y) * real_fact (asnat (st Z)) = real_fact x /\
         asnat (st Z) <> 0 }}               (* ループ不変式、かつ、ループ実行条件 *)
    =>                                      (* 導出(4) *)
    {{ fun st =>
         asnat (st Y) * asnat (st Z) * real_fact (asnat (st Z) - 1) = real_fact x }}
    Y ::= (AMult (AId Y) (AId Z))
    {{ fun st =>
         asnat (st Y) * real_fact (asnat (st Z) - 1) = real_fact x }};
    Z ::= AMinus (AId Z) (ANum 1)
    {{ fun st =>
         asnat (st Y) * real_fact (asnat (st Z)) = real_fact x }} (* ループ不変式 *)
    END
    {{ fun st => 
         asnat (st Y) * real_fact (asnat (st Z)) = real_fact x /\
         asnat (st Z) = 0 }}                   (* ループ不変式、かつ、終了条件 *)
    =>                                         (* 導出(5) *)
    {{ fun st => asnat (st Y) = real_fact x }} (* 要求仕様 *)
  ) % dcom.

Theorem fact_com_dec_correct : forall x,
  dec_correct (fact_com_dec x).
Proof.
  intros x.
  verify.
  (* 導出(3) *)
  subst. rewrite H0. omega.
  (* negb (beq_nat Z 0) = true -> Z <> 0 *)
  apply beq_nat_false_iff.
  apply negb_true_iff.
  apply H0.
  (* Z <> 0 -> negb (beq_nat Z 0) = true *)
  apply negb_true_iff.
  apply beq_nat_false_iff.
  apply H0.
  (* negb (beq_nat Z 0) <> true -> Z = 0 *)
  apply beq_nat_true_iff.
  apply negb_not_true_iff.
  apply H0.
  (* Z = 0 -> negb (beq_nat Z 0) <> true *)
  apply negb_not_true_iff.
  apply beq_nat_true_iff.
  apply H0.
  (* 導出(4) *)
  destruct (asnat (st Z)) as [| z'].
  apply ex_falso_quodlibet. inversion H0.
  rewrite <- H. rewrite <- mult_assoc.
  replace (S z' - 1) with z' by omega.
  reflexivity.
  (* 導出(5) *)
  rewrite <- H.
  rewrite H0.
  simpl. omega.
Qed.

  (* すべて、ここで証明した場合 *)
Theorem fact_com_dec_correct' : forall x,
  dec_correct (fact_com_dec x).
Proof.
  intros x.
  verify.
  (* 導出(3) *)
  subst. rewrite H0. omega.
  (* negb (beq_nat Z 0) = true -> Z <> 0 *)
  destruct (asnat (st Z)) as [| n'].
  intro Contra. inversion H0.
  intro Contra. rewrite Contra in H0. inversion H0.
  (* Z <> 0 -> negb (beq_nat Z 0) = true *)
  destruct (asnat (st Z)) as [| n'].
  simpl. apply ex_falso_quodlibet. apply H0. reflexivity.
  simpl. reflexivity.
  (* negb (beq_nat Z 0) <> true -> Z = 0 *)
  destruct (asnat (st Z)) as [| n'].
  reflexivity.
  apply ex_falso_quodlibet. apply H0. reflexivity.
  (* Z = 0 -> negb (beq_nat Z 0) <> true *)
  destruct (asnat (st Z)) as [| n'].
  intro Contra. inversion Contra.
  intro Contra. rewrite H0 in Contra. inversion Contra.
  (* 導出(4) *)
  destruct (asnat (st Z)) as [| z'].
  apply ex_falso_quodlibet. inversion H0.
  rewrite <- H. rewrite <- mult_assoc.
  replace (S z' - 1) with z' by omega.
  reflexivity.
  (* 導出(5) *)
  rewrite <- H.
  rewrite H0.
  simpl. omega.
Qed.
(** [] *)

(* ####################################################### *)
(* ####################################################### *)
(* ####################################################### *)
(* ####################################################### *)
(* Finally, for a bigger example, let's redo the proof of
    [list_member_correct] from above using our new tools.

    Notice that the [verify] tactic leaves subgoals for each use of
    [hoare_consequence] -- that is, for each [=>] that occurs in the
    decorated program. Each of these implications relies on a fact
    about lists, for example that [l ++ [] = l]. In other words, the
    Hoare logic infrastructure has taken care of the boilerplate
    reasoning about the execution of imperative programs, while the
    user has to prove lemmas that are specific to the problem
    domain (e.g. lists or numbers). *)
(** 最後に、より大きな例として、
    新しい道具立てを使って[list_member_correct]の証明を再度行ってみましょう。

    [verify]タクティックは[hoare_consequence]を利用するたびに
    (つまり修飾付きプログラムに[=>]が現れるたびに)サブゴールを作ることに注意します。
    これらの含意は、リストについての事実(例えば[l ++ [] = l]など)に依存しています。
    言い換えると、ホーア論理のインフラは命令型プログラムの実行についての一般的な部分を扱い、
    一方ユーザは(例えば数値のリストという)問題領域特有の補題を証明しなければなりません。*)

Definition list_member_dec (n : nat) (l : list nat) : dcom := (
    {{ fun st => st X = VList l /\ st Y = VNat n /\ st Z = VNat 0 }}
  WHILE BIsCons (AId X)
  DO {{ fun st => st Y = VNat n
               /\ (exists p, p ++ aslist (st X) = l
               /\ (st Z = VNat 1 <-> appears_in n p))
               /\ bassn (BIsCons (AId X)) st }}
    IFB (BEq (AId Y) (AHead (AId X))) THEN
        {{ fun st =>
          ((st Y = VNat n
            /\ (exists p, p ++ aslist (st X) = l
                /\ (st Z = VNat 1 <-> appears_in n p)))
          /\ bassn (BIsCons (AId X)) st)
          /\ bassn (BEq (AId Y) (AHead (AId X))) st }}
        =>
        {{ fun st =>
            st Y = VNat n
            /\ (exists p, p ++ tail (aslist (st X)) = l
                 /\ (VNat 1 = VNat 1 <-> appears_in n p)) }}
      Z ::= ANum 1
        {{ fun st => st Y = VNat n
             /\ (exists p, p ++ tail (aslist (st X)) = l
                  /\ (st Z = VNat 1 <-> appears_in n p)) }}
   ELSE
        {{ fun st =>
          ((st Y = VNat n
            /\ (exists p, p ++ aslist (st X) = l
                  /\ (st Z = VNat 1 <-> appears_in n p)))
          /\ bassn (BIsCons (AId X)) st)
          /\ ~bassn (BEq (AId Y) (AHead (AId X))) st }}
        =>
        {{ fun st =>
          st Y = VNat n
          /\ (exists p, p ++ tail (aslist (st X)) = l
               /\ (st Z = VNat 1 <-> appears_in n p)) }}
      SKIP
        {{ fun st => st Y = VNat n
            /\ (exists p, p ++ tail (aslist (st X)) = l
                 /\ (st Z = VNat 1 <-> appears_in n p)) }}
   FI ;
   X ::= (ATail (AId X))
     {{ fun st  =>
         st Y = VNat n /\
         (exists p : list nat, p ++ aslist (st X) = l
           /\ (st Z = VNat 1 <-> appears_in n p)) }}
  END
   {{ fun st =>
     (st Y = VNat n
       /\ (exists p, p ++ aslist (st X) = l
            /\ (st Z = VNat 1 <-> appears_in n p)))
     /\ ~bassn (BIsCons (AId X)) st }}
   =>
   {{ fun st => st Z = VNat 1 <-> appears_in n l }}
) % dcom.

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

Lemma beq_true__eq : forall n n',
  beq_nat n n' = true ->
  n = n'.
Proof.
  induction n; destruct n'.
  Case "n = 0, n' = 0".     reflexivity.
  Case "n = 0, n' = S _".   simpl. intros H. inversion H.
  Case "n = S, n' = 0".     simpl. intros H. inversion H.
  Case "n = S, n' = S".     simpl. intros H.
                            rewrite (IHn n' H). reflexivity.
Qed.

Lemma appears_in_snoc1 : forall a l,
  appears_in a (snoc l a).
Proof.
  induction l.
    Case "l = []". apply ai_here.
    Case "l = cons". simpl. apply ai_later. apply IHl.
Qed.

Lemma appears_in_snoc2 : forall a b l,
  appears_in a l ->
  appears_in a (snoc l b).
Proof.
  induction l; intros H; inversion H; subst; simpl.
    Case "l = []". apply ai_here.
    Case "l = cons". apply ai_later. apply IHl. assumption.
Qed.

Lemma appears_in_snoc3 : forall a b l,
   appears_in a (snoc l b) ->
   (appears_in a l \/ a = b).
Proof.
   induction l; intros H.
   Case "l = []". inversion H.
     SCase "ai_here". right. reflexivity.
     SCase "ai_later". left. assumption.
   Case "l = cons". inversion H; subst.
     SCase "ai_here". left. apply ai_here.
     SCase "ai_later". destruct (IHl H1).
       left. apply ai_later. assumption.
       right. assumption.
Qed.

Lemma append_singleton_equation : forall (x : nat) l l',
  (l ++ [x]) ++ l' = l ++ x :: l'.
Proof.
  intros x l l'.
  induction l.
    reflexivity.
    simpl. rewrite IHl. reflexivity.
Qed.

Lemma beq_nat_refl : forall n,
  beq_nat n n = true.
Proof.
  induction n.
    reflexivity.
    simpl. assumption.
Qed.

Theorem list_member_correct' : forall n l,
  dec_correct (list_member_dec n l).
Proof.
  intros n l.
  verify.
  Case "The loop precondition holds.".
    exists []. simpl. split.
      rewrite H. reflexivity.
      rewrite H1. split; inversion 1.
  Case "IF taken".
    destruct H2 as  [p [H3 H4]].
    (* We know X is non-nil. *)
    remember (aslist (st X)) as x.
    destruct x as [|h x'].
      inversion H1.
      exists (snoc p h).
      simpl. split.
         rewrite snoc_equation. assumption.
         split.
           rewrite H in H0.
           simpl in H0.
           rewrite (beq_true__eq _ _ H0).
           intros. apply appears_in_snoc1.
           intros. reflexivity.
  Case "If not taken".
    destruct H2 as [p [H3 H4]].
    (* We know X is non-nil. *)
    remember (aslist (st X)) as x.
    destruct x as [|h x'].
      inversion H1.
      exists (snoc p h).
      split.
        rewrite snoc_equation. assumption.
        split.
          intros. apply appears_in_snoc2. apply H4. assumption.
          intros Hai.  destruct (appears_in_snoc3 _ _ _ Hai).
          SCase "later". apply H4. assumption.
          SCase "here (absurd)".
            subst.
            simpl in H0. rewrite H in H0. rewrite beq_nat_refl in H0.
            apply ex_falso_quodlibet. apply H0. reflexivity.
  Case "Loop postcondition implies desired conclusion (->)".
    destruct H2 as [p [H3 H4]].
    unfold bassn in H1. simpl in H1.
    destruct (aslist (st X)) as [|h x'].
       rewrite append_nil in H3. subst. apply H4. assumption.
       apply ex_falso_quodlibet. apply H1. reflexivity.
  Case "loop postcondition implies desired conclusion (<-)".
    destruct H2 as [p [H3 H4]].
    unfold bassn in H1. simpl in H1.
    destruct (aslist (st X)) as [|h x'].
       rewrite append_nil in H3. subst. apply H4. assumption.
       apply ex_falso_quodlibet. apply H1. reflexivity.
Qed.

(* ####################################################### *)
(* ####################################################### *)
(* ####################################################### *)
(* ####################################################### *)
Definition max a b :=
  if ble_nat a b then b else a.

Definition maximum l := fold_right max 0 l.

Definition maximum_com_dec (l : list nat) : dcom :=
  (
    {{ fun st => aslist (st X) = l }}       (* 初期値 *)
    =>                                      (* 導出(1) *)
    {{ fun st => aslist (st X) = l /\ 0 = 0 }}
    Y ::= ANum 0
    {{ fun st => aslist (st X) = l /\ asnat (st Y) = 0 }}
    =>                                      (* 導出(2) *)
    {{ fun st =>                            (* ループ不変式 *)
         max (asnat (st Y)) (maximum (aslist (st X))) = maximum l }};
    WHILE (BNot (BIsNull (AId X))) DO
    {{ fun st =>                            (* ループ不変式かつループ実行条件 *)
         max (asnat (st Y)) (maximum (aslist (st X))) = maximum l /\
         aslist (st X) <> [] }}
    =>                                      (* 導出(3) *)
    {{ fun st =>                            (* ... head-tail分解、maxの結合 *)
         max (max (asnat (st Y)) (head (aslist (st X)))) (maximum (tail (aslist (st X)))) = maximum l }}
    IFB (BLe (AId Y) (AHead (AId X))) THEN
    {{ fun st =>                            (* THEN条件 *)
         max (max (asnat (st Y)) (head (aslist (st X)))) (maximum (tail (aslist (st X)))) = maximum l /\
         asnat (st Y) <= head (aslist (st X)) }}
    =>                                      (* 導出(4) *)
    {{ fun st =>                            (* ... max Y (head X) = (head X) *)
         max (head (aslist (st X))) (maximum (tail (aslist (st X)))) = maximum l }}
    Y ::= AHead (AId X)
    {{ fun st =>
         max (asnat (st Y)) (maximum (tail (aslist (st X)))) = maximum l }}
    ELSE
    {{ fun st =>                            (* ELSE条件 *)
         max (max (asnat (st Y)) (head (aslist (st X)))) (maximum (tail (aslist (st X)))) = maximum l /\
         head (aslist (st X)) < asnat (st Y) }}
    =>                                      (* 導出(5) *)
    {{ fun st =>                            (* ... max Y (head X) = Y *)
         max (asnat (st Y)) (maximum (tail (aslist (st X)))) = maximum l }}
      SKIP
    {{ fun st =>
         max (asnat (st Y)) (maximum (tail (aslist (st X)))) = maximum l }}
    FI;
    {{ fun st =>
         max (asnat (st Y)) (maximum (tail (aslist (st X)))) =  maximum l }}
    X ::= ATail (AId X)
    {{ fun st =>                            (* ループ不変式 *)
         max (asnat (st Y)) (maximum (aslist (st X))) =  maximum l }}
    END
    {{ fun st =>                            (* ループ不変式かつループ終了条件 *)
         max (asnat (st Y)) (maximum (aslist (st X))) =  maximum l /\
         aslist (st X) = [] }}
    =>                                       (* 導出(6) *)
    {{ fun st => asnat (st Y) = maximum l }} (* 結果 *)
    ) % dcom.

(*
 * maxについての補題
 *)
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
 * 不等号についての補題
 *)
Lemma ble_nat_true__le : forall x y : nat,
                          ble_nat x y = true -> x <= y.
Proof.
  intros x y H.
  apply ble_nat_true.                       (* おなじもの。 *)
  apply H.
Qed.

Lemma ble_nat_false__gt : forall x y : nat,
                            ble_nat x y = false -> x > y.
Proof.
  intros x y H.
  apply ble_nat_false in H.
  apply not_le in H.
  apply H.
Qed.

Lemma le__ble_nat_true : forall x y : nat,
                           x <= y -> ble_nat x y = true.
Proof.
  intros x y H.
  apply not_false_iff_true. unfold not.
  intro Contra.
  apply ble_nat_false__gt in Contra.
  (* 対偶である ble_nat_false__gt を使って証明する。 *)
  omega.
Qed.

Lemma gt__ble_nat_false : forall x y : nat,
                            y < x -> ble_nat x y = false.
Proof.
  intros x y H.
  apply not_true_is_false. unfold not.
  intro Contra.
  apply ble_nat_true__le in Contra.
  (* 対偶である ble_nat_true__le を使って証明する。 *)
  omega.
Qed.

(* 
 * リストについての補題
 *)

Definition bnull {A : Type} (l : list A) : bool :=
  match l with
    | [] => true
    |  _ :: _ => false
  end.

Lemma bnull_true__nil : forall (A : Type) (l : list A),
                          bnull l = true -> l = [].
Proof.
  intros A l H.
  destruct l as [| a' l'].
  Case "[]".
  reflexivity.
  Case "a' :: l'".
  inversion H.
Qed.

Lemma nil__bnull_true : forall (A : Type) (l : list A),
                          l = [] -> bnull l = true.
Proof.
  intros A l H.
  destruct l as [| a' l'].
  Case "[]".
  simpl.
  reflexivity.
  Case "a' :: l'".
  simpl. inversion H.
Qed.

Lemma bnull_false__not_nil : forall (A : Type) (l : list A),
                               bnull l = false -> l <> [].
Proof.
  intros A l H.
  intro Contra.
  apply nil__bnull_true in Contra.
  apply not_true_iff_false in H. apply H.
  apply Contra.
Qed.

Lemma not_nil__bnull_false : forall (A : Type) (l : list A),
                          l <> [] -> bnull l = false.
Proof.
  intros A l H.
  apply not_true_is_false. unfold not.
  intro Contra.
  apply bnull_true__nil in Contra.          (* 対偶を使う。 *)
  apply H. apply Contra.
Qed.

(*
 * 本題
 *)
Theorem maximum_com_dec_correct : forall l,
  dec_correct (maximum_com_dec l).
Proof.
  intros l.
  verify.
  (* 導出(2) *)
  rewrite H. rewrite H0. unfold max.
  simpl. reflexivity.

  (* negb (isNull X) = true -> X <> [] *)
  apply negb_true_iff in H0.
  apply bnull_false__not_nil.
  apply H0.

  (* X <> [] -> negb (isNull X) = true *)
  apply not_nil__bnull_false in H0.
  apply negb_true_iff.
  apply H0.
  
  (* negb (isNull X) <> true -> X = [] *)
  apply bnull_true__nil.
  apply negb_not_true_iff in H0.
  apply H0.

  (* X = [] -> negb (isNill X) <> true *)
  apply nil__bnull_true in H0.
  apply negb_not_true_iff.
  apply H0.

  (* 導出(3) *)
  rewrite <- max_assoc.
  rewrite max_hdtl_equation.
  apply H.
  
  (* ble_nat Y (head X) = true -> Y <= head X *)
  apply ble_nat_true__le.
  apply H0.
  
  (* ble_nat Y (head X) <> true -> head X < asnat Y *)
  apply ble_nat_false__gt.
  apply not_true_iff_false in H0.
  apply H0.
  
  (* 導出(4) *)
  unfold max in H at 2.
  erewrite le__ble_nat_true in H.
  apply H. apply H0.
  
  (* 導出(5) *)
  unfold max in H at 2.  
  erewrite gt__ble_nat_false in H.
  apply H. apply H0.
  
  (* 導出(6) *)
  remember (aslist (st X)) as x'.
  destruct x'.
  (* X = [] のとき *)
  rewrite max_nil in H. rewrite max0r in H.
  apply H.
  (* X = n :: x' のとき *)
  rewrite H0 in H.
  simpl in H.
  rewrite max0r in H.
  apply H.
Qed.

(* [] *)

(* END *)
