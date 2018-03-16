(** ProofCafe SF/PLF Support Page *)
(** Smallstep.v *)

(**
これは、「Software Foundations, Vol.2 Programming Language Foundations」 の
勉強会（ProofCafe）のサポートページです。復習などに利用しててください。

本ファイルの実行は、本ファイルを pfl ディレクトリの中に混ぜて置くか、
pfl のオリジナルの適当なファイルの適当な場所にcopy&pasteすることで可能です。
 *)

(** ご注意：

1. 実際の勉強会は、本ファイルではなく、オリジナルのファイルを直接編集・実行しておこないます。

2. 本ファイルには、演習問題の答えは含まれません。

*)

Require Import Coq.Arith.Arith.
Require Import Coq.Arith.EqNat.
Require Import Coq.omega.Omega.
Require Import Coq.Lists.List.
Import ListNotations.
Require Import Maps.
Require Import Imp. 
Require Import Smallstep.

(* ################################################################# *)
(** ProofCafe ##72 2018/01/20 *)
(** * A Toy Language *)

(** 概要：

1. 定数と加算だけあるおもちゃの言語を定義する。この項をtmとする。

2. big-step style の評価器(evaluator)の定義。evalF。
 evalF tm の実行結果が n 。

3. big-step style の評価関係(evaluation releation)。eval
 論理式 (tm \\ n) 。 tm (項) と自然数(結果 )との関係である。

4. small-step style の評価関係(evaluation releation)。step
 論理式 (tm1 ==> tm2) 。 tm (項) どうしの関係であることに留意する。
 *)

Module PF_SimpleArith1.
Import SimpleArith1.

(** * おもちゃの言語のコンストラクタ *)
Check C : nat -> tm.
Check P : tm -> tm -> tm.

(** tm の例 *)
(* 1 + (2 + 3)) + (11 + (12 + 13)) *)
Definition sample := (P (P (C 1) (P (C 2) (C 3)))
                        (P (C 11) (P (C 12) (C 13)))) : tm.

(** * big-step evaluator *)
Check evalF : tm -> nat.                    (* 関数 *)

(** 例 *)
Compute evalF sample.                       (* = 42 : nat *)

(** * big-step evaluation relation *)
Check eval : tm -> nat -> Prop.

(** 導入した公理 *)
Check E_Const : forall n : nat, C n \\ n.
Check E_Plus : forall (t1 t2 : tm) (n1 n2 : nat),
    t1 \\ n1 -> t2 \\ n2 -> P t1 t2 \\ (n1 + n2).

(** 例 *)
Goal sample \\ 42.
Proof.
  unfold sample.
  apply E_Plus with (n1 := 6) (n2 := 36).
  - apply E_Plus with (n1 := 1) (n2 := 5).
    + now apply E_Const.
    + apply E_Plus with (n1 := 2) (n2 := 3).
      * now apply E_Const.
      * now apply E_Const.
  - apply E_Plus with (n1 := 11) (n2 := 25).
    + now apply E_Const.
    + apply E_Plus with (n1 := 12) (n2 := 13).
      * now apply E_Const.
      * now apply E_Const.
Qed.

(** * small-step evaluation relation *)
Check step : tm -> tm -> Prop.              (* tm1 ==> tm2 *)

(** 導入した公理 *)
Check ST_PlusConstConst :
  forall n1 n2, (P (C n1) (C n2) ==> C (n1 + n2)).
Check ST_Plus1 :
  forall t1 t1' t2, (t1 ==> t1') -> (P t1 t2 ==> P t1' t2).
Check ST_Plus2 :
  forall (n1 : nat) (t2 t2' : tm),
    (t2 ==> t2') -> P (C n1) t2 ==> P (C n1) t2'.

(** 例 *)
Goal sample ==> (P (P (C 1) (C 5))
                   (P (C 11) (P (C 12) (C 13)))).
Proof.
  constructor.
  constructor.
  constructor.
  Show Proof.

  Restart.
  apply ST_Plus1.
  apply ST_Plus2.
  apply ST_PlusConstConst.
Qed.

Goal (P (P (C 1) (C 2)) (C 3)) ==> (P (C 3) (C 3)).
Proof.
  constructor.
  constructor.
  Show Proof.

  Restart.
  apply ST_Plus1.
  apply ST_PlusConstConst.
Qed.


(** 補足説明：

Small-stepのひとつのステップでやっていること：

- 「==>」の左辺の、最も左（で最も深いところ）にある 「P (C n1) (C n2)」を探す。
- これを 「C (n1 + n2)」 に書き換えたものを「==>」の右辺とする。


stepの定義の読み方：

stepの定義は、「->」 を逆向きみ見ていく。
- 左側優先深さ優先で検索し(ST_Plus1)、
- P の第一引数が定数(C n1)になったら、第二引数を見ていって(PT_Plus2)、
- 両方の引数が定数になったら、定数に書き換える(ST_PlusConstConst)。


余力があれば、本章の終わりにある、 
Concurrent Imp の PAR c1 with c2 END の定義と比較してみてください。
*)

(**
以下はうまくいかない例：
 *)
(**
2回分はできない。
 *)
Goal sample ==> (P (C 6)
                   (P (C 11) (P (C 12) (C 13)))).
Proof.
  constructor.
  admit.                                    (* OK. *)
Admitted.

(** 前の例の結果を使って、2回に分ければできる。  *)
Goal (P (P (C 1) (C 5))
        (P (C 11) (P (C 12) (C 13))))       (* 前の例の結果 *)
     ==>
     (P (C 6)
        (P (C 11) (P (C 12) (C 13)))).
  constructor.
  constructor.
Qed.

(**
最も左でなければならない。
 *)
Goal sample ==> (P (P (C 1) (P (C 2) (C 3)))
                   (P (C 11) (C 25))).
Proof.
  admit.                                    (* OK. *)
Admitted.

(**
当然、できない。
*)
Goal sample ==> (C 42).
Proof.
  admit.                                    (* OK. *)
Admitted.
  
End PF_SimpleArith1.

(* ################################################################# *)
(** ProofCafe ##73 2018/02/17 *)
(** * Relations *)

(** 概要：

1. Relations（二項関係）
stepが決定的な二項関係であることの証明、inversionタクティクを使う。

2. Values（値）

3. Strong Progress and Normal Form
stepが強進行性（正規形がある）ことの証明、Coqの定石タクティクを使う。
 *)

Module PF_SimpleArith2.
Import PF_SimpleArith1.
Import SimpleArith1.

(** * 二項関係 *)

(** 二項関係 R が決定的であるという命題 *)
Check @deterministic : forall X : Type, relation X -> Prop.
(** ここで、relation tm に step が渡される。 *)

Print deterministic.
(** = 
fun (X : Type) (R : relation X) =>
forall x y1 y2 : X, R x y1 -> R x y2 -> y1 = y2 *)

(**
補足説明：

二項関係が決定的である。 <-> 二項関係は部分関数 partial function である。 

R x y が決定的ならxに対してyが唯一決まるので関数っぽいけれども、
任意のxに対してyが決まるとは限らないので、部分関数である。

なお、任意のxに対してyが決まる全域関数は、部分関数の一種である。
*)

(** ** step が決定的であることの証明 *)

(** inversion を使う典型的な証明。オリジナルと同内容である。 *)

Theorem step_deterministic'' : deterministic step.
Proof.
  unfold deterministic.
  intros x y1 y2 Hy1 Hy2.
(**
[[
  Hy1 : x ==> y1
  Hy2 : x ==> y2
  ============================
   y1 = y2
]]
*)
  (** 0. Hy1 のコンストラクタで再帰的に場合分けする。 *)
  induction Hy1 as [n1 n2 H1 H2 | t1 t1' t2 H1 IHHy1 H2 |n t1' t2 H1 IHHy1 H2].
  Undo 1.
  generalize dependent y2.
  induction Hy1 as [n1 n2 | t1 t1' t2 H1 IHHy1 |n t1' t2 H1 IHHy1]; intros y2 Hy2'.
  (**
  ST_PlusConstConst の場合：
    Hy2' : P (C n1) (C n2) ==> y2
    x = P (C n1) (C n2) なので、
    ゴールは C (n1 + n2) = y2 である。

  ST_Plus1 の場合：
    Hy2' : P t1 t2 ==> y2
    x = P t1 t2 なので、
    ゴールは P t1' t2 = y2

  ST_Plus2 の場合 :
    P (C n) t1' ==> y2
    x = P (C n) t1' なので、
    ゴールは P (C n) t2 = y2
 *)

(**
[[
   Hy2' : P (C n1) (C n2) ==> y2
  ============================
   C (n1 + n2) = y2
]]
*)
  (** 1. Hy2' にコンストラクタを逆に適用する。 *)
  - inversion Hy2'; subst.
    
    (** 1.1 ST_PlusConstConst の場合、
       Hy2' : P (C n1) (C n2) ==> C (n1 + n2)
       y2 = C (n1 + n2),
       Goal : C (n1 + n2) = C (n1 + n2)
     *)
    + reflexivity.
      
    (** 1.2 ST_Plus1 の場合、
       H2 : C n1 ==> t1'
       これはコンストラクトできない（矛盾）。
       矛盾は inversion で消す！ *)
    + inversion H2.
      
    (** 1.3 ST_Plus2 の場合、
       H2 : C n2 ==> t2'
       これはコンストラクトできない（矛盾）。
       矛盾は inversion で消す！ *)
    + inversion H2.

(**
[[
   H1 : t1 ==> t1'
   IHHy1 : forall y2 : tm, t1 ==> y2 -> t1' = y2
   Hy2' : P t1 t2 ==> y2
  ============================
   P t1' t2 = y2
]]
*)
  (** 2. Hy2' にコンストラクタを逆に適用する。 *)
  - inversion Hy2'; subst.
    
    (** 2.1 ST_PlusConstConst の場合、
        H1 : C n1 ==> t1'
        これはコンストラクトできない（矛盾）。 *)
    (** 矛盾は inversion で消す！ *)
    + inversion H1.
      
    (** 2.2 ST_Plus1 の場合、
       IHHy1 : forall y2 : tm, t1 ==> y2 -> t1' = y2、帰納法
       Goal : P t1' t2 = P t1'0 t2
    *)
    (** generalize dependent y2 したのを活用する。 *)
    + rewrite <- (IHHy1 t1'0).
      * reflexivity.
      * apply H3.
    (** 2.3 ST_Plus2 の場合、
       H1 : C n1 ==> t1'
       これはコンストラクトできない（矛盾）。 *)
    (** 矛盾は inversion で消す！ *)
    + inversion H1.
      
(**
[[
   H1 : t1' ==> t2
   IHHy1 : forall y2 : tm, t1' ==> y2 -> t2 = y2
   Hy2' : P (C n) t1' ==> y2
  ============================
   P (C n) t2 = y2
]]
*)
  (** 3. Hy2' にコンストラクタを逆に適用する。 *)
  - inversion Hy2'; subst.
    
    (** 3.1 ST_PlusConstConst の場合、
       H1 : C n2 ==> t2
       これはコンストラクトできない（矛盾）。 *)
    (** 矛盾は inversion で消す！ *)
    + inversion H1.
      
    (** 3.2 ST_Plus1 の場合、
       H3 : C n ==> t1'0
       これはコンストラクトできない（矛盾）。 *)
    (** 矛盾は inversion で消す！ *)
    + inversion H3.
      
    (** 3.3 ST_Plus2 の場合、
       IHHy1 : forall y2 : tm, t1 ==> y2 -> t1' = y2、帰納法
       Goal : P (C n) t2 = P (C n) t2'
     *)
    (** generalize dependent y2 したのを活用する。 *)
    + rewrite <- (IHHy1 t2').
      * reflexivity.
      * apply H3.
Qed.          

(** now と easy を使う例。 *)
(** Home The Coq Proof Assistant Chapter 8 Tactics 8.8.5 easy *)
(** https://coq.inria.fr/refman/tactics.html#hevea_tactic166 *)
Theorem step_deterministic' : deterministic step.
Proof.
  unfold deterministic.
  intros x y1 y2 Hy1 Hy2.
  generalize dependent y2.
  induction Hy1; intros y2 Hy2.
  - inversion Hy2; subst.
    + reflexivity.
    + easy.
    + easy.
  - inversion Hy2; subst.
    + easy.
    + now rewrite <- (IHHy1 t1'0).
    + easy.
  - inversion Hy2; subst.
    + easy.
    + easy.
    + now rewrite <- (IHHy1 t2'0).
Qed.

(** さらに短くした例。 *)
Theorem step_deterministic : deterministic step.
Proof.
  unfold deterministic.
  intros x y1 y2 Hy1 Hy2.
  generalize dependent y2.
  induction Hy1; intros y2 Hy2;
    inversion Hy2; subst; try easy.
  - now rewrite <- (IHHy1 t1'0).
  - now rewrite <- (IHHy1 t2'0).
Qed.

End PF_SimpleArith2.

(** ** inversion について *)

(**
- http://proofcafe.org/sf/Poly_J.html#lab114
- https://softwarefoundations.cis.upenn.edu/lf-current/Tactics.html#lab136

「任意のコンストラクタは単射であること、また、コンストラクタどうしは互いに素であること。」
 *)

(** step_deterministic は step に対して inversion を行っている。 *)
(** 以下は、 tm に対して inversion を行う例である。 *)

Goal forall n1 n2 n3 n4, P (C n1) (C n2) = P (C n3) (C n4) -> n1 = n3 /\ n2 = n4.
Proof.
  intros n1 n2 n3 n4 H.
  inversion H.
  (** Hにおけるコンストラクタの単射性から、前提に等式が追加される。 *)
  split.
  - reflexivity.
  - reflexivity.
Qed.

Goal forall n1 n2 n3, P (C n1) (C n2) = C n3 -> False.
Proof.
  intros n1 n2 n3 H.
  inversion H.
  (** コンストラクタは互いに素なので、Hは矛盾であり、ゴールの証明が終了する。 *)
Qed.

(*
(** おまけ。 *)
(** 順番が前後するが、λx.(x x) に型がつかないことを言うには、
型が有限性から、xの型 T1 -> T2 が T1 にひとしくないことを使う。
より一般的に、(Inductiveで定義された）コンストラクタの有限性を証明できないだろうか。
*)
(** 参考： TAPL 解答 9.3.2 *)
Goal forall tm1 tm2, P tm1 tm2 = tm1 -> False.
Proof.
  intros tm1 tm2 H.
  induction tm1.
  - easy.
  - inversion H.
    rewrite H1 in *.
    easy.
Qed.
*)

(* ================================================================= *)
(** * Values *)

(** 導入した公理 *)
Check v_const : forall n : nat, value (C n).

(** (C 3) は value であることが証明できる。 *)
Goal value (C 3).
Proof.
  apply v_const.
Qed.

(** Exercise: redo_determinism を解いてみましょう！！！
   ヒント：
   value はひとつだけだが、コンストラクタ v_const を持つ。
   それが前提にあるならば、場合分けをする必要がある。
*)

(* ================================================================= *)
(** ProofCafe ##74 2018/03/17 *)
(** * Strong Progress and Normal Forms *)
(**
概要：

(1) step (==>) が強進行性を満たす。strong_progress
    ∀t, value t ∨ (∃ t', t ==> t').
任意のtmであるtは、値（すなわち C n）であるか、別のtmにステップできる。

(2) tが(stepの)正規形である (normal_form step t) とは、
    ~(∃t', t ==> t')
すなわち、 t ==> t' なる t'が存在しない（もうstepできない）ことをいう。

(3) 値なら正規形である。value_is_nf
    ∀t, value t -> ~(∃t', t ==> t').

(4) 正規形なら値である。nf_is_value
    ∀t, ~(∃t', t ==> t') -> value t.

(5) (3)(4)より、値と正規形は同じである。
    ∀t, value t <-> ~(∃t', t ==> t').

参考：TAPL p.28
*)

(** ** step(==>)が強進行性であることの証明 *)

(** 任意の項 t は、値であるか、別の項 t' にstepできる。
「強」進行性とは、stepに戦略が無くても正規形が得られることをいう。
うまく選ばないと正規形が得られない場合は、単に「進行性」と呼ぶ。
 *)

(** オリジナルは、あいかわらずinversionだけで解いているが、inversionを使わなくても証明できる。
inversionを使うことの是非については議論しないが、ここでは、Coqの定石の説明する。
 *)

(** t は強進行性を満たす。 *)
Theorem strong_progress : forall t : tm,
    value t \/ (exists t', t ==> t').
Proof.
  induction t.                      (** q t を証明したい命題とし、tで帰納する。 *)
  - left.                           (** 帰納の底 q (C n) *)
    now apply v_const.
  - right.              (** 帰納の途中 : q t1 -> q t2 -> q (P t1 t2) *)
    destruct IHt1 as [H11 | H12].         (** 選言を場合分けする。 *)
    (** IHt1 の左側 *)
    + destruct IHt2 as [H21 | H22].       (** 選言を場合分けする。 *)
      (** IHt2 の左側、t1とt2がvalue であるとき。 *)
      * destruct H11 as [n1 H11'].        (** value を場合分けする。 *)
        destruct H21 as [n2 H21'].        (** value を場合分けする。 *)
        exists (C (n1 + n2)).
        now apply ST_PlusConstConst.
      (** IHt2 の右側、t1がvalue、t2がstep可能であるとき。 *)
      * destruct H22 as [t' H22'].       (** exists を場合分けする。 *)
        exists (P t1 t').
        now apply ST_Plus2.
    (** IHt1 の右側、t1がstep可能であるとき。 *)
    + destruct H12 as [t' H12'].         (** exists を場合分けする。 *)
      exists (P t' t2).
      now apply ST_Plus1.
Qed.

(** ** 正規形 *)
Print normal_form.
(**                                        not
fun (X : Type) (R : relation X) (t : X) => ~ (exists t' : X, R t t')
     : forall X : Type, relation X -> X -> Prop
 *)

(** R には step（==>）を渡すなら、
tが正規形であるとは、t ==> t' なる t'が存在しない（もうstepできない）ことをいう。 *)

(** ** 値なら正規形であることの証明 *)
(** t が値なら、t は正規形である。 *)
Lemma value_is_nf : forall v,
  value v -> normal_form step v.
Proof.
  unfold normal_form. (** ゴールが Define されたものの場合 *)
  intros v H.         (** ゴールに ∀や->がある場合。ただし、やりすぎに注意 *)
  destruct H.         (** 前提がデータ型のとき、帰納的でないなら場合分けする。 *)
  intro contra.       (** ゴールが否定のとき。引数の無い intros ではだめ。 *)
  destruct contra.    (** 前提が exists のとき *)
  easy.               (** 前提が矛盾（コンストラクトできない）場合 *) (** inversion H. *)
Qed.

(** ** 正規形なら値であることの証明 *)

(** 補題：t が強進行性を満たすなら、tが正規形なら、tは値である。 *)
(** ただし、これは任意の二項関係(s : tm -> tm -> Prop) で成立する。 *)
(** suhara オリジナルは、assert を使っているが、わかりやすく補題として外に出した。  *)
Lemma l_strong_progress__nf_is_value : forall t s,
    (value t \/ (exists t', s t t')) -> normal_form s t -> value t.
Proof.
  unfold normal_form.
  intros t G H.
  destruct H.              (** 前提が \/ のとき、左右で場合分けする。 *)
  (** 左側 *)
  + easy.                   (** 前提がゴールと同じ。 *) (** apply H0. *)
  (** 右側 *)
  + easy.                         (** 矛盾した前提があるとき。 *)
    (** exfalso. apply H. assumption. *) 
Qed.


(** tが正規形なら、tは値である。 *)
Lemma nf_is_value : forall t,
    normal_form step t -> value t.
Proof.
  intros t.
  apply l_strong_progress__nf_is_value.
  apply strong_progress.
Qed.

(** ** 値と正規形は同じである。 *)
Corollary nf_same_as_value : forall t,
  normal_form step t <-> value t.
Proof.
  split.                                    (** ゴールが <-> のとき *)
  - now apply nf_is_value.
  - now apply value_is_nf.
Qed.

(**
本文より：

なぜ、値と正規形が同じあることが興味深いのでしょう？ 2つの理由があります:

なぜならvalue(値)は構文的概念です。つまり項の形を見ることで定義されま
す。一方normal_form(正規形)は意味論的なものです。 つまり項がどのように
ステップを進むかによって定義されます。 この2つの概念が一致することは自
明ではないのです!

実際、正規形と値の概念が一致「しない」言語はたくさん存在します。
*)

(**
定石集：

まじかんと さんのページから：

証明事例集: 前提が……のとき
https://magicant.github.io/programmingmemo/coq/byhyp.html

証明事例集: ゴールが……のとき
https://magicant.github.io/programmingmemo/coq/bygoal.html

tmiyaさんんページから：
http://study-func-prog.blogspot.jp/2010/12/coq-coq-advent-calender-apply-1-of-25.html
http://study-func-prog.blogspot.jp/2010/12/coq-coq-advent-calender-inversion-19-of.html
 *)

(* ################################################################# *)
(** * Multi-Step Reduction *)
(** 概要：

マルチステップ簡約(multi-step reduction)関係 ==>* は、
1ステップ関係 ==> の反射推移閉包です。

（step自体は反射でも推移でもない。）
*)

Check step : tm -> tm -> Prop.
Check step : relation tm.
Check multi step : tm -> tm -> Prop.        (* tm1 ==>* tm2 *)
Check multi step : relation tm.             (* tm1 ==>* tm2 *)

(** 導入される公理 *)
Check multi_refl step : forall x : tm, x ==>* x. (* 反射 *)
Check multi_step step : forall x y z : tm, x ==> y -> y ==>* z -> x ==>* z. (* 推移 *)

(** lf/Rel.v では、clos_refl_trans_1n として定義されている。 *)

(** 前出の ==> ではだめだった例を証明する。 *)

Definition sample := (P (P (C 1) (P (C 2) (C 3)))
                        (P (C 11) (P (C 12) (C 13)))) : tm.

Goal sample ==>* (P (C 6)
                   (P (C 11) (P (C 12) (C 13)))).
Proof.
  apply multi_step with (y:=(P (P (C 1) (C 5)) (P (C 11) (P (C 12) (C 13))))).
  (** sample ==> P (P (C 1) (C 5)) (P (C 11) (P (C 12) (C 13))) *)
  - constructor.
    constructor.
    constructor.
    constructor.
  - apply multi_step with (y:=(P (C 6) (P (C 11) (P (C 12) (C 13))))).
    (** P (P (C 1) (C 5)) (P (C 11) (P (C 12) (C 13))) ==>
         P (C 6) (P (C 11) (P (C 12) (C 13))) *)
    + constructor.
      constructor.
    + apply multi_refl.
Qed.

(* ================================================================= *)
(** ** Normal Forms Again *)
(**
tが0以上のステップでt'に簡約され、
t'が正規形(normal form、前出、もうこれ以上stepできない形)のとき、
「t'はtの正規形である」と言います。

これを二項関係 [normal_form_of t t'] で定義し、
[t ==>* t'] で示す。
 *)

Print normal_form_of.
(** [fun (t t' : tm) => t ==>* t' /\ ~(∃t'', t' ==> t'')] *)

(**
概要：
二項関係(normal_form_of)は、次のふたつの性質をもつ。

(1) 正規形の一意性：この二項関係(normal_form_of)は決定的である。
(2) 簡約（評価）の停止性：すべての項に対して、正規形が存在する。

(1)(2)より、normal_form_of は全域関数である。

参考：TAPL p.29
 *)

(**
(1) 正規形の一意性を証明する。

xがy1とy2に簡約でき、y1もy2も正規形なら、y1 = y2 である。

[[
deterministic normal_form_of :
  ∀x y1 y2. normal_form_of x y1 -> normal_form_of x y2 -> y1 = y2
]]
*)

(** 補題： 正規型なら、 stepしない suhara *)
(** [step_normal_form x] と [x ==> y] は矛盾 *)
(** ただし、これは任意の二項関係(s : tm -> tm -> Prop) で成立する。 *)
Lemma l_nf__not_step : forall (x y : tm) s, normal_form s x -> ~ s x y.
Proof.
  unfold normal_form.
  intros x y s H1 H2.
  apply H1.
  now exists y.
Qed.

Goal deterministic normal_form_of.
Proof.
  unfold deterministic.
  (** forall x y1 y2 : tm, normal_form_of x y1 -> normal_form_of x y2 -> y1 = y2 *)
  unfold normal_form_of.
  unfold step_normal_form.                  (* normal_form step *)
  intros x y1 y2 P1 P2.
  inversion P1 as [P11 P12]; clear P1.
  inversion P2 as [P21 P22]; clear P2.
  generalize dependent y2.
  
  induction P11 as [x|x y z H]; intros y2 Hy2 P2.
  - inversion Hy2.
    + reflexivity.
    + induction P12.
      now exists y.
  - apply IHP11.
    + apply P12.
    + inversion Hy2; subst.
      * now apply (l_nf__not_step y2 y step) in P2.  (* P2 と Hy2 は矛盾、補足参照 *)
      * now rewrite (step_deterministic x y y0). (* H と H0 から y = y0 *)
    + easy.                                      (* apply P2 *)
Qed.
(** step の決定性 step_deterministic も使用します。  *)

(**
(2) 簡約（評価）の停止性を証明する。

stepは正規化性を持つ（任意のtは、0以上のステップで、正規形に到達できる）。
つまり、任意のtに対して、あるt'があって、tからステップを進めるとt'に到達し、
かつt'は正規形である。 

[[
step_normalizing :
    ∀t, ∃t', t ==>* t' /\ ~(∃t'', t' ==> t'')
]]
*)

Lemma step_normalizing : forall t, exists t', normal_form_of t t'.
Proof.
  induction t.
  - exists (C n).
    split.
      + now apply multi_refl.
      + rewrite nf_same_as_value.
        now apply v_const.
  - destruct IHt1 as [t1' [H11 H12]].
    destruct IHt2 as [t2' [H21 H22]].
    rewrite nf_same_as_value in H12.
    rewrite nf_same_as_value in H22.
    inversion H12 as [n1 H].
    inversion H22 as [n2 H'].
    rewrite <- H in H11.
    rewrite <- H' in H21.
    exists (C (n1 + n2)).
    split.
    + apply multi_trans with (P (C n1) t2).
      * now apply multistep_congr_1.
      * apply multi_trans with (P (C n1) (C n2)).
        ** apply multistep_congr_2.
           *** apply v_const.
           *** apply H21.
        ** apply multi_R.
           apply ST_PlusConstConst.
    + rewrite nf_same_as_value.
      now apply v_const.
Qed.

(* ================================================================= *)
(** ** Equivalence of Big-Step and Small-Step *)
(** 概要：

（略）

*)

(** END *)
