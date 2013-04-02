(*
inversion について。
*)

Require Export SfLib_J.

(*
Logic_J.vより。

Inversion 再び

これまでにも inversion が等値性にからむ仮定や帰納的に定義された命題に対して 使われるところを見てきま
した。今度もやることは変わりませんが、もう少し近くまで 寄って inversion の振る舞いを観察してみましょ
う。

一般的に inversion タクティックは、
- 帰納的に定義された型 P の命題 H をとる。 
- その型 P の定義にある各コンストラクタ C が、 
  - H が C から成っていると仮定するような新しいサブゴールを作る。 
  - C の引数（前提）を、追加の仮定としてサブゴールのコンテキストに加える。 
  - C の結論（戻り値の型）を現在のゴールとmatchして、 C を適用できるような一連の等式算出する。 
  - そしてこれらの等式をサブゴールのコンテキストに加えてから、 
  - もしこの等式が充足可能でない場合（S n = O というような式を含むなど）は、 即座にサブゴールを解決する。

例 : or で構築された仮定を反転（ invert ）すると、or に二つのコンストラクタが あるため二つのサブゴー
ルが生成されます。コンストラクタ (P ∨ Q) の結果 （戻り値の型）は P や Q の形からくる制約を付けません。
そのため追加の等式が サブゴールのコンテキストに加えられることはありません。

例 : and で構築された仮定を反転（ invert ）すると、and にはコンストラクタが 一つしかないため、サブゴー
ルも一つしか生成されません。やはり、コンストラクタ (P ∧ Q) の結果（戻り値の型）は P や Q の形からく
る制約を付けず、追加の等式が サブゴールのコンテキストに加えられることはありません。このコンストラクタ
は引数を二つ とりますが、それらはサブゴールのコンテキストに現れます。

例 : eq で構築された仮定を反転（ invert ）すると、これにもやはりコンストラクタが 一つしかないため、サ
ブゴールも一つしか生成されません。しかしこの場合 コンストラクタ refl_equal の形は我々にもう少し情報を
与えてくれます。 それは、eq の二つの引数は同じでなければならないという点です。 inversion タクティック
はこの事実をコンテキストに加えてくれます。

*)

(*
証明事例集: 自前で inversion を行う より
http://homepage2.nifty.com/magicant/programmingmemo/coq/maninv.html

ただし、ここでは同じ例題をinversionを使って証明する。
*)

(* 単純な例: even *)

Inductive even : nat -> Prop :=
  | even_O : even O
  | even_SS : forall n, even n -> even (S (S n)).

Goal ~ even 1.
Proof.
  intro H.
  inversion H.
Qed.
(*
even 1 には even_O と even_SS のどちらも当てはまらないため、inversion を使うと直ちに証明が完了する。
*)
(*
では、組み込みの inversion タクティクを使わない場合はどうするか。以下のように単純に case H をしただけ
では、even の引数が 1 であることが場合分けの後に忘れられてしまうので、False を導くための条件が揃わな
い。実際、case H した後の一つ目のサブゴールは case H をする前と全く変わっていない。（略）
*)

(* 追記： ~even 5のとき。*)

Goal ~ even 7.
Proof.
  intro H.
  inversion H.
  (* H1 : even 5 *)
  inversion H1.
  (* H3 : even 3 *)
  inversion H3.
  (* H5 : even 1 *)
  inversion H5.
Qed.

(* 途中で、いらない前提を消すと、見通しがよくなる。*)
Goal ~ even 7.
Proof.
  intro H.
  inversion H. subst. clear H.
  (* H1 : even 5 *)
  inversion H1. subst. clear H1.
  (* H0 : even 3 *)
  inversion H0. subst. clear H0.
  (* H1 : even 1 *)
  inversion H1.
Qed.

(* 次は証明できるに違いないが、前提のほうは even 0 から進まない。
また、前提Hを反転ることについては、GoalはTrueでもFalseでも関係ない、ことに注意するべきだ。
 *)
Goal even 2 -> True.
Proof.
  intro H.
  inversion H. subst. clear H.
  exact I.
Qed.

(* その上、とどめのinversion H1さえ、GoalがTrueでもFalseでも有効である。 *)
Goal even 3 -> True.
Proof.
  intro H.
  inversion H. subst. clear H.
  inversion H1.                             (* exact Iでもよいが。 *)
Qed.

(* さすがに、これは証明できない。*)
Goal even 2 -> False.
Proof.
  intro H.
  inversion H. subst. clear H.
  inversion H1.
Admitted.                                   (* OK *)


(* 今度は、S (S n) が偶数ならば n も偶数であることを示そう。*)
Goal forall n, even (S (S n)) -> even n.
Proof.
  intros n H.
  inversion H.
  apply H1.
Qed.

(* 複数の引数を取る述語: succ *)

(*
場合分けをする述語が複数の引数を取る場合は、それに合わせて複数の等式をゴールに追加する必要がある。こ
こでは、二つの自然数の後者関係を表す述語 succ を定義し、任意の自然数は自分自身の後者ではないことを示
そう。
*)

Inductive succ : nat -> nat -> Prop :=
  succ_intro : forall n, succ n (S n).
(* succ は二つの引数を取るので、それらに対応する二つの等式をゴールに追加してから case する。 *)

Goal forall n, ~ succ n n.
Proof.
  intros n H.
  induction n.
  inversion H.
  apply IHn.
  inversion H.
  apply H.
Qed.

(* 固定パラメータのある述語: le *)

(*
Inductive le (n : nat) : nat -> Prop :=
  | le_n : n <= n
  | le_S : forall m : nat, n <= m -> n <= S m

le は二つの引数を受け取るように見えるが、実際には最初の引数は固定されたパラメータである。すなわち正確
には、任意の自然数 n に対して le n が一つの引数を受け取ると考える必要がある。そのため、inversion では
最初の引数 n に関する条件は得られず、最後の引数に関する条件だけが得られる。最後の引数に関する条件を場
合分けの後まで覚えておくために、最後の引数に関する等式をゴールに追加してから場合分けを行う。

なぜ最初の引数に関する等式を追加してはいけないのかというと、もしそうすると pattern 後の case で正しく
値が置き換えられないからである。
*)

(* 以下の例は、n <= 0 から n = 0 を導く証明である。 *)

Goal forall n, n <= 0 -> n = 0.
Proof.
  intros n H.
  induction n.
  reflexivity.
  inversion H.
Qed.

(*
タクティクリファレンス: 帰納法と場合分け より
http://homepage2.nifty.com/magicant/programmingmemo/coq/t-induct.html
*)

(*
inversion タクティク

inversion タクティクは、case タクティクや destruct タクティクのように代数的データ型に対する場合分けを
行うが、コンストラクタの引数に関する条件を保存する。

特定の値に関する条件を表す述語が代数的データ型として定義してあり、そのような述語が実際に前提として得
られている場合に、その述語から具体的な値に関する条件を取り出すのに使う。
*)

Print le.
(*
Inductive le (n : nat) : nat -> Prop :=
| le_n : n <= n
| le_S : forall m : nat, n <= m -> n <= S m.
*)

Goal forall n : nat, n <= 0 -> n = 0.
Proof.
  intros n H.
  inversion H as [ H' | ].
  reflexivity.
Qed.
(*
上の例では、前提 H : n <= 0 から条件 n = 0 を取り出すために inversion を用いている。述語 le には二つ
のコンストラクタがあるが、le_S から作ることのできる条件の型 n <= S m は前提 H の型 n <= 0 に適合しな
いため、この場合は自動的に除外される。le_n の型 n <= n と H の型 n <= 0 とを照らし合わせた結果として
条件 n = 0 が前提に追加され、この等式を利用して自動的にゴールの n が 0 に書き換えられる。
*)

(*
inversion ident
前提 ident に対して inversion を適用し、得られる条件を前提に追加する。指定した前提が存在しない場合は、
先に intros until ident を試みる。
as によって前提名を指定しないで inversion を使うと、処理系によって自動的に前提名が生成される。生成さ
れる前提名は常に同じとは限らないので、前提名に依存した証明を書く場合は以下の as を用いる構文を使うこ
と。

inversion num
intros until num を行い、最後に追加された前提に対して inversion を適用する。

inversion … as intropattern
追加される前提の名前を指定して inversion する。名前の指定のしかたは destruct … as … と似ているが、
inversion が取り出した条件 (等式) の名前も追加で指定する必要がある。条件の名前の指定は injection …
as … に準ずる。名前が足りない場合は処理系が自動的に名前を選ぶので注意。
*)

Inductive list_in {A : Type} : A -> list A -> Prop :=
| in_hd : forall a l, list_in a (a :: l)
| in_tl : forall a b l, list_in a l -> list_in a (b :: l).

Goal forall l, list_in 0 (1 :: l) -> list_in 0 l.
Proof.
  inversion 1 as [ | a b l' H' H1 [H2 H3] ].
  exact H'.
Qed.
(*
上の例では、述語 list_in の二つのコンストラクタのうち in_hd の場合については条件が合わずに自動的に除
外されるので名前を指定していない。in_tl の場合の名前の指定は、まず a, b, l', H' の四つがそれぞれ
in_tl の四つの引数に対応しており (ここまでは destruct と同じ)、その後の H1 と [H2 H3] はそれぞれ
list_in の二つの引数 (A 型と list A 型) に対応して得られる二つの条件 a = 0 と b :: l' = 1 :: l に対応
している。後者は自動的に適用される injection により b = 1 と l' = l とに分解されるため、それに合わせ
て H2 と H3 の二つの名前を指定している。
*)

(*
inversion … in ident1 … identn
ゴールだけでなく前提 ident1 … identn においても、得られた条件に基づいた書き換えを行う。

inversion … as … in …
inversion タクティクの最も一般的な形。

inversion_clear ident
inversion_clear ident as …
inversion_clear ident in …
inversion_clear ident as … in …
inversion した後に、ident および不要な条件等を自動的に前提から消去する。

inversion ident1 using ident2
inversion ident1 using ident2 in …
Derive Inversion コマンドで作成した補題 ident2 を使用して inversion ident1 を行う。
*)

Derive Inversion le_0_inv with (forall n, n <= 0) Sort Prop.

Check le_0_inv.
(*
le_0_inv
     : forall (n : nat) (P : nat -> Prop),
       (n <= 0 -> n = 0 -> P 0) -> n <= 0 -> P n
*)

Goal forall n, n <= 0 -> n = 0.
Proof.
  intros n H.
  inversion H using le_0_inv.
  reflexivity.
Qed.
(*
この例で inversion H using le_0_inv がしていることは、pattern n; apply le_0_inv, H に等しい。
*)

(*
Derive Inversion コマンドの亜種として、Derive Inversion_clear, Derive Dependent Inversion, Derive
Dependent Inversion_clear コマンドがある。

dependent inversion ident
dependent inversion ident as …
dependent inversion ident with …
dependent inversion ident as … with …
dependent inversion_clear ident
dependent inversion_clear ident as …
dependent inversion_clear ident with …
dependent inversion_clear ident as … with …
ident 自体がゴールの型に含まれる場合に使う。通常の inversion/inversion_clear の処理をする他に、ゴール
の型に含まれる ident を実際に場合分けされた値に置換する。

simple inversion ident
simple inversion num
より単純な inversion を行う。すなわち、場合分けの際に条件が噛み合わない場合を除外したり、得られた条件
を元にゴールを書き換えたりしない。追加される前提名は処理系が自動的に選ぶので、前提名に依存した証明を
書く際には使わないこと。*)

(* END *)
