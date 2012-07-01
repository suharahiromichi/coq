(** ソフトウエアの基礎 Benjamin C. Pierceさん他、梅村さん他訳
   Prop_J: 命題と根拠からの抜粋
   練習問題の回答が含まれていても、正解ではないかもしれない。
   @suharahiromichi *)

(** 概要
   1. 根拠(Evidence)と証明オブジェクト(Proof Objects)
   カリー・ハワード対応について。
   
   2. 帰納的に定義された型に対する帰納法
   inductionタクティックは、apply t_indのラッパーである。
   
   3. 帰納法の原理
   t_indの定義について。
   
   4. 根拠に対する帰納法の推測
   destructとinduction、induction Eとindeuction n、inductionとinversion

   5. Coqのふたつの空間
   TypeとProp
   *)
   
Inductive day : Type :=
| monday : day
| tuesday : day
| wednesday : day
| thursday : day
| friday : day
| saturday : day
| sunday : day.

(** 1. 根拠(Evidence)と証明オブジェクト(Proof Objects) *)

(** 以下は同じことをいう。

   ・eがPの証明である。
   ・命題Pが真であることの、根拠がe。
   ・e : P

   最後のe : Pは、「式eが型Pを持つ」と対応する (C-H対応)。

                 命題          ~  集合 / 型
                 propositions  ~  sets / types

                 証明          ~  元、要素 / データ値
                 proofs        ~  data values

   命題 [P] の各要素は、それぞれ異なる [P] の根拠です。
   もし要素がないならば、[P] は証明不能です。
   もしたくさんの要素があるならば、[P] には多数の異なった証明があります。 *)
(** 証明オブジェクトとは、与えられた命題(型)の根拠(式)を構築するもの。
   タクティックによる証明は、自分で証明オブジェクトを書く代わりに、証明
   オブジェクトを構築する方法をCoqに指示すること。
*)

Inductive good_day : day -> Prop :=
| gd_sat : good_day saturday
| gd_sun : good_day sunday.

Inductive day_before : day -> day -> Prop :=
| db_tue : day_before tuesday monday
| db_wed : day_before wednesday tuesday
| db_thu : day_before thursday wednesday
| db_fri : day_before friday thursday
| db_sat : day_before saturday friday
| db_sun : day_before sunday saturday
| db_mon : day_before monday sunday.

(** good dayならok dayである。また、ok dayの前日ならok dayである。 *)
Inductive ok_day : day -> Prop :=
| okd_gd : forall d, good_day d -> ok_day d
| okd_before : forall d1 d2, ok_day d2 -> day_before d2 d1 -> ok_day d1.

(** 証明オブジェクトによる証明 *)
Definition okdw : ok_day wednesday :=
  okd_before wednesday thursday
    (okd_before thursday friday
       (okd_before friday saturday
         (okd_gd saturday gd_sat)
         db_sat)
       db_fri)
    db_thu.

(** タクテッィクによる証明 *)
Theorem okdw' : ok_day wednesday.
Proof.
  (** wednesday is OK because it's the day before an OK day *)
  apply okd_before with (d2:=thursday).
  (** "subgoal: show that thursday is ok". *)
  (** thursday is OK because it's the day before an OK day *)
  apply okd_before with (d2:=friday).
  (** "subgoal: show that friday is ok". *)
  (** friday is OK because it's the day before an OK day *)
  apply okd_before with (d2:=saturday).
  (** "subgoal: show that saturday is ok". *)
  (** saturday is OK because it's good! *)
  apply okd_gd.
  apply gd_sat.
  (** "subgoal: show that the day before saturday is friday". *)
  apply db_sat.
  (** "subgoal: show that the day before friday is thursday". *)
  apply db_fri.
  (** "subgoal: show that the day before thursday is wednesday". *)
  apply db_thu.
Qed.

(** 定理 okd_before2 *)
Definition okd_before2 := forall d1 d2 d3,
  ok_day d3 -> day_before d2 d1 -> day_before d3 d2 -> ok_day d1.

(** タクテッィクによる証明 *)
Theorem okd_before2_valid : okd_before2.
Proof.
  intros.
  unfold okd_before2.
  intros.
  Check (okd_before d1 d2).
  apply (okd_before d1 d2).
  Check (okd_before d2 d3).
  apply (okd_before d2 d3).
  apply H.
  apply H1.
  apply H0.
Qed.

(** 証明オブジェクトによる証明 *)
Definition okd_before2_valid' : okd_before2 :=
  fun (d1 d2 d3 : day) =>
  fun (H : ok_day d3) =>
  fun (H0 : day_before d2 d1) =>
  fun (H1 : day_before d3 d2) =>
  okd_before d1 d2 (okd_before d2 d3 H H1) H0.

   
(** 2. 帰納的に定義された型に対する帰納法 *)

(** [Inductive] でデータ型を新たに定義するたびに、Coqは帰納法の原理に対
   応する公理を自動生成します。型[t]に対応する帰納法の原理は[t_ind]とい
   う名前になります。*)

(** 自然数の例 *)
Inductive nat : Type :=
| O : nat
| S : nat -> nat.
Definition nat_ind_me :
  forall P : nat -> Prop,
    P O ->                                  (* O : nat *)
    (forall n : nat, P n -> P (S n))  ->    (* S : nat -> nat *)
    forall n : nat, P n :=
      fun P : nat -> Prop => nat_rect P.
(** 記載はないが、:= 以降をつけると、実際にapplyできるようになる。
   nat_rect の定義はInductiveの定義による。内容は、Printで確認できる。
   *)
Print nat_rect.

Inductive False' : Prop := .
Definition False_ind_me :
  forall P : Prop,
    False' ->                               (* 存在しないコンストラクタ *)
    P :=
    fun P : Prop => False'_rect P.

Fixpoint plus (n : nat) (m : nat) : nat :=
  match n with
    | O => m
    | S n' => S (plus n' m)
  end.
Notation "x + y" := (plus x y)  (at level 50, left associativity) : nat_scope.

Definition one : nat := S O.

(** 定理 n + 1 = S n *)
Theorem plus_one_r : forall n : nat,
  n + one = S n.
Proof.
  intros.
  induction n.
  reflexivity.
  simpl.
  rewrite IHn.
  reflexivity.
  Qed.

Theorem plus_one_r' : forall n : nat,
  n + one = S n.
Proof.
  (** apply nat_indは、
     forall n, n + one = S n を forallなn に対して、
     O + one = S O
     forall n, n + one = S n -> S n + one = S (S n)
     のふたつにわけるのである。
     
     そのまえにintros nすると、
     n + one = S n を適当なn に対して、
     n + one = O
     forall n0 : nat, n + one = n0 -> n + one = S n0
     にわけることになってしまい、証明がたちいかなくなる。
     induction nなら、そこをなんとかしてくれるのだろう。
     *)
  apply nat_ind.
  simpl.
  reflexivity.
  simpl.
  intros.
  rewrite H.
  reflexivity.
  Qed.

(** 3. 帰納法の原理 *)
(** コンストラクタ [c1] ... [cn] を持った型 [t] を定義すると、Coqは次の形の定理を生成します。
[[
    t_ind :
       forall P : t -> Prop,
            ... c1の場合 ... ->
            ... c2の場合 ... ->
            ...                 ->
            ... cnの場合 ... ->
            forall n : t, P n
]]

型宣言は複数のコンストラクタを持ち、各コンストラクタが帰納法の原理の各節に対応する。
・ 各コンストラクタ [c] は引数 [a1]..[an] を取る。
・ [ai] は [t]（定義しようとしているデータ型）、もしくは別の型 [s] かのどちらかである。
・ 帰納法の原理において各節は以下のことを述べている。
・ "型 [a1]...[an] のすべての値 [x1]...[xn] について、各 [x] について [P] が成り立つならば、
[c x1 ... xn] についても [P] が成り立つ"
*)

Inductive yesno : Type :=
| yes : yesno
| no : yesno.
Definition yesno_ind_me :
  forall P : yesno -> Prop,
    P yes  ->
    P no  ->
    forall y : yesno, P y :=
      fun P : yesno -> Prop => yesno_rect P.

Inductive rgb : Type :=
| red : rgb
| green : rgb
| blue : rgb.
Definition rgb_ind_me :
  forall P : rgb -> Prop,
    P red ->
      P green ->
      P blue ->
      forall r : rgb, P r :=
        fun P : rgb -> Prop => rgb_rect P.

Inductive natlist : Type :=
| nnil : natlist
| ncons : nat -> natlist -> natlist.
Definition natlist_ind_me :
  forall P : natlist -> Prop,
    P nnil  ->
    (forall (n : nat) (l : natlist), P l -> P (ncons n l)) ->
    forall n : natlist, P n :=
      fun P : natlist -> Prop => natlist_rect P.

Inductive natlist1 : Type :=
  | nnil1 : natlist1
  | nsnoc1 : natlist1 -> nat -> natlist1.
Definition natlist1_ind_me :
  forall P : natlist1 -> Prop,
    P nnil1 ->
    (forall n : natlist1, P n -> forall n0 : nat, P (nsnoc1 n n0)) ->
    forall n : natlist1, P n :=
      fun P : natlist1 -> Prop => natlist1_rect P.

Inductive ExSet : Type :=
  | con1 : bool -> ExSet
  | con2 : nat -> ExSet -> ExSet.
Definition ExSet_ind_me :
  forall P : ExSet -> Prop,
    (forall b : bool, P (con1 b)) ->
    (forall (n : nat) (e : ExSet), P e -> P (con2 n e)) ->
    forall e : ExSet, P e :=
      fun P : ExSet -> Prop => ExSet_rect P.

(** 多相的なデータ型
   定義全体が集合 [X] によってパラメータ化されていることです。つまり、
   それぞれの [X] ごとに帰納型 [list X] を定義していることになります。
   *)

Inductive list (X:Type) : Type :=
| nil : list X
| cons : X -> list X -> list X.
(** コンストラクタに対しては、毎回明示的に[X]（パラメータ化された型）を与える必要がある。
   タクテッィクから使う場合は、Implicit Arguments で省略できる(see. sfja/Poly_J.v)。
   しかし、list_indの定義としては、省略されるわけではない。*)
Definition list_ind_me :
  forall (X : Type) (P : list X -> Prop),
    P (nil X) ->
    (forall (x : X) (l : list X), P l -> P (cons X x l)) ->
    forall l : list X, P l :=
      fun X : Type => fun P : list X -> Prop => list_rect X P.

Inductive tree (X:Type) : Type :=
| leaf : X -> tree X
| node : tree X -> tree X -> tree X.
Definition tree_ind_me :
  forall (X : Type) (P : tree X -> Prop),
    (forall x : X, P (leaf X x)) ->
    (forall t1 : tree X, P t1 -> (forall t2 : tree X, P t2 -> P (node X t1 t2))) ->
    (forall t : tree X, P t) :=
    fun X : Type => fun P : tree X -> Prop => tree_rect X P.

Inductive mytype (X : Type) : Type :=
| constr1 : X -> mytype X
| constr2 : nat -> mytype X
| constr3 : mytype X -> nat -> mytype X.
Definition mytype_ind_me :
  forall (X : Type) (P : mytype X -> Prop),
    (forall x : X, P (constr1 X x)) ->
    (forall n : nat, P (constr2 X n)) ->
    (forall m : mytype X, P m -> forall n : nat, P (constr3 X m n)) ->
    forall m : mytype X, P m :=
      fun X : Type => fun P : mytype X -> Prop => mytype_rect X P.

Inductive foo (X Y : Type) : Type :=
| bar : X -> foo X Y
| baz : Y -> foo X Y
| quux : (nat -> foo X Y) -> foo X Y.
Definition foo_ind_me :
  forall (X Y : Type) (P : foo X Y -> Prop),
    (forall x : X, P (bar X Y x)) ->        (* bar *)
    (forall y : Y, P (baz X Y y)) ->        (* baz *)
    (forall f1 : nat -> foo X Y, (forall n : nat, P (f1 n)) -> P (quux X Y f1)) -> (* quux *)
    forall f2 : foo X Y, P f2 :=
      fun X Y : Type => fun P : foo X Y -> Prop => foo_rect X Y P.

Inductive foo' (X : Type) : Type :=
  | C1 : list X -> foo' X -> foo' X
  | C2 : foo' X.
Definition foo'_ind_me :
  forall (X : Type) (P : foo' X -> Prop),
    (forall (l : list X) (f : foo' X), P f -> P (C1 X l f)) -> (* C1 *)
    P (C2 X) ->                                                (* C2 *)
    forall f : foo' X, P f :=
      fun X : Type => fun P : foo' X -> Prop => foo'_rect X P.

(** 4. 根拠に対する帰納法の推測 *)

Inductive ev : nat -> Prop :=
| ev_0 : ev O
| ev_SS : forall n : nat, ev n -> ev (S (S n)).

Definition pred (n : nat) : nat :=
  match n with
    | O => O
    | S n' => n'
  end.

Fixpoint evenb (n : nat) : bool :=
  match n with
    | O        => true
    | S O      => false
    | S (S n') => evenb n'
  end.

Definition even (n : nat) : Prop :=
  evenb n = true.

(** destructとinduction *)

(** 定理：ev n -> ev pred(pred n) *)
Theorem ev_minus2: forall n,
  ev n -> ev (pred (pred n)).
Proof.
  intros n E.
  (** ev (pred (pred n)) を E(= ev n)に対して、
     E = ev_0のときの、ev (pred (pred O))
     E = ev_SSのときの、forall n', ev n' -> pred (pred (S (S n')))
     のふたつにわける。*)
  destruct E as [| n' E'].
  (* E = ev_0 *)
  simpl.
  apply ev_0.
  (* E = ev_SS n' E' *)
  simpl.
  apply E'.
Qed.

(** 定理 ev -> even n *)
Theorem ev_even : forall n,
  ev n -> even n.
Proof.
  intros n E.
  (** even n を E(= ev n)に対して、
     E = ev_0のときの、even 0
     E = ev_SSのときの、forall n', ev n' ->  even (S (S n'))
     のふたつにわける。*)
  induction E as [| n' E'].
  (* E = ev_0 *)
  unfold even.
  reflexivity.
  (* E = ev_SS n' E' *)
  (** destruct E の場合、
     帰納の前提 IHE' : even n' が消えてしまう。*)
  unfold even.
  apply IHE'.
Qed.

(** induction E と induction n *)

(** 上の定理 ev n -> ev pred(pred n) と定理 ev -> even n は、
   destruct E または inductoion E として証明した。
   しかし、destruct n または inductoion n とすると証明できない。
   
   今の段階では、根拠 [ev n] に対する帰納法は [n] に対する帰納法に似ているが、
   [ev n] が成立する数についてのみ着目することができると直感的に理解しておいて問題ありません。

   nについての帰納は、自然数 0,1,2,3,4.... に対して帰納する。
   ev nについての帰納は、ev nの成立する、つまり偶数、0,2,4,6,8... に対して帰納する。
*)

(** inductionとinversion *)

(** 定理 ev (SS n) -> ev n *)
Theorem SSev_even : forall n,
  ev (S (S n)) -> ev n.
Proof.
  intros n E.
  inversion E as [| n' E'].
  apply E'.
Qed.

(** [inversion I] ここで、I = ev n は、inversion をする前の前提である、
   [E : ev (S (S n))] を分析する。
   
   Eはev_SSを使って構築されていいることがわかるので、コンストラクタを後
   ろから前に使い、あたらしいサブゴール [E' : ev n] が生成される。
   
   補助的な等式[H0 : n' = n]が追加される。
*)
(*
   destruct(とinduction)
   (ひとつめのゴール)
  n : nat
  ============================
   ev n

   (ふたつめのゴール)
  n' : nat
  ev : n'
  ============================
   ev S (S n')

   inversion (ゆいいつのゴール)
  n : nat
  E : ev (S (S n))
  n' : nat
  E' : ev n
  H0 : n' = n
  ============================
   ev n
   *)

(** 定理 ev (SSSS n) -> ev n *)
Theorem SSSSev_even : forall n,
  ev (S (S (S (S n)))) -> ev n.
Proof.
  intros n E.
  inversion E as [| n' E'].
  apply SSev_even.
  apply E'.
Qed.

(** 定理：ev n -> ev pred(pred n) *)
Theorem ev_minus2': forall n,
  ev n -> ev (pred (pred n)).
Proof.
  intros n E.
  inversion E as [| n' E'].
  (* E = ev_0 *)
  simpl.
  apply ev_0.
  (* E = ev_SS n' E' *)
  simpl.
  apply E'.
Qed.

(** 定理：ev n -> ev pred(pred n) については、
   destruct, induction, inversionのどれでも証明できる。
 ふたつめのゴールの前提が、違うことがわかる。

destruct のとき、
  n' : nat
  E' : ev n'
  ============================
   ev (pred (pred (S (S n'))))

induction のとき、
  n' : nat
  E' : ev n'
  IHE' : ev (pred (pred n'))
  ============================
   ev (pred (pred (S (S n'))))

inversion のとき、
  n : nat
  E : ev n
  n' : nat
  E' : ev n'
  H : S (S n') = n
  ============================
   ev (pred (pred (S (S n'))))
*)

(** 本文の説明より引用：
    [I] が現在のコンテキストにおいて帰納的に宣言された仮定 [P] を参照し
    ているとします。ここで、[inversion I] は、[P]のコンストラクタごとに
    サブゴールを生成します。 各サブゴールにおいて、 コンストラクタが
    [P] を証明するのに必要な条件によって [I] が置き換えられます。サブゴー
    ルのうちいくつかは矛盾が存在するので、 [inversion] はそれらを除外し
    ます。 残っているのは、元のゴールが成り立つことを示すのに必要なサブ
    ゴールです。
    
    先ほどの例で、 [inversion] は [ev (S (S n))] の分析に用いられ、 こ
    れはコンストラクタ [ev_SS] を使って構築されていることを判定し、その
    コンストラクタの引数を仮定に追加した新しいサブゴールを生成しました。
    (今回は使いませんでしたが、補助的な等式も生成しています。)
    
    このあとの[定理 ev -> False]では、inversion のより一般的な振る舞い
    について調べていきましょう。[inversion] タクティックは、仮定が矛盾
    していることを示し、ゴールを達成するためにも使えます。*)

(** 定理 ev -> False *)
Theorem even5_nonsense :
  ev (S (S (S (S (S O))))) -> False.
Proof.
  intros Hev5.
  inversion Hev5 as [|n Hev3].
  inversion Hev3 as [|n' Hev1].
  inversion Hev1.
Qed.

(** 5. Coqのふたつの空間 *)

(** Coq の式は2つの異なる空間のどちらかに属しています。
   - [Type] は計算とデータの空間です。
   - [Prop] は論理的表明と根拠の空間です。

   (1) 値 (Value)
   [Type] 空間において、値はデータとして捉えます。
   [Prop] において、値を根拠として捉えます。値は導出木と呼ばれることもあります。
   
   (2) 帰納的定義 (Inductive Definitions)
   - [Type] 帰納的な型 [nat] の定義は、要素の全てが自然数を表しているような集合を表します。
   帰納的な定義が「全ての値の集合」から以下のような属性を持つ要素だけを
   抜き出して部分集合 [nat] を作っていると考えられます。
   - 値 [O] はこの集合の要素である。
   - この集合は、 [S] の適用に対し閉じている（つまり、値 [n] がこの集合の要素なら [S n] もまたこの集合の要素である）。
   - これらの条件を満たす最小の集合がこの集合である。
   （つまり集合 [nat] の要素だけが上の二つの条件を満たしていて、それ以外のものはこの集合に入っていない）。
   
   - [Prop] 帰納的な型 [ev] の定義は、その数字が偶数であるという根拠となる命題を集めたものの定義です。
   全ての [n] について、この定義が全ての値の集合から以下の条件を満たす
   値を全て集めて部分集合 [ev n] を抜き出してくるような定義、ということです。
   - 値 [ev_0] は集合 [ev O] の要素である。
   - この集合は [ev_SS] の型が正しい（well-typed な）適用に関して閉じている。
   -- つまり、もし値 [e] が集合 [ev n] の要素なら、値[ev_SS n e] は集合 [ev (S (S n))] の要素である。
   - これらの条件を満たす最小の集合がこの集合である。
   (つまり集合 [ev n] の要素だけが上の二つの条件を満たしていて、それ以外のものはこの集合に入っていない）。

   (3) 型(Type)、Propと種類(kinds)
   [Type] や [Prop] 、そしてそれらの複合式（ [Type -> Type] など）には、「ひとつ上位の」分類が可能です。
   それを、単なる「型」と混同しないために「種類 (kinds)」と呼ぶことにします。
   [nat] や [nat->nat] 、[list nat] などは全て [Type] という「種類」です。[list] は [Type -> Type] という種類です。
   [ev] は [nat -> Prop] という種類です。
   
   (4) 命題とブール値 (厳密に区別する)
   - ブール値は、「計算の世界における値」です。
   [bool] 型の式は全て、必ず [true] か [false] のどちらかに簡約することができます。
   - 命題は「論理の世界における型」です。これらは「証明可能（この型の式を書くことができる）」か、
   「証明不能（そのような式は存在しない）」かのいずれかです。従って「命題が [true] である」というような言い方は意味を持ちません。
   
   (5) 関数(Functions)と限量子(Quantifiers) (同一視する)
   [A -> B] は、[forall x : A, B] の略記と考えてよい。
   戻り値の型 [B] が引数 [x] を参照する場合（例：[forall X : Type, list (list X)]）はこの略記が使えない。
   しかし、後者を関数と呼ぶこともある（厳密には依存積か）。
   
   (6) 関数と含意(implies) (同一視する)
   含意に根拠を与えるということは、関数に根拠を与えるということと同じで
   す。Coqでは関数と論理学の「含意」に同じ表記を与えている理由です。
   *)

(* END *)
