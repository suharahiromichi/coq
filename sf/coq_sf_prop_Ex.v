(** * Prop_J: 命題と根拠 *)

(** 練習問題のうち、簡単に解けなかったものや、ProofCafeの皆さんに教えて
   もらって解けた問題を記録しています。模範解答ではありませんが、できる
   だけコメントを多くし、私がどこで躓いたかわかるようにしました。なお、
   お約束として、答えや解説の正しさは無保証です。*)
(* @suharahiromochi 2012_09_25 *)

Require Export Prop_J.
(* 定義などを省略しているほか、以前に証明した定理を補題として使う場合があります。
   そのために、Prop_J 全体をrequireしています。注意してください。*)

(* **** Exercise: 2 stars (plus_one_r') *)
(** **** 練習問題: ★★  (plus_one_r') *)
(** [induction] タクティックを使わずに、下記の証明を完成させなさい。 *)

(* まず、inductionを使う例 *)
Theorem plus_one_r : forall n : nat,
  n + 1 = S n.
Proof.
  intros n.                                 (* introsは省ける。 *)
  induction n.
  reflexivity.
  simpl.
  rewrite IHn.
  reflexivity.
  Qed.

(* elimを使うなら、introは必須。 *)
Theorem plus_one_r' : forall n : nat,
  n + 1 = S n.
Proof.
  intros n.                                 (* introsは必須。 *)
  elim n.
  simpl.
  reflexivity.
  simpl.
  intros n0 H.
  rewrite H.
  reflexivity.
Qed.

(* apply nat_indの例 *)
Theorem plus_one_r'' : forall n : nat,
  n + 1 = S n.
Proof.
  (* ここに intros n. を書いてはいけない。 *)
  apply nat_ind.
  simpl.
  reflexivity.
  simpl.
  intros n0 H.
  rewrite H.
  reflexivity.
Qed.

(* refineで証明を与える *)
(* elim n は、refine (xxx_ind (ゴール) _ _ n) とおなじ。*)
Theorem plus_one_r''' : forall n : nat,
  n + 1 = S n.
Proof.
  intros n.
  refine (nat_ind (fun n => n + 1 = S n) _ _ n).
  simpl.
  reflexivity.
  simpl.
  intros n0 H.
  rewrite H.
  reflexivity.
Qed.

(* ProofCafe当日の模範解答 *)
Theorem plus_one_r'''' : forall n : nat,
  n + 1 = S n.
Proof.
  Print plus.
  (* ここに intros n. を書いてはいけない。 *)
  apply nat_ind.
  (* ひとつめのGoal *)
  reflexivity.
  (* ふたつめのGoal *)
  intros n0 H.
  change (S (n0 + 1) = S (S n0)).
  (* changeは、simplとおなじだが、具体的に指定する。 *)
  rewrite H.
  reflexivity.
Qed.

Print plus_one_r.
Print plus_one_r'.
Print plus_one_r''.
Print plus_one_r'''.
Print plus_one_r''''.

(* 感想。Printで出力される式はすべて同じです。とくに、elimとinductionが
   同じなことは、覚えておくとよいように思います。
   同様に、caseとdistructの組も同じ。*)

(** [] *)

(* **** Exercise: 1 star (tree) *)
(** **** 練習問題: ★ (tree) *)
(** 次のデータ型に対してCoqが生成する帰納法の原理を予測しなさい。
    答えが書けたら、それをCoqの出力と比較しなさい。 *)

Inductive tree (X:Type) : Type :=
| leaf : X -> tree X
| node : tree X -> tree X -> tree X.

Definition tree_rect' :
  forall (X : Type) (P : tree X -> Type),
    (forall x : X, P (leaf X x)) ->
    (forall t1 : tree X, P t1 ->
      (forall t2 : tree X, P t2 -> P (node X t1 t2))) ->
    (forall t : tree X, P t).
Proof.
  intros X P f f0.
  fix F 1.                                  (* tによる帰納 *)
  intros t.
  destruct t.
  apply f.
  apply f0.
  apply F.
  apply F.
Qed.

Definition tree_ind' :
  forall (X : Type) (P : tree X -> Prop),   (* 1行め *)
    (forall x : X, P (leaf X x)) ->         (* 2行め *)
    (forall t1 : tree X, P t1 ->            (* 3行め *)
      (forall t2 : tree X, P t2 -> P (node X t1 t2))) ->
    (forall t : tree X, P t).               (* 4行め *)
Proof.
(* fun X : Type => fun P : tree X -> Prop => tree_rect X P *)
  intros X P H H0 t.
  apply tree_rect'.
  apply H.
  apply H0.
Qed.
(* 補足説明：
   1行め、全体がX:Typeでパラメータ化される。(forall X)
   2行め、leafコンストラクタの場合。        (* c1 *)
   3行め、nodeコンストラクタの場合。引数二つを受け取る。(t1 と t2) (* c2 *)
   4行め、2行め3行めがみたされたt:tree Xは、P tを満たす。
   *)
Print tree_rect.
Print tree_rect'.
Print tree_ind.
Print tree_ind'.
(* 感想。題意はtree_indの型を示すことですが、独自にtree_rectとtree_ind
   を定義してみました。t_rectの定義には、fixタクティクを使わないといけ
   ません。*)
(** [] *)

(* なお、型tをInductiveで定義をしても、その型が帰納的でなければ、
   t_rectがなくてもt_indを定義できます。その例を示します。*)
Inductive False' : Prop := .
Definition False'_ind' :
forall P : Prop,
  False' ->                             (* 存在しないコンストラクタ *)
  P.
Proof.
  intros P H.
  case H.
Qed.
Print False'.
Print False'_ind'.
Print False_rect.                (* False_rectはあるが、帰納しない。*)
Print False_ind.

(* **** Exercise: 1 star, optional (four_ev) *)
(** **** 練習問題: ★, optional (four_ev) *)
(** 4が偶数であることをタクティックによる証明と証明オブジェクトによる証
   明で示しなさい。 *)

Theorem four_ev' :
  ev 4.
Proof.
  apply ev_SS.                              (* Goal : ev 4 *)
  apply ev_SS.                              (* Goal : ev 2 *)
  apply ev_0.                               (* Goal : ev 0 *)
Qed.

Definition four_ev : ev 4 :=
  (ev_SS (S (S O)) (ev_SS O ev_0)).
(** [] *)

(** 練習問題ではないが、よく使う定理を inversion の例として示します。 *)
Theorem SSev_even : forall n,
  ev (S (S n)) -> ev n.
Proof.
  intros n E.
  inversion E as [| n' E'].
  apply E'.
Qed.

(* **** Exercise: 3 stars (ev_ev_even) *)
(** **** 練習問題: ★★★ (ev_ev_even) *)
(** 何に対して帰納法を行えばいいかを探しなさい。(ちょっとトリッキーですが) *)

Theorem ev_ev_even : forall n m,
  ev (n+m) -> ev n -> ev m.
Proof.
  intros n m H1 H2.
  induction H2.                             (* ev n について帰納する。 *)
  (* ev (0 + m) のもとで ev m を証明する。 *)
  simpl in H1.
  apply H1.

  (* ev (n + m) -> em m のもとで ev m を証明する。 *)
  apply IHev.
  simpl in H1.
  SearchAbout ev.
  apply SSev_even.
  apply H1.
Qed.
(**
   感想。ev nで帰納することは、既に勉強しています。
   できてしまうと、どこにもトリックはないようですが、evの性質をよく理解していないと、
   記号操作だけでは、simpl in H1 と apply SSev_even の組み合わせは思いつきませんでした。
   *)
(** [] *)

(* **** Exercise: 1 star (inversion_practice) *)
(** **** 練習問題: ★ (inversion_practice) *)

Theorem SSSSev_even : forall n,
  ev (S (S (S (S n)))) -> ev n.
Proof.
  intros n E.
  inversion E as [| n' E'].                 (* apply SSev_even. *)
  inversion E' as [| n'' E''].              (* apply SSev_even. *)
  apply E''.
Qed.
(**
   感想。SSev_even とおなじことを2回繰り返せば解けるわけです。
   aaply SSev_even を2回繰り返してもよいのですが、
   inversion を2回実行するのもおもしろいと思いました。
   自動的に（解けるまで）繰り返してくれると、もっとうれしいですね。
   *)
(** [] *)

(* **** Exercise: 3 stars, optional (ev_plus_plus) *)
(** **** 練習問題: ★★★, optional (ev_plus_plus) *)
(** 既存の補題を適用する必要のある練習問題です。帰納法も場合分けも不要
    ですが、書き換えのうちいくつかはちょっと大変です。Basics_J.v の
    [plus_swap'] で使った [replace] タクティックを使うとよいかもしれま
    せん。 *)
Theorem ev_plus_plus : forall n m p,
  ev (n+m) -> ev (n+p) -> ev (m+p).
Proof.
  intros n m p Hnm Hnp.
  (* ev (m + p) *)
  apply (ev_ev_even (n + m) (m + p)).
  (*  ev (n + m + (m + p)) *)
  rewrite <- (plus_assoc n m (m + p)).
  (*  ev (n + (m + (m + p))) *)
  rewrite (plus_assoc m m p).
  (*  ev (n + ((m + m) + p)) *)
  rewrite (plus_comm (m + m) p).
  (*  ev (n + (p + (m + m))) *)
  rewrite (plus_assoc n p (m + m)).
  (*  ev ((p + n) + (m + m)) *)
  apply (ev_sum (n + p) (m + m)).

  (* ev (n + p) *)
  apply Hnp.

  (* ev (m + m) *)
  rewrite <- double_plus.
  (* ev (double m) *)
  apply double_even.

  (* ev (n + m) *)
  apply Hnm.
Qed.
(**
   感想。ev (n + m + m + p) の証明をするというヒントをもらって解きました。
   これを ev (n + p + double m) に変換するのは、ちょっと大変でした。
   おそらく、上記が最短コースだと思いますが、もっとよい方法があるかもしれません。
   replaceを使っていませんね。
 *)

Theorem ev_plus_plus' : forall n m p,
  ev (n+m) -> ev (n+p) -> ev (m+p).
Proof.
  intros n m p Hnm Hnp.
  (* ev (m + p) *)
  apply (ev_ev_even (n + m) (m + p)).
  (*  ev (n + m + (m + p)) *)
  replace (n + m + (m + p)) with (n + p + (m + m)).
  (*  ev ((p + n) + (m + m)) *)
  apply (ev_sum (n + p) (m + m)).
  (* ev (n + p) *)
  apply Hnp.
  (* ev (m + m) *)
  rewrite <- double_plus.
  (* ev (double m) *)
  apply double_even.

  (* replace によるサブゴールの証明をおこなう。 *)
  (* n + p + (m + m) = n + m + (m + p) *)
  rewrite <- (plus_assoc n m (m + p)).
  (* n + p + (m + m) = n + (m + (m + p)) *)
  rewrite (plus_assoc m m p).
  (* n + p + (m + m) = n + (m + m + p) *)
  rewrite (plus_comm (m + m) p).
  (* n + p + (m + m) = n + (p + (m + m)) *)
  rewrite (plus_assoc n p (m + m)).
  (* n + p + (m + m) = n + p + (m + m) *)
  reflexivity.
  (* サブゴールの証明終わり。 *)

  (* ev (n + m) *)
  apply Hnm.
Qed.
(** 感想。replaceを使ってみました。やっていることは同じです。
   等式の書き換えのほうが解りやすいでしょうか。
   サブゴールを証明するためのrewriteを簡潔に書くのは次のステップです。
   *)

(** [] *)
