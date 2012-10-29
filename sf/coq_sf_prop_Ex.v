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

(*  **** Exercise: 4 stars (palindromes) *)
(** **** 練習問題: ★★★★ (palindromes) *)

(** palindrome（回文）は、最初から読んでも逆から読んでも同じになるよう
    なシーケンスです。

    - 以下を証明しなさい。
[[ forall l, pal (l ++ rev l). ]]
    - 以下を証明しなさい。
[[ forall l, pal l -> l = rev l. ]]
*)

Inductive pal : list nat -> Prop :=
| pal0 : pal []
| pal1 : forall (x : nat), pal [x]
| pal2 : forall (x : nat) (l : list nat),
  pal l -> pal (x :: (snoc l x)).

Theorem pal_app_rev : forall l, pal (l ++ rev l).
Proof.
  intros l.
  induction l.
  (* pal ([] ++ rev []) *)
  simpl.
  apply pal0.
  (* pal ((x :: l) ++ rev (x :: l)) *)
  simpl.
  SearchAbout list.
  Check snoc_with_append.
  rewrite <- snoc_with_append.
  apply pal2.
  apply IHl.
Qed.

Fixpoint rev (l : list nat) : list nat :=
  match l with
    | []    => []
    | h :: t => snoc (rev t) h
  end.

Lemma rev_snoc : forall x l, x :: rev l = rev (snoc l x).
Proof.
  intros x l.
  induction l.
  simpl.  
  reflexivity.

  simpl.
  rewrite <- IHl.
  simpl.
  reflexivity.
Qed.

Lemma snoc_rev : forall x l, snoc (rev l) x = rev (x :: l).
Proof.
  intros x l.
  induction l.
  simpl.
  reflexivity.
  simpl.
  reflexivity.
Qed.

Lemma snoc_xlx : forall (x : nat)  l, x :: (snoc l x) = snoc (x :: l) x.
Proof.
  intros x l.
  induction l.
  simpl.
  reflexivity.
  simpl.
  reflexivity.
Qed.

Theorem pal_eq_rev : forall l, pal l -> l = rev l.
Proof.
  intros l H.
  induction H.
  (* [] = rev [] *)
  simpl.
  reflexivity.  

  (* [x] = rev [x] *)
  simpl.
  reflexivity.  

  (* x :: snoc l x = rev (x :: snoc l x) *)
  rewrite <- snoc_rev.
  rewrite <- rev_snoc.
  rewrite <- snoc_xlx.
  rewrite <- IHpal.
  reflexivity.
Qed.

(* 模範解答はこちらです。https://gist.github.com/3963617
   補助定理を自分で証明せず、List.v の
   rev_unit : forall (l:list A) (a:A), rev (l ++ [a]) = a :: rev l.
   を使って解いています。
   *)
(** [] *)

(*  **** Exercise: 5 stars, optional (palindrome_converse) *)
(** **** 練習問題: ★★★★★, optional (palindrome_converse) *)
(**  一つ前の練習問題で定義した [pal] を使って、これを証明しなさい。
[[
     forall l, l = rev l -> pal l.
]]
*)

Theorem eq_rev_pal : forall l, l = rev l -> pal l.
Proof.
Admitted.                                   (* XXXXXX *)
(** [] *)

(*  **** Exercise: 4 stars (subsequence) *)
(** **** 練習問題: ★★★★ (subsequence) *)
(** あるリストが、別のリストのサブシーケンス（ _subsequence_ ）であるとは、
    最初のリストの要素が全て二つ目のリストに同じ順序で現れるということです。
    ただし、その間に何か別の要素が入ってもかまいません。例えば、
[[
    [1,2,3]
]]
    は、次のいずれのリストのサブシーケンスでもあります。
[[
    [1,2,3]
    [1,1,1,2,2,3]
    [1,2,7,3]
    [5,6,1,9,9,2,7,3,8]
]]
    しかし、次のいずれのリストのサブシーケンスでもありません。
[[
    [1,2]
    [1,3]
    [5,6,2,1,7,3,8]
]]

    - [list nat] 上に、そのリストがサブシーケンスであることを意味するよ
      うな命題 [subseq] を定義しなさい。（ヒント：三つのケースが必要に
      なります）

    - サブシーケンスである、という関係が「反射的」であることを証明しな
      さい。つまり、どのようなリストも、それ自身のサブシーケンスである
      ということです。

    - 任意のリスト [l1]、 [l2]、 [l3] について、もし [l1] が [l2] のサ
      ブシーケンスならば、 [l1] は [l2 ++ l3] のサブシーケンスでもある、
      ということを証明しなさい。.

    - （これは少し難しいですので、任意とします）サブシーケンスという関
      係は推移的である、つまり、 [l1] が [l2] のサブシーケンスであり、
      [l2] が [l3] のサブシーケンスであるなら、 [l1] は [l3] のサブシー
      ケンスである、というような関係であることを証明しなさい。（ヒント：
      何について帰納法を適用するか、よくよく注意して下さい。）
*)

Inductive subseq : list nat -> list nat -> Prop :=
| nseq0 : subseq [] []
| nseq1 : forall (n : nat) (l1 : list nat) (l2 : list nat),
  subseq l1 l2 -> subseq (n :: l1) (n :: l2)
| nseq2 : forall (n : nat) (l1 : list nat) (l2 : list nat),
  subseq l1 l2 -> subseq       l1  (n :: l2).

Theorem subseq_sym : forall l : list nat, subseq l l.
Proof.
  intros.
  induction l.
  apply nseq0.
  apply nseq1.
  apply IHl.
Qed.

Theorem subseq_app :
  forall l1 l2 l3 : list nat, subseq l1 l2 -> subseq l1 (l2 ++ l3).
Proof.
  intros l1 l2 l3 H.
  induction H.
  simpl.
  (* subseq [] l3 *)
  induction l3.
  (** subseq [] [] *)
  apply nseq0.
  (** subseq [] (x :: l3) *)
  apply nseq2.
  apply IHl3.
  simpl.
  (* subseq (n :: l1) (n :: l2 ++ l3) *)
  apply nseq1.
  apply IHsubseq.
  simpl.
  (*  subseq l1 (n :: l2 ++ l3) *)
  apply nseq2.
  apply IHsubseq.
Qed.

Theorem subseq_trs :
  forall l1 l2 l3 : list nat, subseq l1 l2 -> subseq l2 l3 -> subseq l1 l3.
Proof.
Admitted.                                   (* XXXXXX *)
(** [] *)

(*  **** Exercise: 2 stars, optional (foo_ind_principle) *)
(** **** 練習問題: ★★, optional (foo_ind_principle) *)

(** 次のような、帰納的な定義をしたとします： *)
Inductive foo'' (X : Set) (Y : Set) : Set :=
| foo''1 : X -> foo'' X Y
| foo''2 : Y -> foo'' X Y
| foo''3 : foo'' X Y -> foo'' X Y.
Print foo''_ind.
(*
   次の空欄を埋め、この定義のために Coq が生成する帰納法の原理を完成させなさい。
   回答：
*)
Definition foo''_ind_me : forall P : nat -> Prop,
  forall (X Y : Set) (P : foo'' X Y -> Prop),
    (forall x : X, P (foo''1 X Y x)) ->
    (forall y : Y, P (foo''2 X Y y)) ->
    (forall p : foo'' X Y, P p  -> P (foo''3 X Y p)) ->
    (forall p : foo'' X Y, P p).
(** [] *)

(** **** 練習問題: ★★, optional (bar_ind_principle) *)
(*
   ↓これ(bar'''_ind)に対応する帰納的な集合の定義を書きなさい。
   回答：
*)
Inductive bar''' : Set :=
| bar'''1 : nat -> bar'''
| bar'''2 : bar''' -> bar'''
| bar'''3 : bool -> bar''' -> bar'''.
Print bar'''_ind.

(** 次に挙げた帰納法の原理について考えてみましょう：↑ *)
Definition bar'''_ind_me : forall P : bar''' -> Prop,
  (forall n : nat, P (bar'''1 n)) ->
  (forall b : bar''', P b -> P (bar'''2 b)) ->
  (forall (b : bool) (b0 : bar'''), P b0 -> P (bar'''3 b b0)) ->
  forall b : bar''', P b.
(** [] *)

(*  **** Exercise: 2 stars, optional (no_longer_than_ind) *)
(** **** 練習問題: ★★, optional (no_longer_than_ind) *)

(** 次のような、帰納的に定義された命題が与えられたとします：*)
Inductive no_longer_than (X : Set) : (list X) -> nat -> Prop :=
| nlt_nil  : forall n, no_longer_than X [] n
| nlt_cons : forall x l n, no_longer_than X l n ->
  no_longer_than X (x::l) (S n)
| nlt_succ : forall l n, no_longer_than X l n ->
  no_longer_than X l (S n).
Check no_longer_than_ind.

(*
   この命題のために Coq が生成する帰納法の原理を完成させなさい。
   回答：
*)
Definition no_longer_than_ind_me : forall (X : Set) (P : list X -> nat -> Prop),
  (forall n : nat, P [] n) ->               (* nlt_nil *)
  (forall (x : X) (l : list X) (n : nat),
    no_longer_than X l n -> P l n -> P (x :: l) (S n)) -> (* nlt_cons *)
  (forall (l : list X) (n : nat),
    no_longer_than X l n -> P l n -> P l (S n)) -> (* nlt_succ *)
  forall (l : list X) (n : nat), no_longer_than X l n ->  P l n.
(** [] *)

(*  **** Exercise: 2 stars, optional (R_provability) *)
(** **** 練習問題: ★★, optional (R_provability) *)
(** Coq に次のような定義を与えたとします： *)

Inductive R : nat -> list nat -> Prop :=
  | c1 : R 0 []
  | c2 : forall n l, R n l -> R (S n) (n :: l)
  | c3 : forall n l, R (S n) l -> R n l.

(*
   次のうち、証明可能なのはどの命題でしょうか？
    - [R 2 [1,0]]
    - [R 1 [1,2,1,0]]
    - [R 6 [3,2,1,0]]
*)

Goal (R 2 [1,0]).
Proof.
  apply c2.
  apply c2.
  apply c1.
Qed.

Goal (R 1 [1,2,1,0]).
Proof.
  apply c3.
  apply c2.    
  apply c3.
  apply c3.
  apply c2.
  apply c2.
  apply c2.
  apply c1.
Qed.

Goal (R 6 [3,2,1,0]).
Proof.
(* 
  回答：
  c2を使わないと、リストは減らない（[]に向かわない)。
  c2を使えるためには、c3をつかって、[R 4 [3,...]] に持っていく必要があるが、
  c3をつかうと、[R 7 [3,...]] と、第一引数の値が増加するばかり。
  ゆえに、[R 6 [3,2,1,0]]は、証明可能ではない。
*)
Abort.

(** [] *)
