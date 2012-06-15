(* Coq Advent Calender *)
(* http://study-func-prog.blogspot.com/2010/12/coq-coq-advent-calender-reflexivity-25.html *)


(* 1/25 apply *)
(*
   「この仮定（下記の例では pq）を使うとゴール（下記の例では Q）が出て来る」という時に、
   apply pq とすると、ゴール Q が変化します。学校で習う普通の証明の順序と違って、
   Coqの証明はゴールを一歩一歩、仮定に戻して行きます。その時使うのが apply です。
*)


Lemma Sample_of_apply : forall P Q:Prop, P -> (P->Q) -> Q.
Proof.
  intros P Q p pq.
  apply pq.
  apply p.
Qed.


(* 2/25 auto *)
(*
   Coq は簡単な証明は自動的に証明してくれる機能が幾つかありますが、
   auto はよく使われます。autoが何をやっているか知りたい場合は、
   autoの代わりにinfo autoと入力すると、autoの中で何をしてるかが判ります。
   Coqの初学者にはinfoは便利ですよ。
*)


Lemma Sample_of_auto : forall A B:Prop, ((((A->B)->A)->A)->B)->B.
Proof.
  info auto.
Qed.


(* 3/25 rewrite *)
(*
   rewrite は仮定にある等式を使ってゴールを書き換えます。
   下記の例では、リスト xs について帰納法を用いて証明していますが、
   ゴールの中に含まれるlength (xs ++ ys)を、
   帰納法の仮定IHxsを用いてrewriteすることでlength xs + length ysに書き換えています。
*)


Require Import List.
Lemma Sample_of_rewrite : forall (A:Set)(xs ys:list A),
  length (xs ++ ys) = length xs + length ys.
Proof.
  intros A xs ys.
  induction xs.
  reflexivity.
  simpl.
  rewrite IHxs.
  reflexivity.
Qed.


(* 4/25 destruct *)
(*
   destruct は基本的にはある項を場合分けする時使うのですが、
   仮定の中にある /\ とか \/ とか exists とかを分解するのに使うのに便利です。
   （それ以外のときは induction とか case_eq とか使う事が多い様にも思います。）
   下記の例では仮定 abc を分解して仮定 a, b, c を作っています。
*)


Lemma Sample_of_destruct : forall A B C:Prop,
  A /\ (B /\ C) -> (A /\ B) /\ C.
Proof.
  intros A B C abc.
  destruct abc as (a, (b, c)).
  split; [ split | idtac ]; assumption.
Qed.


(* 5/25 intros *)
(*
   実は過去４回の記事でも毎回 intros を使用していました。
   forall とかで定義された変数や -> の左の式とかを仮定に持って行く為に使います。
   introの複数形なので、introを必要な回数繰り返してもOKです。
   intros. だけでも勝手に適当に名前（仮定は通常 H? みたいな名前）を付けてくれますが、
   判りやすさを考えると自分で適切な名前を付けた方が良いと思います。
*)


Lemma Sample_of_intros : forall A B C:Prop, (A->B->C) -> (A->B) -> A -> C.
Proof.
  intros A B C abc ab a.
  apply abc.
  exact a.
  apply ab; exact a.
Qed.


(* 6/25 omega *)
(*
   Coq でよく使われる tactic の６つ目は omega です...
   ってanarchy proofは課題が数学寄りに偏っているから、
   順序が６つ目というのはあまり気にしないで下さい。
   omega タクティックは、
   forallとかexistsとかを含まない形のPresburger算術の式を自動証明してくれます。
   端的に言うと、
   
   ・割り算無し。
   ・変数と変数の掛け算が入っていない。
   ・変数と定数（2, 3などの具体的な整数）の掛け算はOK。
   
   みたいな感じの等式 or 不等式を証明します。
   Coqがよく使われる理由は、この手の数式関係の自動証明が便利に使えるからだと思います。
   整数の等式不等式に関する公理定理を組み合わせて証明するとか大変ですからね。


   簡単な例はこんなのです。
   使い方は簡単で、Require Import Omega して、introsとかして、omega と入力するだけ。
*)


Require Import Omega.
Lemma Sample_of_omega : forall x:nat, x > 1 -> 3 * x > x + 2.
Proof.
  intros.
  info omega.
Qed.


(* 7/25 assert *)
(*
   １つ目のapplyのところで書いた様に、Coqの証明は最初にゴールがあって、
   それを仮定と逆に戻して行く格好になっています。
   しかし証明する人間は仮定からゴールを考える方が楽な場合、
   つまり証明途中で適当な補題を作りたくなる場合があります。
   補題はある程度汎用性があるならば、予め切り出して証明しておいた方が良いと思いますが、
   使い捨て的な補題は assert を使うと、証明内証明みたいに作る事ができます。
   例えば下記の例で、
*)
Lemma Sample_of_assert : forall P Q, (P /\ P) -> (Q /\ Q) -> (P /\ Q).
Proof.
  intros P Q pp qq.
(*
   ここまで証明した段階で、forall X, X /\ X -> Xという補題があれば、
   ppからPを、qqからQを取り出せて便利そうだと考えました。
   そこでassertを使います。すると現在の証明課題より先に、
   まずこの補題が証明課題になります。
*)
  assert(H: forall X, X /\ X -> X).
  intros X xx.
  destruct xx as [x _].
  exact x.
(*
   assertで設定した補題 H の証明が終わると、以後は仮定 H としてそれを使う事が出来ます。
*)
  split.
  apply (H P).
  exact pp.
  apply (H Q).
  exact qq.
Qed.


(* 8/25 intro *)
(*
   基本的には前に説明したintrosと同じで、introsと違って一度に１つしかintro出来ないのが違います。
   あと、introsと違ってintroの場合は、
   ~Pの形のゴールを、Pという仮定と、Falseというゴールに変形出来ます。
   ~PはP->Falseなのですが、intros.では~Pは~Pのままです。
*)


Lemma Sample_of_intro : forall P, ~~~P -> ~P.
Proof.
  intro P.
  intro nnnp.
  intro p.
  elim nnnp.
  intro np.
  elim np.
  exact p.
Qed.


(* 9/25 simpl *)
(*
   simpl はβι簡約(beta, iota)をして式を簡単にします。
   βι簡約が何かについては「言語ゲーム」の記事が判りやすいです。
   β簡約は関数適用で、ι簡約だと再帰的に関数が適用される、と考えると良いです。


   予め、足し算の定義を示しておきます。plus を含んだ式を simpl すると、
   一つ目の変数 n について再帰的にパターンマッチして式を変形してくれます。
*)
Print plus.
(* 足し算を使った simpl の使用例です。 *)
Lemma Sample_of_simpl : forall n m, n + m = m + n.
Proof.
  intros n m.
  induction n.
  simpl.
(*
   simpl を使うと左辺の0 + mがnに簡約されますが、右辺は変化がありません。
   ここは別途証明しておいた（というか標準ライブラリにはいっている）
   定理のplus_n_Oを使って書き換える事にします。
*)
  Check plus_n_O.
  erewrite <- plus_n_O.
  reflexivity.


(* 帰納法の後半も simpl を使い、別の補題plus_n_Smを使います。*)
  Check plus_n_Sm.
  erewrite <- plus_n_Sm.
  erewrite <- IHn.
  reflexivity.
Qed.


(* 10/25 unfold *)
(*
   unfold は関数定義を展開します。
   unfold だけで使う場合も有りますが、fold と組み合わせて使う事もあります。
   fold は展開された関数を元に戻します。
   unfold して、simpl とか rewrite とかして、
   また fold して戻すと式が良い具合に変形されている場合があります。
   ここではそういう例を見てみましょう。
*)
(* まず、sum n := 1 + 2 + ... + nという関数を定義します。*)


Fixpoint sum n :=
  match n with
    | O => O
    | S n' => S n' + sum n'
  end.


(*
   次に、sum n = 1/2 * n * (n + 1) であることを証明したいのですが、
   割り算が入ると面倒ですから、次の定理を証明する事にします。
   今回は環に関する自動証明器の ring を使いたいのでArithとRingをImportしておきます。
   nに関する帰納法で、n=0の場合はさらっと証明を流すことにします。
*)
Require Import Arith Ring.
Lemma Sample_of_unfold : forall n, 2 * sum n = n * (n + 1).
Proof.
  induction n.
  reflexivity.
  (*
     ここで、sum を unfold して、fold すると式が少し変形されます。
     *)
  unfold sum.
  fold sum.
  (*
     ここでreplaceを使ってちょっと左辺を書き換えます。書き換えて良い証明はsubgoal 2と後回しです。
     *)
  replace (2 * (S n + sum n)) with (2 * S n + 2 * sum n).
  (*
     ここでIHnを用いて書き換えて式変形を ring で自動証明します。後回しにしたものもringで一発です。
     *)
  rewrite IHn.
  ring.
  ring.
Qed.


(* 11/25 exists *)
(*
   証明のゴールが exists x, P x とか { n:nat | isPrime n } とか、
   ある性質を満たす要素が存在することを求めている時に、
   「具体的に」その要素を与えてゴールを変形します。


   下記は exists を使う簡単な例です。
   mの具体的な値としてS n = n+1 を与えています。
   具体的なmを何か与えないとomegaでの自動証明は通りません。
*)


Lemma Sample_of_exists : forall n, exists m, n < m.
Proof.
  intros.
  exists (S n).
  omega.
Qed.


(* 12/25 replace *)
(*
   Coq でよく使われる tactic の12番目は replace です。
   replace t1 with t2 とすると、t2 = t1 という等式をsubgoalに追加し、
   t2 = t1 を用いてゴールの書き換えを行います。
   書き換え規則 t2 = t1 の証明を先送りにすることで本筋の証明の見通しがよくなります。
   また、simpl, unfold, rewriteを使う場合とかで、
   「ゴールのこの部分だけ書き換えたいのだが別のところも書き換えられてしまう」
   と悩む場面もありますが、
   そういうときは replace でとりあえず部分的に書き換え、
   あとでその箇所の書き換えを証明すると楽です。
   replace を多用するのは、等式変形を繰り返す場合です。今回はそういう例を。
*)


(* 下記の様に群 G を定義してみます。 *)


Axiom G : Set.                                           (* 群G *)
Axiom G_dec : forall a b:G, {a=b} + {a <> b}.            (* 単位元や逆元の一意性とかを示す時に必要 *)
Axiom mult : G -> G -> G.                                (* 乗法 *)
Notation "a * b" := (mult a b).                          (* 記号 * で書ける様にする *)
Axiom assoc : forall a b c:G, (a * b) * c = a * (b * c). (* 結合則 *)
Axiom G1 : G.                                            (* 単位元 *)
Notation "1" := G1.                                      (* 記号 1 で書ける様にする *)
Axiom id_l : forall a:G, 1 * a = a.                      (* 左単位元である *)
Axiom inv : G -> G.                                      (* 逆元 *)
Axiom inv_l : forall a:G, (inv a) * a = 1.               (* 左逆元 *)


(*
   では、左逆元は右逆元でもあることを証明してみます。
   長くなるのでゴールを示すのは要所要所だけです。
   replaceを使うと、subgoalが増えているのが判ります。
*)


Theorem inv_r : forall a:G, a * (inv a) = 1.
Proof.
  intros.
  replace (a * inv a) with (1 * a * inv a) .
  replace (1 * a * inv a) with (inv (inv a) * inv a * a * inv a) .
  replace (inv (inv a) * inv a * a * inv a) with
    (inv (inv a) * (inv a * a) * inv a) .
  rewrite inv_l.                            (* ここからは replace を使わなくても
                                               rewrite で簡単に変形出来る *)
  rewrite assoc.
  rewrite id_l.
  rewrite inv_l.
  reflexivity.                              (* メインゴールの証明完了。
                                               残りは replace の書き換えの証明 *)
  rewrite <- assoc; reflexivity.
  erewrite inv_l; reflexivity.
  rewrite assoc; rewrite id_l; reflexivity.
Qed.


(* 13/25 induction *)
(*
   Coq は帰納的な型を定義すると、その型に対する帰納法を自動で定義してくれます。
   例えば


   Inductive nat : Set :=
   | O : nat
   | S : nat -> nat.


   という自然数natに対して、


   forall P : nat -> Prop,
   P 0 ->
   (forall n : nat, P n -> P (S n)) ->
   forall n : nat, P n


   というnat_indを定義してくれます。
   これを使って、自然数nについての帰納法の証明の時に、


   ・n=0 の場合のゴール
   ・nの時成り立つという仮定IHnと、S nの場合のゴール


   を作ってくれます。同様にリストであれば、nilとconsの場合などです。
   今までにも何度か induction を使った証明を示してきましたが、今回も簡単な例を。
*)


Lemma plus_comm : forall n m, n + m = m + n.
Proof.
  induction n.
  intro m.
  simpl.
  erewrite <- plus_n_O.
  reflexivity.
  intro m.
  simpl.
  erewrite <- plus_n_Sm.
  erewrite IHn.
  reflexivity.
Qed.


(* 14/25 split *)
(*
   split はゴールが P /\ Q の形をしている時に、
   二つのゴール P, Q に分割します。あとはそれぞれを別々に証明すればOKです。
*)


Lemma Sample_of_split : forall A B C:Prop, A /\ (B /\ C) -> (A /\ B) /\ C.
Proof.
  intros A B C abc.
  destruct abc as [a [b c]].
  split.
  split.
  assumption.
  assumption.
  assumption.
Qed.


(* 15/25 case *)
(*
   帰納的な型について自動で場合分けをしてくれるという意味では、13番目のinductionと同じですが、
   inductionと違って単に場合分けを行うだけで帰納法の仮定とかは作ってくれません。


   今回は３値論理を定義してみます。帰納的な bool3 という型を定義し、
   それらに対する否定、論理積、論理和を定義します。
*)
Inductive bool3 : Set := yes | maybe | no.
Definition not3(b:bool3) :=
  match b with
    | yes => no
    | maybe => maybe
    | no => yes
  end.


Definition and3(a b:bool3) :=
  match a,b with
    | yes,yes => yes
    | no, _ => no
    | _, no => no
    | _,_ => maybe
  end.


Definition or3(a b:bool3) :=
  match a,b with
    | no,no => no
    | yes,_ => yes
    | _,yes => yes
    | _,_ => maybe
  end.


(*
   では、bool3 における簡単な証明をしてみます。
   a, b についての場合分けを行うのに case タクティックを使用します。
   下記の例では case でゴールが増えるのを示したいので個別に case を使っていますが、
   普通は、
   case a; case b; reflexivity.
   で一行で９通りの場合分けを実施して終了とするでしょう。
*)
Lemma Sample_of_case : forall a b:bool3,
  not3 (or3 a b) = and3 (not3 a) (not3 b).
Proof.
  intros a b.
  case a.
  case b.
  reflexivity.
  reflexivity.
  reflexivity.
  case b; reflexivity.
  case b; reflexivity.
Qed.




(* 16/25 ring *)
(*
   ring は可換な半環（演算 +, * があって、それぞれ単位元 0, 1 があって、
   それぞれ交換則と結合則が成り立って、分配法則があってな数学的構造）
   での計算を行ってくれます。
   基本的には多項式の掛け算を展開し、標準形に直して比較するようなことをします。
   使用するにはRequire Import Ring.が必要です。
   下記で色々試してみましたが、適宜 rewrite, replace なども併用しないとうまくいきませんでした。
*)


Require Import ZArith Ring.
Open Scope Z_scope.
Lemma Sample_of_ring : forall a b:Z, a + b = 7 -> a * b = 12 -> a^2 + b^2 = 25.
Proof.
  intros a b H1 H2.
  replace (a^2 + b^2) with ((a+b)^2 - 2*a*b) by ring.
  rewrite H1.
  replace (2*a*b) with (2*12) by ring [H2].
  reflexivity.
Qed.
Close Scope Z_scope.


(* 17/25 elim *)
(*
   elim はほとんど induction と同じ事が出来ます。
   例えばこんな感じ。帰納法の仮定を自分で intro する必要があるのが違います。
*)


Lemma Sample_of_elim : forall n, n + 0 = n.
Proof.  
  intros.
  elim n.
Abort.


(*
   ただこうやって帰納法で使うときはinductionする方が多い様にも思います。
   下記の様にゴールが False で、仮定が ~P の形をしている時は、
   私は習慣で他のタクティックではなく elim を使います。こんな感じ。
   *)


Lemma Sample_of_elim' : forall P, ~~(P \/ ~P).
Proof.
  intros.
  intro npnp.
  elim npnp.
  right.
  intro p.
  elim npnp.
  left.
  exact p.
Qed.


(* 18/25 clear *)
(*
   clear Hとすると、仮定 H が消えます。下記の様な感じです。
*)


Lemma Sample_of_clear : forall A B C, (A->B->C)->(A->B)->A->C.
Proof.
  intros A B C abc ab a.
  apply abc; clear abc.
  exact a.
  apply ab; clear ab.
  exact a.
Qed.


(*
   使い終わって不要になった仮定をclearで消すと多少見通しが良くなる事もありますが、
   あまり使わないのではないかなぁ。
   むしろ、各種 tactic の中で内部的に使われる事が多い様な気がします。
   例えば下記の簡単な tactic の swap の中で使われています。
   apply して一回使った仮定は不要なので clear で消しているようです。
*)


Ltac swap H := 
  idtac "swap is OBSOLETE: use contradict instead.";
  intro; apply H; clear H.


(* これを使った証明です。*)


Lemma Sample_of_claer : forall P, ~~~P -> ~P.
Proof.
  intros.
  swap H.
  swap ipattern:H.
  exact H0.
Qed.


(* 19/25 inversion *)
(*
   inversion は仮定に対して帰納的な定義を適用し、その仮定が成立する為の前提を導き出すか、
   あるいはそもそもそのような前提が存在しない（＝仮定が間違っている）ので証明終了、
   を導いてくれます。
   ある種の証明では inversion を使うと証明が非常に簡単なのですが、
   中で何をしているのかは簡単には説明するのは難しいです。
*)


(* inversionの使用例というと典型的にはこの関数を定義することになっています。*)
Inductive even : nat -> Prop :=
| EvenO : even O
| EvenSS : forall n, even n -> even (S (S n)).


(*
   偶数である事を、上記の様に帰納的に定義します。
   では３が偶数でない事を証明しましょう。
   こういう定理の証明の時にはinversionが有用です。
   今回はinversionの中で何をしているかみたいのでinfo inversionとして使っています。
*)


Lemma Sample_of_inversion : ~(even 3).
Proof.
  intro.
  info inversion H.
(* H: even 3の前提にH1: even 1が前提である事が判りました。
   このH1について再度inversionを使います。 *)
  info inversion H1.
Qed.
(* H1を成立させる前提が無いので、証明完了になります。*)


(* あと、inversionが役に立つ例というとsmall-stepの決定性の証明とかです。*)
Inductive term : Set :=
| TmTrue : term
| TmFalse : term
| TmIf : term -> term -> term -> term.


Inductive eval : term -> term -> Prop :=
| EvIfTrue : forall t2 t3, eval (TmIf TmTrue t2 t3) t2 
| EvIfFalse : forall t2 t3, eval (TmIf TmFalse t2 t3) t3
| EvIf : forall t1 t1' t2 t3, eval t1 t1' ->
  eval (TmIf t1 t2 t3) (TmIf t1' t2 t3).


(* 上記の様にsmall-stepの規則を定義して、下記を証明します。*)


Theorem eval_deterministic : forall t t' t'', (eval t t') -> (eval t t'') -> (t' = t'').
Proof.
  intros t t' t'' tEt' tEt''.
  
  (* まず tEt' について induction で場合分けをします。*)
  induction tEt' as [t2 t3|t2 t3|t1 t1' t2 t3 t1Et1'] in t'', tEt'' |-*.
  (*
     最初の場合は、t' = TmIf TmTrue t2 t3 の場合です。
     ここで tEt'' については induction ではなくinversion を使うと、
     tEt'' が成立するような t'' の場合分けを自動で行ってくれます。
     *)
  inversion tEt'' as [t2_ t3_| t2_ t3_| t1_ t1'_ t2_ t3_ t1Et1'_].
  reflexivity.
  (*
     ここでinversion t1Et1'_を行います。
     TmTrueが何かにevalされる規則はevalに無いので、仮定が不成立となり、
     goalの証明が終わります。
     *)
  inversion t1Et1'_.
  
  (* t' = TmIfFalse t2 t3 の場合は同様の証明をすればOKです。*)
  inversion tEt'' as [t2_ t3_| t2_ t3_| t1_ t1'_ t2_ t3_ t1Et1'_].
  reflexivity.
  inversion t1Et1'_.
  
  (*
     最後は、t' = TmIf t1 t2 t3 の場合についてです。
     やはりtEt''についてinversionします。
     *)
  inversion tEt'' as [t2_ t3_| t2_ t3_| t1_ t1'_ t2_ t3_ t1Et1'_].
  (*
   ここでも、H0とt1Et1'から、eval TmTrue t1'を作って
   inversionして仮定が成立しない事を使って証明します。
   *)
  rewrite <- H0 in t1Et1'.
  inversion t1Et1'.


  (* 同様にして、TmFalse の場合も証明出来ます。*)
  rewrite <- H0 in t1Et1'.
  inversion t1Et1'.
  
  (* 最後はIHt1Et1'のt''をt1'_にして、t1Et1'_と組み合わせてゴールを導きます。*)
  rewrite (IHt1Et1' t1'_ t1Et1'_).
  reflexivity.
Qed.


(* 20/25 generalize *)
(*
   generalize は intro の逆で、具体的な値の term を、"forall t" のような形に戻します。
   簡単な使用例は下記の様なものです。
*)
Lemma sample_of_generalize : forall x y, 0 <= x + y + y.
Proof.
  intros.
  generalize (x + y + y).
  Require Import Arith.Le.
  apply le_O_n.
Qed.


(*
   単純に generalize で戻せない場合は、generalize dependent t のような形で使います。
   例えば下記の証明（TAPLの練習問題の証明）で使っています。
   よほど明らかな場合以外は、generalize dependentの形で使う事が多い様に思います。
   まず証明の前提の定義を幾つか。
*)
Inductive term2 : Set :=
| Tm2True : term2
| Tm2False : term2
| Tm2If : term2 -> term2 -> term2 -> term2
| Tm2Zero : term2
| Tm2Succ : term2 -> term2
| Tm2Pred : term2 -> term2
| Tm2Iszero : term2 -> term2.


Inductive nvalue : term2 -> Prop :=
| NvZero : nvalue Tm2Zero
| NvSucc : forall t, nvalue t -> nvalue (Tm2Succ t).


Inductive bvalue : term2 -> Prop :=
| BvTrue : bvalue Tm2True
| BvFalse : bvalue Tm2False.


Definition value(t:term2) : Prop := bvalue t \/ nvalue t.


Inductive eval2 : term2 -> term2 -> Prop :=
| Ev2IfTrue : forall t2 t3, eval2 (Tm2If Tm2True t2 t3) t2
| Ev2IfFalse : forall t2 t3, eval2 (Tm2If Tm2False t2 t3) t3
| Ev2If : forall t1 t1' t2 t3, eval2 t1 t1' -> eval2 (Tm2If t1 t2 t3) (Tm2If t1' t2 t3)
| Ev2Succ : forall t1 t1', eval2 t1 t1' -> eval2 (Tm2Succ t1) (Tm2Succ t1')
| Ev2Pred : forall t1 t1', eval2 t1 t1' -> eval2 (Tm2Pred t1) (Tm2Pred t1')
| Ev2PredZero : eval2 (Tm2Pred Tm2Zero) Tm2Zero
| Ev2PredSucc : forall nv, nvalue nv -> eval2 (Tm2Pred (Tm2Succ nv)) nv
| Ev2IszeroZero : eval2 (Tm2Iszero Tm2Zero) Tm2True
| Ev2IszeroSucc : forall nv, nvalue nv -> eval2 (Tm2Iszero (Tm2Succ nv)) Tm2False
| Ev2Iszero : forall t1 t1', eval2 t1 t1' -> eval2 (Tm2Iszero t1) (Tm2Iszero t1').


Notation "t1 ---> t2" := (eval2 t1 t2) (at level 80, no associativity).


Definition normal_form (t : term2) : Prop := ~ exists t', eval2 t t'.


(* ここで下記の定理を証明します。
   intros を下記の様にすると予めdestructした形で intros 可能です。
*)
Lemma value_is_normal_form : forall v, value v -> normal_form v.
Proof.
  intros v [bv|nv] [t vEt].
  destruct bv; inversion vEt.
(*
   ここで t をgeneralize dependentします。
   （generalize t だと、forall t:term2, にならずうまくいかない。）
*)
  generalize dependent t.
  induction nv.
  intros t zEt.
  inversion zEt.
  intros t0 stEt0.
  inversion stEt0.
  elim (IHnv t1').
  exact H0.
Qed.


(* 21,22/25 left, right *)
(*
   left は constructor 1 、right は constructor 2 の意味で、
   実は goal が A \/ B の場合に限らず、
   コンストラクタが２通りあってどちらかを明示的に指定したい時に使えます。
   大抵そういう場合は左右と対応している訳ですが、例えば nat とかも left が O を指すはず。
   同様に n:nat に対して destruct n ではなく split とかも使えるはず。
   単に他人に判りにくいだけですが。
   
   今回は sumbool について left, right を使う例です。やはり左右に対応しています。
*)
Lemma Sample_of_left_right : forall n:nat, {n = 0} + {n <> 0}.
Proof.
  induction n.
  left.
  reflexivity.
  
  right.
  intro.
  inversion H.
Qed.


(* 23/25 specialize *)
(*
   公理とかライブラリにある定理とか証明済み補題とかに、
   特定の引数を適用した物を仮定に使いたい事があります。
   forall n, P n. みたいな補題Lのnに特定の値 n0 を代入した P n0 が仮定にあると良いなぁ、とか。
   勿論、assert(H:P n0)とかcut (P n0)とか書いても良いのですが、
   specialize (L n0). と書けば cut (P n0)してapply (L n0) するのと同じになり、
   証明が短く判りやすくなります。
   
   replaceの説明の時と同じ定理を、replaceを使わず、specializeとrewriteを使って証明してみます。
   証明の前提と成る公理は replace の回を参照して下さい。
*)
Theorem inv_r' : forall a:G, a * (inv a) = 1.
Proof.  
  intros.
  specialize (id_l (a * inv a)).
  (*
     specializeすると、公理 id_l に (a * inv a) を適用した物が得られますので、
     intro して書き換えて消去します。あとは同様に。
     *)
  intro H; rewrite <- H; clear H.
  specialize (inv_l (inv a)); intro H; rewrite <- H; clear H.
  specialize (assoc (inv (inv a)) (inv a) (a * inv a)); intro H; rewrite H; clear H.
  specialize (assoc (inv a) a (inv a)); intro H; rewrite <- H; clear H.
  specialize (inv_l a); intro H; rewrite H; clear H.
  specialize (id_l (inv a)); intro H; rewrite H; clear H.
  reflexivity.
Qed.


(* 24/25 exact *)
(*
   現在のゴールが、仮定のどれか、あるいは既存の定理にマッチする時に
   exact H?. とか exact my_theorem. とかするとゴールが証明されます。
   前者の場合は assumption. で済みますし、
   exact ではなく apply でもOKなんで、無理に使う必要は無いですが、
   ゴールと同じ物があったという意図を多少は示せるのかも。
   exact を使って書いてみました。
*)


Lemma Sample_of_exact : forall n m, n + m = m + n.
Proof.
  intros.
  induction n.
  simpl.
  exact (plus_n_O m).
  simpl.
  rewrite IHn.
  exact (plus_n_Sm m n).
Qed.


(* 25/25 reflexivity *)
(*
   reflexivity はゴールが等式で、左辺と右辺の値が等しい時に使います。
   内容的には apply refl_equal. と同じです。refl_equal はこんな公理。


Inductive eq (A : Type) (x : A) : A -> Prop :=  refl_equal : x = x.


   左辺と右辺が全く同じ形をしていないと等式は成り立ちません
   （が、reflexivity は内部的に simpl を実行しているので
   simpl で簡単化して等しくなる物は成立します）。
   
   ところで、同じ形というのはどこまで同じならば = が成り立つかというのは良く解らないので、
   色々試してみました。
*)


Definition f : nat -> nat := fun x => x.
Definition h : nat -> nat := fun y => y .
Goal f = h.
  simpl.
  unfold f.
  unfold h.
  reflexivity.
Qed.
(*
   これを見ると、(fun x : nat => x) = (fun y : nat => y) は成立するようです。同様に、
*)


Goal forall P:nat->Prop, (forall n, P n) = (forall m, P m).
  intros P.
  reflexivity.
Qed.
(*
   これを見ると、(forall n : nat, P n) = (forall m : nat, P m) も成立。
   上記の f, h の場合はreflexivityで等しい事が示せましたが、
   一般には関数が等しい事を reflexivity で証明する事は出来ません。
   
   f, g : nat -> nat について、f = g ⇔ ∀n:nat, f n = g n. を以て等しいとする場合は、
   こんな感じで証明します。
*)


Definition f' : nat -> nat := fun x => x.
Fixpoint g' (x:nat) : nat :=
  match x with
    | O => O
    | S n' => S (g' n')
  end.


Require Import Logic.FunctionalExtensionality.


Lemma Sample_of_reflexivity : f' = g'.
Proof.
  extensionality n.
  unfold f'.
  induction n.
  reflexivity.
  simpl.
  rewrite <- IHn.
  reflexivity.
Qed.


(*
   他にも、= を同値関係を以て定義する場合は Setoid というものを使って考える
   （Coqの型理論には集合論の商集合が無いので、代わりに = を同値関係で置き換えた物を使う）
   とか有るらしいのですが、そっちはちょっと調べきれませんでした。
*)


(* END *)