(**
http://www.a-k-r.org/d/2024-03.html#a2024_03_22_1
 *)
(**
#1 Coq/SSReflect の bigop とシグマ (Σ) についてCoq/SSReflect には
bigop というライブラリが入っていて、 総和の Σ などを表現できる。

\big[add/u]_(a <= i < b | P i) F i と書くと、 a 以上 b 未満の i につい
て、P i が真になるものに限定して、F i を add する (u は単位元で、b < a
なら結果は u になる)

「P i が真になるものに限定して」という条件を無視すれば、 学校で習った
シグマと同じである。 TeX で書くと \sum_{i=a}^{b} Fi である。

関数型言語的な表現としては、foldr, map, filter, index_iota で記述でき
る。 \big[add/u]_(a <= i < b | P i) F i = foldr add u (map F (filter P
(index_iota a b))) である。 (index_iota a b は、a 以上 b 未満の自然数
のリストを返す)
 *)
From mathcomp Require Import all_ssreflect.

Goal forall (T : Type) (add : T -> T -> T) u a b P F,
  \big[add/u]_(a <= i < b | P i) F i =
  foldr add u (map F (filter P (index_iota a b))).
  (* foldr add u [seq F i | i <- index_iota a b & P i] *)
Proof.
  move=> T add u a b P F.
  by rewrite foldrE big_map_id big_filter.
Qed.

(**
ちなみに、上記は右辺を左辺に (foldr ... を \big ... に) 書き換えて
証明しているが、 逆に左辺を右辺に書き換えて証明することもできなくはな
い。
 *)
Goal forall (T : Type) (add : T -> T -> T) u a b P F,
  \big[add/u]_(a <= i < b | P i) F i =
  foldr add u (map F (filter P (index_iota a b))).
  (* foldr add u [seq F i | i <- index_iota a b & P i] *)
Proof.
  move=> T add u a b P F.
  rewrite -big_filter.
  change (fun i : nat => BigBody i add true (F i)) with
    (fun i : nat => BigBody i add (predT (F i)) (F i)).
  by rewrite -big_map_id -foldrE.
Qed.

(**
ここで、big_map_id は条件のところが P (F i) という形でないと (右か
ら左に) 書き換えられないので、ゴールを change で変形している。 これは
かなり面倒くさいので、foldr 側に変形してから証明するのは厄介であり、
\big 側で証明するのが無難だと思った。

さて、範囲を a <= i < b という形式で与えたので、index_iota a b が使わ
れているが、 かわりに任意のリストを与えることもできて、それは
\big[add/u]_(i <- r | P i) F i と書く。
 *)
Goal forall (T : Type) (add : T -> T -> T) u (r : seq T) P F,
  \big[add/u]_(i <- r | P i) F i =
  foldr add u (map F (filter P r)).
  (* foldr add u [seq F i | i <- r & P i] *)
Proof.
  move=> T add u r P F.
  by rewrite foldrE big_map_id big_filter.
Qed.

(**
こうすれば index_iota は使わないことができるが、map と filter (相当)
の機能は残っている。 map は数学のシグマでも相当する機能があるのでそう
いうものだろうが、filter はどうなのだろうか。 もちろん、filter に与え
る述語として、常に真を返す述語を与えれば、filter は無視できるのだが、
リストを与える形式であれば利用者側で filter を呼び出せるので、そもそも
不要ともいえる。 なんでそんな機能を組み込んだのだろうか。

というわけで疑問は、なんで「P i が真になるものに限定して」という
filter の機能が入っているのだろうか、ということである。 学校で習ったシ
グマにはそういう機能はなかったと思うのだが。

検索すると、bigop の論文が見つかった: Canonical Big Operators

しかし、filter の機能をつけたということは書いてあるが、なぜつけたのか
は書いていないようだ。 ただ、例として \big[addn/0]_(i <= n | even i)
i^2 というのを書いてあるので、連続した範囲でないものを扱いたいのだろう
という気はする。

数学では、そういう書き方をするのだろうか。 Wikipedia:Summation をみる
と、 一般化された記法がよく使われる (Generalizations of this notation
are often used) と書いてある。 シグマの下に 0<=k<100, x∈S, d|n と書く
例が出ている。 0<=k<100 や x∈S は、よくある書き方だと思う。 最後の
d|n は、d が n を割り切る (n が d の倍数) という条件である。 これはちょっ
と見慣れないが、シグマの下には任意の命題を記述できて、その命題を成り立
たせる値それぞれについて加算すると思えば、0<=k<100 や x∈S と同種の書
き方と考えられるか。

あと、Wikipedia には、Concrete Mathematics: A Foundation for Computer
Science に Chapter 2: Sums という章があるという脚注がある。 一章まるご
と総和の話なのだろうか。

filter の機能が役に立つのか、ちょっと考えてみよう。 たとえば、同じ総和
で、奇数という条件がついたものと、偶数という条件がついたものを加算する
と、条件がついていない総和と等しくなるだろう。 証明してみよう。 なお、
SSReflect に標準で提供されているのは偶数で真になる even じゃなくて、奇
数で真になる odd なので、そっちを使う。
 *)
Goal forall a b F,
  \sum_(a <= i < b | odd i) F i +
  \sum_(a <= i < b | ~~ odd i) F i =
  \sum_(a <= i < b) F i.
Proof.
  move=> a b F.
  elim: b a.
  - move=> a.
    by do 3 (rewrite big_geq; last by []).
  - move=> b IH a.
    case: (boolP (a <= b)); last first.
    + rewrite -ltnNge => ltn_ba.
      by do 3 (rewrite big_geq; last by []).
    + move=> leq_ab.
(*
  rewrite [\sum_(a <= i < b.+1 | odd i) F i](@BigBody _ _ _ _ _ _ b) => //; [|exact addnA|exact addnC].
  rewrite [\sum_(a <= i < b.+1 | odd i) F i](@big_cat_nat_idem _ _ _ _ _ _ b) => //; [|exact addnA|exact addnC].
  rewrite [in \sum_(b <= i < b.+1 | odd i) F i]/index_iota subSnn /=.
  rewrite [in \sum_(i <- [:: b] | odd i) F i]unlock /= addn0.
  rewrite [\sum_(a <= i < b.+1 | ~~ odd i) F i](@big_cat_nat_idem _ _ _ _ _ _ b) => //; [|exact addnA|exact addnC].
  rewrite [in \sum_(b <= i < b.+1 | ~~ odd i) F i]/index_iota subSnn /=.
  rewrite [in \sum_(i <- [:: b] | ~~ odd i) F i]unlock /= addn0.
  rewrite big_nat_recr /=; last by [].
  rewrite -IH.
  by case: (odd b) => /=; ring.
Qed.
 *)
Admitted.

(**
うぅむ、予想外に面倒くさい。 そもそも、filter の条件の論理和に関す
る補題が見当たらないので、帰納法を使う必要があるし、IH を使えるように
する書き換えも面倒くさい。

でも、書き換えが面倒くさいのは、 a <= i < b という形で範囲を与えるから
で、一般化してリストを与えればもっと簡単ではないか、ということでやりな
おし。 (index_iota a b という特定の形のリストじゃなくて任意のリストを
扱う、ということ)
 *)
Goal forall r F,
  \sum_(i <- r | odd i) F i +
  \sum_(i <- r | ~~ odd i) F i =
  \sum_(i <- r) F i.
Proof.
  move=> r F.
  elim: r.
  - by rewrite 3!big_nil.
  - move=> x r IH.
    rewrite 3!big_cons -IH.
    by case: (odd x) => /=; ring.
Qed.

(**
お、簡単になった。

せっかくなので、対象を自然数に限定しない一般化をしてみよう。 fold に与
える演算が associative, commutative でないといけないし、単位元も必要な
ので、 そういう証明がついている演算として、 T -> T -> T じゃなくて、
Monoid.com_law idx を使う (idx が単位元である)
 *)
Goal forall (T : Type) (idx : T) (op : Monoid.com_law idx) (P : pred T) F r,
  op (\big[op/idx]_(j <- r | P j) F j)
     (\big[op/idx]_(j <- r | ~~ P j) F j) =
  \big[op/idx]_(j <- r) F j.
Proof.
  move=> T idx op P F.
  elim.
  - rewrite 3!big_nil.
    by rewrite Monoid.mul1m.
  - move=> x r IH.
    rewrite 3!big_cons -IH.
    case: (P x) => /=.
    + by rewrite Monoid.mulmA.
    + rewrite Monoid.mulmA.
      Fail rewrite [op _ (F x)]Monoid.mulmC.
      Check (SemiGroup.Law.sort (Monoid_ComLaw__to__SemiGroup_Law op) _ (F x)).
      rewrite [(SemiGroup.Law.sort (Monoid_ComLaw__to__SemiGroup_Law op) _ (F x))]Monoid.mulmC.
      by rewrite Monoid.mulmA.
Qed.

(**
最後の部分は、ring を使えなくて、変形を自分でやる必要があった。
Monoid の場合の rewrite は Monoid.mulmA とかを使えるのだな。初めて使っ
た。

P j と ~~ P j というのも具体的すぎるので、単に異なる述語 P, Q と一般化
してみよう。 この場合、P j と Q j が両方とも真になると成り立たないので、
述語の intersection が空ということで、predI P Q =1 pred0 という前提を
追加する。 これ以上の一般化は思いつかないので、big_filter_or と名前を
つけることにする。

あと、何回も Monoid. と書くのは面倒くさいので Import しよう。
 *)
Import Monoid.

Lemma big_filter_or (T : Type) (idx : T) (op : Monoid.com_law idx) (P Q : pred T) F r:
  predI P Q =1 pred0 ->
  op (\big[op/idx]_(j <- r | P j) F j)
     (\big[op/idx]_(j <- r | Q j) F j) =
  \big[op/idx]_(j <- r | predU P Q j) F j.
Proof.
  move=> PQ0.
  elim: r.
  - rewrite 3!big_nil.
    by rewrite mul1m.
  - move=> x r IH.
    rewrite 3!big_cons -IH.
    move: (PQ0 x) => /=.
    case: (P x); case: (Q x) => //= _.
    + by rewrite mulmA.
    + by rewrite mulmA [(SemiGroup.Law.sort (Monoid_ComLaw__to__SemiGroup_Law op) _ (F x))]mulmC mulmA.
Qed.

(**
まぁ、ほぼ同じくらいの証明になった。Import したぶん短くなっているか
な。

最後の部分は、P x と Q x の両方で場合分けするので、4種類になるのだが、
2種類は自明に証明されるので、手動でやらないといけないのは残り 2つで、
それらは P j と ~~ P j のときと同じ形だった。

big_filter_or を使って、最初の、奇数限定と偶数限定を足すと無条件になる、
というのを証明してみる。
 *)
Goal forall a b F,
  \sum_(a <= i < b | odd i) F i +
  \sum_(a <= i < b | ~~ odd i) F i =
  \sum_(a <= i < b) F i.
Proof.
  move=> a b F.
  rewrite big_filter_or /=.
  
  (* 多くの場合、apply: でもよいが、最後の例はunderが必須。 *)
  
  - apply: eq_bigl => x.
    by rewrite orbN.
    Undo 2.
    
    under eq_bigl => x.
    + rewrite orbN.
      over.
    + by [].
  - move=> x /=.
    by rewrite andbN.
Qed.

(**
うまく証明できた。

証明の中で、 \sum_(a <= j < b | odd j || ~~ odd j) F j の中の odd j ||
~~ odd j を書き換えるのに under tactic を使っている。

odd j || ~~ odd j を true に書き換えるのは orbN でいいのだが、 j はゴー
ルの中で束縛されているので、そのままでは書き換えられない。

この場合は、under tactic を使うと 中身を書き換えられる。 (補題が必要に
なるので、ここでは eq_bigl を使っている) under tactic はサブゴールを作っ
てくれて、ユーザがサブゴールを書き換えた後に over とすると、書き換えた
結果を元のゴールに反映してくれる。 サブゴールは証明しないというのがな
かなか奇妙というか面白い。

under tactic には Interactive mode と One-liner mode があって、上は変
形を見ながらやりたかったので Interactive mode を使っているが、 まぁ、
変形は rewrite orbN だけなので、One-liner mode で十分で、そうすると以
下のように書ける。
 *)
Goal forall a b F,
  \sum_(a <= i < b | odd i) F i +
  \sum_(a <= i < b | ~~ odd i) F i =
  \sum_(a <= i < b) F i.
Proof.
  move=> a b F.
  rewrite big_filter_or /=.
  - apply: eq_bigl => x.
    by rewrite orbN.

  Undo 2.
  - under eq_bigl => x.
    + rewrite orbN.
      over.
    + done.
      
  Undo 6.
  - by under eq_bigl => x do rewrite orbN.

  - move=> x /=.
    by rewrite andbN.
Qed.

(**
短くてよろしい。

なお、今回の場合は、under tactic を使わなくても、apply eq_bigl だけでも十分ではあった。
*)
Goal forall a b F,
  \sum_(a <= i < b | odd i) F i +
  \sum_(a <= i < b | ~~ odd i) F i =
  \sum_(a <= i < b) F i.
Proof.
  move=> a b F.
  rewrite big_filter_or /=.
  - apply eq_bigl => x /=.
    by rewrite orbN.
  - move=> x /=.
    by rewrite andbN.
Qed.

(**
under tactic が便利なのは、\sum みたいなのが、部分式に現れるときと
か、 そのまま apply eq_bigl とはできないときかな。
 *)
Goal forall a b F,
  (\sum_(a <= i < b | odd i) F i +
   \sum_(a <= i < b | ~~ odd i) F i) + 3 =
  (\sum_(a <= i < b) F i) + 3.
Proof.
  move=> a b F.
  rewrite big_filter_or /=.
  
  (* ここは、apply: eq_bigl はできない。 *)
  
  - under eq_bigl => x.
    + rewrite orbN.
      over.
    + done.
    Undo 6.
    by under eq_bigl => x do rewrite orbN.

  - move=> x /=.
    by rewrite andbN.
Qed.

(**
ここでは、+ 3 というのがついているので、apply eq_bigl はできなくて、 under eq_bigl を使っている。
 *)

(* END *)
