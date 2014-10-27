(**
正規表現の言語を定義して、次の文献にある例を実行してみた。
文献[1]：Tukuba Coq Users' Grup 「Coqによる定理証明」
坂口さん著「反復定理で遊ぼう」

実装にあたっては、
文献[2]: https://www.ps.uni-saarland.de/~doczkal/regular/
を参考にしているが、そのパッケージは使用しない。
 *)

Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq fintype finset.

(** 定義 1.1
語は文字のseqで表す。
 *)
Variable char : finType.                    (* アルファベットΣ *)
Variables a b c : char.                     (* 文字 *)
Variables w : seq char.                     (* 語 *)

(** 定義 1.2
正規表現
 *)
Inductive regexp :=
 | Void              : regexp
 | Eps               : regexp
 | Atom (a : char)   : regexp
 | Plus (e1 e2 : regexp) : regexp
 | Conc (e1 e2 : regexp) : regexp
 | Star (e : regexp) : regexp.

Check Void.
Check Eps.

(* 例 1.3
正規表現
*)
Check (Conc (Conc (Star (Atom a))
                  (Plus (Atom b) (Atom c)))
            (Star (Star (Atom a)))).

(** 定義 1.5
正規表現の言語
*)
(**
決定性言語を「与えられた語が、その言語に含まれるか」を示す述語として定義する。
*)
Definition dlang := pred (seq char).        (* 決定性言語の集合 *)
Variables L1 L2 : dlang.                    (* ひとつの言語 *)

(**
言語の演算
 *)
Definition void : dlang := pred0.           (* 語を含まない言語 *)
Definition eps : dlang := pred1 [::].       (* 空の語だけを含む言語 *)
Definition atom x : dlang := pred1 [:: x].  (* 一文字の語だけを含む言語 *)
Definition plus (L1 L2 : dlang) :=          (* 言語の和 *)
  [pred w | L1 w || L2 w].
Definition conc (L1 L2: dlang) : dlang :=   (* 言語の積、語の畳込 *)
  fun v => [exists i : 'I_(size v).+1, L1 (take i v) && L2 (drop i v)].
Definition residual (x : char) (L : dlang) := [pred w | L (x :: w)].
Definition star (L : dlang) : dlang :=      (* クリーネ閉包 *)
  fix star v := if v is x :: v' then conc (residual x L) star v' else true.

(* 以下は、正規表現の言語の定義には不要だが *)
Definition compl L : dlang := predC L.      (* 言語の補集合 *)
Definition prod (L1 L2 : dlang) :=          (* 言語の積、語の積 *)
  [pred w in L1 | L2 w].

(**
正規表現の言語
与えられた正規表現に対して、それに対応する語を含む言語
（その語に対してtrueを返す論理式）を返す。
 *)
Fixpoint re_lang (e : regexp) : dlang :=
  match e with
  | Void => void
  | Eps => eps
  | Atom x => atom x
  | Star e1 => star (re_lang e1)
  | Plus e1 e2 => plus (re_lang e1) (re_lang e2)
  | Conc e1 e2 => conc (re_lang e1) (re_lang e2)
  end.

Lemma re_void__lang_none :
  forall (w : seq char), ~~ (re_lang Void w).
Proof.
  move=> w.
  rewrite /re_lang /void.
  by [].
Qed.

Lemma re_eps__lang_null : re_lang Eps [::].
Proof.
  rewrite /re_lang /eps.
  by [].
Qed.

Lemma re_atom__lang_atom : 
  forall (a : char), re_lang (Atom a) [:: a].
Proof.
  rewrite /re_lang /atom /= => a.
  by [].
Qed.

Lemma re_plus__lang_or :
  forall (e1 e2 : regexp) (w : seq char),
    re_lang e1 w || re_lang e2 w ->
    re_lang (Plus e1 e2) w.
Proof.
  move=> e1 e2 w.
  rewrite /re_lang /=.
  case/orP => H.
    by apply/orP; left.
    by apply/orP; right.
Qed.

Goal forall (L1 L2 : dlang) (w : seq char) (i : 'I_(size w).+1),
    L1 (take i w) -> L2 (drop i w) -> (conc L1 L2) w.
Proof.
  move=> L1 L2 w i H1 H2.
  rewrite /conc.
  apply/existsP.
  exists i.
  by apply/andP; split.
Qed.  
    
Lemma re_cons__lang_take_drop :
  forall (e1 e2 : regexp) (w : seq char) (i : 'I_(size w).+1),
    re_lang e1 (take i w) ->
    re_lang e2 (drop i w) ->
    re_lang (Conc e1 e2) w.
Proof.
  rewrite /re_lang /conc.
  move=> e1 e2 w i L1 L2.
  apply/existsP.
  exists i.
  apply/andP; split.
  by apply L1.
  by apply L2.
Qed.

(**
文献[2]で証明されている補題たち。一部を修正した。
*)
Lemma concP {L1 L2 : dlang} {w : seq char} :
  reflect (exists w1 w2, w = w1 ++ w2 /\ L1 w1  /\ L2 w2) (conc L1 L2 w).
Proof.
  apply: (iffP existsP) => [[n] /andP [H1 H2] | [w1] [w2] [e [H1 H2]]].
  - exists (take n w). exists (drop n w).
             by rewrite cat_take_drop.
  - have lt_w1: size w1 < (size w).+1 by rewrite e size_cat ltnS leq_addr.
    exists (Ordinal lt_w1); subst.
    rewrite take_size_cat // drop_size_cat //. exact/andP.
Qed.
(*
使わない：
Lemma plusP r s w :
  reflect (w \in r \/ w \in s) (w \in plus r s).
Proof. rewrite !inE. exact: orP. Qed.

Lemma conc_cat w1 w2 L1 L2 : w1 \in L1 -> w2 \in L2 -> w1 ++ w2 \in conc L1 L2.
Proof. move => H1 H2. apply/concP. exists w1. by exists w2. Qed.

Lemma conc_eq (l1: dlang) l2 l3 l4: l1 =i l2 -> l3 =i l4 -> conc l1 l3 =i conc l2 l4.
Proof.
  move => H1 H2 w. apply: eq_existsb => n.
  by rewrite (_ : l1 =1 l2) // (_ : l3 =1 l4).
Qed.

Lemma star_eq (L1 : dlang) (L2 : dlang) :
  L1 =i L2 -> star L1 =i star L2.
Proof.
  move => H1 w. apply/starP/starP; move => [] vv H3 H4; exists vv => //;
  erewrite eq_all; try eexact H3; move => x /=; by rewrite ?H1 // -?H1.
Qed.
*)

Lemma starP : forall {L v},
  reflect (exists2 vv, all [predD L & eps] vv & v = flatten vv) (star L v).
Proof.
  move=> L v.
  elim: {v}_.+1 {-2}v (ltnSn (size v)) => // n IHn [|x v] /= le_v_n.
  - by left; exists [::].
  - apply: (iffP concP) => [[u] [v'] [def_v [Lxu starLv']] | [[|[|y u] vv] //=]].
    case/IHn: starLv' => [|vv Lvv def_v'].
    + by rewrite -ltnS (leq_trans _ le_v_n) // def_v size_cat !ltnS leq_addl.
    + by exists ((x :: u) :: vv); [exact/andP | rewrite def_v def_v'].
    + case/andP=> Lyu Lvv [def_x def_v]; exists u. exists (flatten vv).
      subst. split => //; split => //. apply/IHn; last by exists vv.
      by rewrite -ltnS (leq_trans _ le_v_n) // size_cat !ltnS leq_addl.
Qed.

Lemma star_cat (w1 w2 : seq char) (L : dlang) :
  L w1 -> star L w2 -> star L (w1 ++ w2).
Proof.
  case: w1 => [|a w1] // H1 /starP [vv Ha Hf].
  apply/starP.
  exists ((a::w1) :: vv).
  - rewrite /=.
    apply/andP; split.
    + by apply H1.
    + by apply Ha.
  - by rewrite Hf //= H1.
Qed.

Fixpoint rep (s : seq char) n : seq char :=
  if n is n'.+1 then
    s ++ rep s n'
  else
    [::].
(*
Lemma rep_nil n : rep [::] n = [::].
Proof.
  elim: n.
  - by [].
  - move=> n IHn /=.
    by [].
Qed.
*)
Lemma star_rep : forall (L1 : dlang) (w : seq char) (n : nat),
       L1 w -> (star L1) (rep w n).
Proof.
  move=> L1 w.
  elim.                                     (* elim by n *)
  - move=> H1 /=.                           (* n = 0 *)
    by [].
  - move=> n IHn H1 /=.                     (* n = n + 1 *)
    apply star_cat.
    + by [].
    + by apply IHn.
Qed.

Lemma re_star__lang_star :
  forall (e : regexp)  (w : seq char) (n : nat),
    re_lang e w ->
    re_lang (Star e) (rep w n).
Proof.
  move=> e w n.
  elim: n.
  - by [].
  - move=> n /= IHn => H.
    apply star_cat.
    + by [].
    + by apply IHn.
Qed.

(** 例 1.6
正規表現の言語
*)

Lemma size_rep_one a n :
  size (rep [:: a] n) = n.
Proof.
  elim: n => /=.
  - by [].
  - move=> n IHn.
    by rewrite IHn.
Qed.

Lemma size_cons (a :char)  l n :
  size l = n -> size (a :: l) = n.+1.
Proof.
  move=> H /=.
  by rewrite H.
Qed.

Search (size (_ ++ _)).
Lemma size_rep a :
  forall n m, size (rep [:: a] n ++ b :: rep [:: a] m) = n + m + 1.
Proof.
  move=> n m.
  rewrite size_cat.
  Check (size_cons b (rep [::a] m)).
  rewrite (size_cons b (rep [::a] m) m).
  rewrite size_rep_one.
  by nat_norm.
  rewrite size_rep_one.
  by [].
Qed.

Lemma take_take_1 (a : char) (n : nat) (ln lm : seq char) :
  size ln = n ->
  take (n + 1) ((ln ++ [:: a]) ++ lm) = ln ++ [:: a].
Proof.
  move=> Hn.
  have Hsize :  n + 1 <= size (ln ++ [:: a]).
  - by rewrite size_cat Hn //=.
  have Hsize2 : n + 1 = size (ln ++ [:: a]).
  - by rewrite size_cat Hn //=.
  Check @takel_cat (n + 1) char (ln ++ [:: a]) Hsize lm.
  rewrite (@takel_cat (n + 1) char (ln ++ [:: a]) Hsize lm).
  rewrite Hsize2.
  Check @take_size char (ln ++ [:: a]).
  rewrite (@take_size char (ln ++ [:: a])).
  by [].
Qed.
  
Lemma take_take' (a : char) (n : nat) (ln lm : seq char) :
  size ln = n ->
  take n (take (n + 1) ((ln ++ [:: a]) ++ lm)) = ln.
Proof.
  move=> Hn.
  rewrite (take_take_1 a n ln lm).
  have Hsize : n <= size ln.
  - by rewrite Hn.
  Check @takel_cat n char ln Hsize [:: a].
  rewrite (@takel_cat n char ln Hsize [:: a]).
  rewrite -Hn.
  Check @take_size char ln.
  rewrite (@take_size char ln).
  by [].
  by apply Hn.
Qed.

Lemma subnnn n : n - n = 0.
Proof.
  elim: n.
  - by [].
  - move=> n IHn.
    by rewrite subSS.
Qed.

Lemma drop_take' (a : char) (n : nat) (ln lm : seq char) :
  size ln = n ->
  drop n (take (n + 1) ((ln ++ [:: a]) ++ lm)) = [:: a].
Proof.
  move=> Hn.
  rewrite (take_take_1 a n ln lm).
  Check @drop_cat n char ln [:: a].
  rewrite (@drop_cat n char ln [:: a]).
  rewrite Hn.
  case: (n < n).
  - rewrite -Hn.
    rewrite (drop_size ln).
    by [].
  - have Hzero : n - n = 0 by rewrite subnnn.
    rewrite Hzero //=.
    by [].
Qed.

(* 特殊化した形で証明する。 *)
Lemma take_take n m (a b : char) :
  take n (take (n + 1) (rep [:: a] n ++ b :: rep [:: a] m)) = rep [:: a] n.
Proof.
  Check take_take' b n (rep [:: a] n) (rep [:: a] m).
  have H : take n (take (n + 1) ((rep [:: a] n ++ [:: b]) ++ rep [:: a] m)) = rep [:: a] n.
  - rewrite (take_take' b n (rep [:: a] n) (rep [:: a] m)).
    + by [].
    + apply size_rep_one.
  - Check catA.
    rewrite -catA /= in H.
      by apply H.
Qed.

(* 特殊化した形で証明する。 *)
Lemma drop_take n m (a b : char) :
  (drop n (take (n + 1) (rep [:: a] n ++ b :: rep [:: a] m))) = [:: b].
Proof.
  have H : drop n (take (n + 1) ((rep [:: a] n ++ [:: b]) ++ rep [:: a] m)) = [:: b].
  - Check drop_take' b n (rep [:: a] n) (rep [:: a] m).
    apply (drop_take' b n (rep [:: a] n) (rep [:: a] m)).
    by apply size_rep_one.
  - rewrite -catA /= in H.
    by apply H.
Qed.

Lemma take_rep n :
  forall (a : char) (l : seq char), take n (rep [:: a] n ++ l) = rep [:: a] n.
Proof.
  move=> a l.
  have Hsize : n <= size (rep [:: a] n) by rewrite size_rep_one.
  Check @takel_cat n char (rep [:: a] n) Hsize l.
  rewrite (@takel_cat n char (rep [:: a] n) Hsize l).

  have Hsize2 : size (rep [:: a] n) = n by rewrite size_rep_one.
  rewrite -{1}Hsize2.
  Check @take_size char (rep [:: a] n).
  rewrite (@take_size char (rep [:: a] n)).
  by [].
Qed.

Lemma drop_rep n :
  forall (a b : char) (l : seq char),
    drop (n + 1) (rep [:: a] n ++ b :: l) = l.
Proof.
  move=> a b l.
  have Hsize2 : n + 1 = size (rep [:: a] n ++ [:: b]).
  - by rewrite size_cat //= size_rep_one.
  have H : drop (n + 1) ((rep [:: a] n ++ [:: b]) ++ l) = l.
  - Check @drop_cat (n + 1) char ((rep [:: a] n) ++ [:: b]) l.
    rewrite (@drop_cat (n + 1) char ((rep [:: a] n) ++ [:: b]) l).
    rewrite -Hsize2.
    case (n + 1 < n + 1).
    + Check (drop_size (rep [:: a] n ++ [:: b])).
      rewrite {1}Hsize2.
      rewrite (drop_size (rep [:: a] n ++ [:: b])).
      by [].
    + have Hzero : (n + 1 - (n + 1)) = 0.
      * nat_norm => //=.
                      by rewrite subnnn.
      rewrite Hzero.
      by apply drop0.
  - Search ((_ ++ _) ++ _).
    Check @catA char.
      by rewrite -catA //= in H.
Qed.

(** 正規表現 a* b a* の言語は、{a^n b a^m : n,m ∈ Nat} である。 *)
Goal forall (n m : nat),
       re_lang
         (Conc (Conc (Star (Atom a)) (Atom b)) (Star (Atom a)))
         (rep [:: a] n ++ [:: b] ++ rep [:: a] m).
Proof.
  move=> n m.
  rewrite /re_lang /conc /=.
  apply/existsP => /=.
  rewrite (size_rep a n m).
  rewrite -addn1.
  have lt_n__n_m_1 : n + 1 < n + m + 1 + 1.
  - apply/ltP.
    rewrite 2!addn1.
    apply Lt.lt_n_S.
    rewrite -addnA.
    rewrite [m + 1]addnC.
    rewrite addnA.
    apply/ltP.
    apply (@ltn_addr n (n + 1) m).
    rewrite addn1.
    apply ltnSn.
    
  exists (Ordinal lt_n__n_m_1).

  apply/andP.
  split.
  - apply/existsP => /=.
    Check size_takel.
    rewrite size_takel.
    rewrite -addn1.
    have lt_n__n_1 : n < n + 1 + 1.
      apply (@ltn_addr n (n + 1) 1).
      rewrite addn1.
      apply ltnSn.

    exists (Ordinal lt_n__n_1).
    apply/andP.
    split.
    + simpl.
      rewrite take_take.
      apply star_rep.
      by rewrite /atom /=.
    + simpl.
      * rewrite drop_take.
          by rewrite /atom /=.
      * rewrite size_cat size_rep_one.
          rewrite (size_cons b (rep [:: a] m) m).
          - rewrite -[m.+1]addn1 [m + 1]addnC addnA.
              by apply leq_addr.
          - by rewrite size_rep_one.
    + simpl.
      rewrite drop_rep.
      apply star_rep.
      by rewrite /atom /=.
Qed.

(** 正規表現 (aaa)* の言語は、{a^3n : n ∈ Nat} である。 *)
Goal forall (n : nat), re_lang
                         (Star (Conc (Conc (Atom a) (Atom a)) (Atom a)))
                         (rep [:: a; a; a] n).
Proof.
  move=> n.
  rewrite /re_lang /conc /=.
  apply star_rep.

  Compute (take 1 (take 2 [:: a; a; a])).
  Compute (drop 1 (take 2 [:: a; a; a])).
  Compute (drop 2 [:: a; a; a]).

  apply/existsP.                            (* exists 2 をする。 *)
  have lt_2_size : 2 < (size [:: a; a; a]).+1 by [].
  exists (Ordinal lt_2_size).

  apply/andP; split.
  - apply/existsP.                          (* exists 1 をする。 *)
    have lt_1_size : 1 <  (size (take 2 [:: a; a; a])).+1 by [].
    exists (Ordinal lt_1_size).
    apply/andP.
    split.
    + simpl.
        by rewrite /atom /=.                  (* atom a [:: a] *)
    + simpl.
        by rewrite /atom /=.                  (* atom a [:: a] *)
  - simpl.
        by rewrite /atom /=.                  (* atom a [:: a] *)
Qed.

(** 正規表現 0* の言語は、{ε} である。  *)
Goal re_lang (Star Eps) [::].
Proof.
  rewrite /re_lang /eps.
  by [].
Qed.

(** 定理 1.10 （クリーネの定理）
言語Lが正規言語なら、かつそのときに限り、言語がLであるような正規表現が存在する。

文献[2]より：
We now call a general language regular if it is equivalent to the language of some
regular expression.
Theorem 3.1 The matching problem for regular expressions is decidable.
Proof This is an immediate consequence of defining the semantics of regular
expressions in terms of decidable languages.

文献[2]ではこの証明は書かれていないで、次が定義されている。
 *)
Definition regular (L : dlang) :=
  exists e : regexp, forall w, L w <-> re_lang e w.

(** 例 *)
Goal regular (re_lang Void).
Proof.
  by exists Void.
Qed.

(** 補足：言語が等しいということ。 *)
Goal L1 = L2 -> L1 =i L2.
Proof.
  move=> H.
  (* Goal : L1 =i L2 *)
  move=> w.
  (* Goal : L1 w = L2 w *)
  apply/(f_equal (fun L => w \in L)).
  (* Goal : L1 = L2 *)
  by [].
Qed.

(* w \in L は、「rewrite /in_mem /mem /=」 で、L w になる。
   実際は、直接 apply できる。
*)
Goal forall (L : dlang), (L w <-> w \in L).
Proof.
  rewrite /in_mem /mem /=.                  (* 不要 *)
  by [].
Qed.

(* END *)
