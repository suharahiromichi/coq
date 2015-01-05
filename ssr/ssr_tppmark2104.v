Require Import ssreflect ssrbool ssrnat eqtype seq ssrfun.
Require Import div prime.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(*
TPPmark2014
September 22, 2014
http://imi.kyushu-u.ac.jp/lasm/tpp2014/tppmark2014-2.pdf
*)

Lemma mod3p a : (a = 0 %[mod 3]) \/ (a = 1 %[mod 3]) \/ (a = 2 %[mod 3]).
Proof.
  by elim: a;
  [left | 
   move=> a [|[]] H;
   [right; left | right; right | left];
   rewrite -addn1 -(modnDml a 1 3) H].
Qed.

Lemma q1 a : a^2 = 0 %[mod 3] \/ a^2 = 1 %[mod 3].
Proof.
 by case: (mod3p a) => [|[]] H;
     [left | right | right];
     rewrite -(modnMm a a 3) H.
Qed.

Lemma q1' a : a^2 <> 2 %[mod 3].
Proof.
  by case: (mod3p a) => [|[]];
      rewrite -(modnMm a a 3) => H;
      rewrite H.
Qed.

Lemma div3p a b c : a + b = 3 * c ->
                    (a %% 3 + b %% 3) %% 3 == 0.
Proof.
  Check f_equal.                            (* これは定理 *)
  Check (f_equal (modn ^~ 3)).
  (* 前提：a + b = 3 * c *)
  move/(f_equal (modn ^~ 3)).
  (* 前提：(a + b) %% 3 = (3 * c) %% 3 *)
  (* これの構文糖が、a + b = (3 * c) %[mod 3] *)
  move/eqP.                                 (* 続けて move/()/eqP とも書ける。 *)
  rewrite modnMr -modnDm.
  by [].
Qed.

Lemma sqr_mod a p: prime p -> p %| (a^2) -> p %| a.
Proof.
  by move=> /Euclid_dvdM -> /orP [|].
Qed.

Lemma prime_3 : prime 3.
Proof.
    by [].
Qed.

Lemma q2 a b c :
  a^2 + b^2 = 3 * c^2 -> 3 %| a /\ 3 %| b /\ 3 %| c.
Proof.
  move=> Heq.
  Check (@div3p (a^2) (b^2) (c^2) Heq).
  case: (div3p Heq) => H.      (* H : (a ^ 2 %% 3 + b ^ 2 %% 3) %% 3 == 0 あとで使う。 *)
  case: (q1 a) => [|] Ha; case: (q1 b) => [|] Hb.
  (* a^2 = 0 mod 3 かつ a^2 = 0 mod 3 の場合 *)
  - move: (Ha) => /eqP.                         (* Ha : a^2 = 0 mod 3 *)
    move: (Hb) => /eqP.                         (* Hb : b^2 = 0 mod 3 *)
    rewrite !eqn_mod_dvd //= !subn0 => Ha' Hb'. (* Ha' : 3 %| a^2 *) (* Hb' : 3 %| b^2 *)
    move: (sqr_mod prime_3 Ha') => Ha''; rewrite Ha''. (* Ha'' : 3 %| a *)
    move: (sqr_mod prime_3 Hb') => Hb''; rewrite Hb''. (* Hb'' : 3 %| b *)
    move: Hb'' Ha'' Heq.
    (* 前提の3を繰り出す。 *)
    move/dvdnP => [a' ->].                  (* Ha'' *)
    move/dvdnP => [b' ->].                  (* Hb'' *)
    rewrite !expnMn -mulnDl -[3^2]mulnn mulnCA.
    move/eqP.
    rewrite eqn_pmul2l.
    move=> /eqP Heq.
    rewrite mulnC in Heq.
    (* 前提の3を繰り出す。終わり。 *) 
    split; [|split]; rewrite //.            (* ゴールの /\ を分解するが、のこるのはひとつ。 *)
    (* ゴール 3 %| c を証明する。  *)
    apply sqr_mod.
    + by apply prime_3.                     (* ゴール： prime 3 *)
    + rewrite -Heq dvdn_mulr.               (* ゴール： 3 |% c^2 *)
      * by [].
      * by [].
      * by [].
  (* a^2 = 0 mod 3 かつ a^2 = 1 mod 3 の場合 *)
  - by rewrite Ha Hb in H.                  (* Hを使って、矛盾を導く。 *)
  (* a^2 = 1 mod 3 かつ a^2 = 0 mod 3 の場合 *)
  - by rewrite Ha Hb in H.                  (* Hを使って、矛盾を導く。 *)
  (* a^2 = 1 mod 3 かつ a^2 = 1 mod 3 の場合 *)
  - by rewrite Ha Hb in H.                  (* Hを使って、矛盾を導く。 *)
Qed.

Lemma lt_wf_ind n P:
  (forall n0 : nat, (forall m : nat, m < n0 -> P m) -> P n0) -> P n.
Proof.
  elim: n P => [| n IHn] P IH; first by apply IH; move=> m; rewrite (ltn0 m).
  apply IHn; move=> m IHm; apply IH.
  move=> [| k] Hltk; first by apply IH; move=> k; rewrite (ltn0 k).
  by apply IHm; rewrite -ltnS.
Qed.

Lemma q3 a b c:
  a^2 + b^2 = 3 * c^2 -> a = 0 /\ b = 0 /\ c = 0.
Proof.
  move=> Heq.
  (* c = 0 を前提に追加して、現在のゴールを証明する。 *)
  suff Heqc0 : c = 0 by move: a b Heqc0 Heq => [| a] [| b] -> //.
  move: a b Heq; elim/lt_wf_ind : c => [] [| c] // IH a b Heq.  (* c = 0 がゴールになる。 *)
  move: Heq (Heq) => /q2.
  move=> [] /dvdnP [] ka ->.                (* 3%|a を使って、aを(ka*3)に書き換える。 *)
  move=> [] /dvdnP [] kb ->.
  move=> [] /dvdnP [] kc Hc. rewrite Hc.    (* Hcはあとで使う。 *)
  (* 前提の ka*3 などの3をくくりだして、消す。 *)
  rewrite !expnMn.
  rewrite -mulnDl !mulnA.
  move/eqP.
  rewrite eqn_pmul2r.
  rewrite eqn_pmul2r.
  rewrite -[3 * _ * _]mulnA mulnn.
  (* ここまで。 *)
  move=> H; apply/eqP; move: H.
  Check muln_eq0.
  rewrite muln_eq0 => Heq.
  apply/orP.
  left.
  move: Heq.
  move/eqP => H.
  Check (IH kc).
  apply/eqP; move: H.
  apply (IH kc).
  rewrite -(@mulnK kc 3) // -Hc ltn_Pdiv //.
    by [].
    by [].
Qed.

(* http://tcug.jp/books/2014-12/ *)

(* forall m d : nat, 0 < d -> m %% d < d の d>0の場合 *)
Lemma ltn_pmod' m d : m %% d.+1 < d.+1.
Proof.
  by apply ltn_pmod.
Qed.

Lemma problem1 a : a ^ 2 %% 3 != 2.
Proof.
  rewrite -modnXm.                          (* Goal: (a %% 3) ^ 2 %% 3 != 2 *)
  move: (ltn_pmod' a 2).                    (* a %% 3 < 3 を前提に追加する。 *)
  by case: (a %% 3) => [| [| []]].          (* 0<3, 1<3, 2<3 とそれ以外に分ける。 *)
(* それ以外のときは、前提が偽。 *)
Qed.  

Lemma problem2 a b c :
  a ^ 2 + b ^ 2 = 3 * c ^ 2 -> [&& 3 %| a, 3 %| b & 3 %| c].
Proof.
  move=> H.
  have/andP [H0 H1] : (3 %| a) && (3 %| b).
  - move/(f_equal (modn ^~ 3)) : H.
    rewrite -modnMml modnn mul0n mod0n.
    move: (problem1 a) (problem1 b) (ltn_pmod' a 2) (ltn_pmod' b 2).
    by rewrite /dvdn /= -modnDm -modnXm -(modnXm _ _ b);
      move: (a %% 3) (b %% 3) => [| [| [| a']]] [| [| []]].
  rewrite H0 H1 /=.
  move/(f_equal (modn ^~ (3 ^ 2))) : H.
  have/eqP -> : 3 ^ 2 %| a ^ 2 + b ^ 2 by apply dvdn_add; rewrite dvdn_pexp2r.
  by move/esym/eqP; rewrite -/(dvdn _ _) dvdn_pmul2l // Euclid_dvdX //= andbT.
Qed.

Lemma well_founded_lt : well_founded (fun n m => n < m).
Proof.
  move=> x.
  elim: x {1 3}x (leqnn x) => [| n IHn] x H; constructor => y H0.
  - by case: x H H0.
  - exact: (IHn _ (leq_trans H0 H)).
Defined.

Lemma divn_expAC d m n : d %| m -> (m %/ d) ^ n = (m ^ n) %/ (d ^ n).
Proof.
  move=> H; elim: n => //= n IH.
  by rewrite !expnS IH divn_mulAC // muln_divA ?dvdn_exp2r // -divnMA (mulnC d).
Qed.

Lemma problem3 a b c :
  a ^ 2 + b ^ 2 = 3 * c ^ 2 -> [&& a == 0, b == 0 & c == 0].
Proof.
  move=> H.
  suff H0 : c = 0 by move: H; rewrite H0; move: a b => [] // [].
  move: c (well_founded_lt c) a b H; refine (Acc_ind _ _).
  case=> [] // c _ IH a b H.
  case/problem2/and3P : (H) => H0 H1 H2.
  rewrite -(divnK H2) (IH (c.+1 %/ 3) _ (a %/ 3) (b %/ 3)) ?ltn_Pdiv //.
  by rewrite !divn_expAC // -divnDl ?dvdn_mul // H muln_divA ?dvdn_mul.
Qed.

(* END *)
