(*
@hatsugai さんの等式論理の証明チェッカ
http://www.principia-m.com/ts/0072/index-jp.html
を自分でもやりたくて、Coq/SSReflect で「==」を「=」にReflectすることまでは考えついた。
でも、実際には、move=>とcaseで、trueとfalseの場合分けを尽すだけで解けてしまう。

曰く、
Goal forall p q, p && q == p == q == p || q.
Proof. move=> p q. by case p; case q. Qed.

Goal forall p q r, p || (q == r) == p || q == p || r.
Proof. move=> p q r. by case p; case q; case r. Qed.

ProofとQedを含めても、5語でできる証明チェッカですね。
ここで、「==」はbool->bool->bool 、「=」はbool->bool->Propです。

これでは、おもしろくないので、caseを使わない証明を考えよう。
*)

Require Import ssreflect ssrbool eqtype ssrnat.
Require Import seq ssrfun.

Section Equational_logic.

  Check eq_op.                              (* == *)
  Check eqP.                                (* reflect (?2 = ?3) (?2 == ?3) *)
  Check _ =P _.                             (* reflect (?2 = ?3) (?2 == ?3) *)
  
  Check eqb.                                (* bool -> bool -> bool *)

(*
  Lemma predU1P : reflect (p = q \/ b) ((p == q) || b).
  Lemma pred2P : reflect (p = q \/ z = u) ((p == q) || (z == u)).
*)

  Theorem eq_refl : forall (p : bool), p == p.
  Proof.
    move=> p.
      by apply/eqP.
  Qed.

  Lemma eq_assoc : forall p q r, 
                     (p == q == r) = (p == (q == r)).
  Proof.
    move=> p q r.
      by case: p; case: q; case r.
  Qed.
  
  Lemma eq_sym' : forall (p q : bool), (p == q) = (q == p).
  Proof.
    move=> p q.
      by case p; case q.
  Qed.

  Theorem eq_sym : forall (p q : bool), p == q == q == p.
  Proof.
    move=> p q.
    rewrite eq_assoc.
    apply/eqP. apply eq_sym'.
  Qed.
  
  Lemma ne_sym' : forall (p q : bool), (p != q) = (q != p).
  Proof.
    move=> p q.
      by case p; case q.
  Qed.

  Theorem ne_sym : forall (p q : bool), (p != q) == (q != p).
    move=> p q.
    apply/eqP. apply ne_sym'.
  Qed.
    
  Lemma eq_del_true' : forall (p : bool), (true == p) = p.
  Proof.
    done.
  Qed.

  Theorem eq_del_true : forall (p : bool), true == p == p.
  Proof.
    move=> p.
    apply/eqP.
    apply eq_del_true'.
  Qed.
(*
    move=> p.
    split.
    (* -> *)
    move=> H. case H.
    done.
    (* <- *)
    move/eqP=> H.
    bq rewrite -H.
*)

  Lemma eq_del_false' : forall (p : bool), false == p = ~~p.
  Proof.
    done.
  Qed.

  Theorem eq_del_false : forall (p : bool), false == p = ~~p.
  Proof.
    done.
  Qed.
  
  Theorem eq_del_true'' : forall (p : bool), reflect p (true == p).
  Proof.
    move=> p. case: p.
      by apply ReflectT.
        by apply ReflectF.
  Qed.

  Lemma eq_neg' : forall (p q : bool), ~~(p == q) = (~~p == q).
  Proof.
    move=> p q.
    by case p; case q.
  Qed.
  
  Theorem eq_nag : forall (p q : bool), ~~(p == q) == ~~p == q.
  Proof.
    move=> p q.
      by case p; case q.
(*
    rewrite eq_assoc.
    apply/eqP.
    apply eq_neg'.
*)
  Qed.
  
  Theorem eq_false : false == ~~true.
  Proof.
    done.
  Qed.

  Lemma eq_notp_q' : forall p q, (~~p == q) = (p == ~~q).
  Proof.
    move=> p q.
    rewrite [_ == ~~_]eq_sym'.
    rewrite -[~~_ == _]eq_neg'.
    rewrite -[~~_ == _]eq_neg'.
    rewrite -ne_sym'.
    done.
  Qed.

  Theorem eq_notp_q : forall p q, ~~p == q == p == ~~q.
  Proof.
    move=> p q.
      by case p; case q.
(*
    rewrite eq_assoc.
    apply/eqP.
    apply eq_notp_q'.
*)
  Qed.

  Lemma eq_dbl_neg' : forall p, ~~ ~~p = p.
  Proof.
    move=> p.
    case p; rewrite //.
  Qed.

  Theorem eq_dbl_neg : forall p, ~~ ~~p == p.
  Proof.
    move=> p.
    by case p.
(*
    apply/eqP.
    apply eq_dbl_neg'.
*)
  Qed.

  Theorem eq_or : forall p q r, p || (q == r) == p || q == p || r.
  Proof.
    move=> p q r.
    by case p; case q; case r.
  Qed.

  Theorem eq_imp : forall p q, p ==> q == p || q == q.
  Proof.
    move=> p q.
      by case p; case q.
  Qed.

  Theorem eq_gold_law : forall p q, p && q == p == q == p || q.
  Proof.
    move=> p q.
    by case p; case q.
  Qed.

End Equational_logic.


