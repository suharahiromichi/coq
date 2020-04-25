From mathcomp Require Import ssreflect.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensiv.

Section Classical_Logic.
  
  Definition peirces := forall P Q : Prop, ((P -> Q) -> P) -> P.
  
  Definition nnpp := forall P : Prop, ~ ~ P -> P. (* double nagation *)
  
  Definition exmid := forall P : Prop, P \/ ~ P. (* 排中律 *)
  
  Definition dms := forall P Q : Prop, ~ (~ P /\ ~ Q) -> P \/ Q.
  
  Definition impor := forall P Q : Prop, (P -> Q) -> ~ P \/ Q.
  
  (* 上記の命題が、同値であることの証明をする。 *)
  
  Lemma nnpp__peirces : nnpp -> peirces.
  Proof.
    move=> nnpp P Q HPQP.
    apply: (nnpp P) => HnP.
    apply: (HnP).                           (* copyする。 *)
      by apply: HPQP => HP.
  Qed.
  
  Lemma exmid__peirces : exmid -> peirces.
  Proof.
    move=> exmid P Q HPQ_P.
    case: (exmid P) => [HP | HnP].
    - done.
    - by apply: HPQ_P => HP.
  Qed.
  
  Lemma dms__peirces : dms -> peirces.
  Proof.
    move=> dms P Q HPQP.
    case: (dms P Q).
    - case=> [HnP HnQ].
      apply: (HnP).
        by apply: HPQP => HP.
    - done.
    - move=> HQ.
        by apply HPQP => HP.
  Qed.
  
  Lemma peirces__nnpp : peirces -> nnpp.
  Proof.
    move=> peirces P HnnP.
    by apply: (peirces P False) => HnP.
  Qed.
  
  Lemma peirces__exmid : peirces -> exmid.
  Proof.
    move=> peirces P.
    apply: (peirces (P \/ ~ P) (~ (P \/ ~ P))) => HPP.
    right=> HP.
    apply: HPP.
    - by left.
    - by left.
  Qed.
  
  Lemma exmid__nnpp : exmid -> nnpp.
  Proof.
    move=> exmid P HnnP.
    by case: (exmid P) => [HP | HnP].
  Qed.
  
  Lemma nnpp__dms : nnpp -> dms.
  Proof.
    move=> nnpp P Q Hn_nPnQ.
    apply: nnpp => Hn_PQ.
    apply: Hn_nPnQ.
    split=> H.
    - apply Hn_PQ.
        by left.
    - apply Hn_PQ.
        by right.
  Qed.

  Lemma impor__nnpp : impor -> nnpp.
  Proof.
    move=> impor P HnnP.
      by case: (impor P P).
  Qed.
  
  (*
    情報論理学
    九州大学大学院システム情報科学研究院 情報学部門 長谷川先生
    平成24年4月
    http://opal.is.kyushu-u.ac.jp/~hasegawa/lecture/infologic/h24/il-txt-haifu-h24.pdf
    p.32, p.33 を参考にした。
   *)
  Lemma nnpp__exmid : nnpp -> exmid.
  Proof.
    move=> nnpp P.
    apply: nnpp => Hn_P_or_n_P.
    apply: (Hn_P_or_n_P).
    right=> HP.
    apply: Hn_P_or_n_P.
      by left.
  Qed.
  
  (* Coq'n Artの回答を参考にした。 *)
  Lemma dms__exmid : dms -> exmid.
  Proof.
    move=> dms P.
    apply: dms => Hn_nPnnP.
      by case: Hn_nPnnP => [HnP HnnP].
  Qed.
  
  Lemma impor__exmid : impor -> exmid.
  Proof.
    move=> impor P.
    case: (impor P P) => [| HnP | HP].
    - done.
    - by right.
    - by left.
  Qed.
  
  Lemma dms__nnpp : dms -> nnpp.
  Proof.
    move=> dms P HnnQ.
    case: (dms P P) => [H | HP | ].
    - apply: HnnQ=> HP.
        by case: H.
    - done.
    - done.
  Qed.

  Lemma exmid__dms : exmid -> dms.
  Proof.
    move=> exmid P Q Hn_nPnQ.
    case: (exmid P) => [HP | HnP].
    - by left.
    - case: (exmid Q) => [HQ | HnQ].
      + by right.
      + by case: Hn_nPnQ.
  Qed.
  
  Lemma exmid__impor : exmid -> impor.
  Proof.
    move=> exmid P Q HPQ.
    case: (exmid P) => [HP | HnP].
    - right.
        by apply: HPQ.
    - left.
        by apply: HnP.
  Qed.
  
  (* 上記以外の証明は、間接的に行うことになる。 *)

  Lemma impor__peirces : impor -> peirces.
  Proof.
    move=> impor.
    apply: nnpp__peirces.
    apply: exmid__nnpp.
    apply: impor__exmid.
    done.
  Qed.

End Classical_Logic.
  
(* END  *)
