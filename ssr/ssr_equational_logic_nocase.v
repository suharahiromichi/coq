(*
等式論理 (==) : bool -> bool -> bool を使う論理体系。
2013_11_23 @suharahiromichi

(Coq/SSReflect の == は、T -> T -> bool だが、
ここでは bool -> bool -> bool だけで使う。そのために、変数をboolに固定する。)

@hatsugai さんの等式論理の証明チェッカ を参考にした。
http://www.principia-m.com/ts/0072/index-jp.html
最後の群論の定理は、boolの範囲を越えるため、証明していない。

Coqはbool式が計算できるので、
変数をcaseで場合分けすると簡単に証明できてしまう。
それではおもしろくないので、以下の制限のもとで証明する。
ただし、公理を追加する必要がある。

決めごと：
(1) caseは使わない。
(2) 公理と定理は==または!=で結ぶかたちだけとする。
(3) 証明はdoneでなく、reflexivityで終わる。doneだとbool計算をするから。
*)

Require Import ssreflect ssrbool eqtype ssrnat.
Require Import seq ssrfun.

Section Equational_logic.
  
  Variable assoc : forall p q r : bool,     (* bagの性質として *)
                     (p == q == r) = (p == (q == r)).
  
  Variable axiom_3_2 : forall p q : bool, p == q == q == p. (* symmetory *)
  (* Variable axiom_3_3 : forall q, true == q. *)
  Variable axiom_3_3 : forall q : bool, true == q == q.
  Variable axiom_3_8 : false == ~~ true.
  Variable axiom_3_9 : forall p q : bool, (p != q) == (~~ p == q). (* not equal *)
  Variable axiom_3_24 : forall p q : bool, p || q == q || p.       (* or'commutative *)
  Variable axiom_3_25 : forall p q r : bool, p || q || r == p || (q || r). (* or'associative *)
  Variable axiom_3_26 : forall p : bool, p || p == p.                      (* or'reflectivity *)
  Variable axiom_3_27 : forall p q r : bool, p || (q == r) == p || q == p || r. (* or'distributive *)
  (* Variable axion_3_28 : forall p, p || ~~ p. *)                     (* excluded middle *)
  Variable axiom_3_28 : forall p : bool, p || ~~ p == true.            (* excluded middle *)
  Variable axiom_3_35 : forall p q : bool, p && q == p == q == p || q. (* golden *)
  Variable axiom_3_57 : forall p q : bool, p ==> q == p || q == q.     (* implication *)

  Ltac use H X :=                           (* substituion *)
    (have H := X;
     try rewrite assoc in H;
     move/eqP in H).

  Lemma leibniz : forall (p q : bool) (f : bool -> bool),
                    p = q -> f p = f q.
  Proof.
    intros. f_equal. apply H.
  Qed.
  Implicit Arguments leibniz [p q].

  Theorem theorem_3_4 : true.
  Proof.
    use H (axiom_3_3 true).
    rewrite H.
    apply/eqP. reflexivity.
  Qed.

  Theorem theorem_3_5 : forall q : bool, q == q. (* reflectivity *)
  Proof.
    move=> q.
    apply/eqP. reflexivity.
  Qed.

  Theorem theorem_3_11 : forall p q : bool,
                           ~~p == q == p == ~~q. (* ちょっと込みいった *)
  Proof.
    move=> p q.
    use H3 (axiom_3_9 p q).
    use H4 (axiom_3_9 q p).
    use H1 (axiom_3_2 p q).                    (* 定理を前提に置く。 *)
    use H2 (axiom_3_2 p (~~ q)).
    rewrite assoc.
    rewrite -H3 H2 -H4 -H1.
    apply/eqP. reflexivity.
  Qed.
  
  (* leibniz equation を使用する場合 *)
  Theorem theorem_3_11' : forall p q : bool,
                            ~~p == q == p == ~~q. (* ちょっと込みいった *)
  Proof.
    move=> p q.
    use H1 (theorem_3_5 (p != q)).          (* reflexivityで終わるなら要らない。 *)
    use H2 (axiom_3_2 p q).
    apply (leibniz (fun x => (p != q) == ~~ x)) in H2.
    use H3 (axiom_3_9 p q).
    apply (leibniz (fun x => x == (q != p))) in H3.
    use H4 (axiom_3_9 q p).
    apply (leibniz (fun x => ~~ p == q == x)) in H4.
    rewrite assoc.
    use H5 (axiom_3_2 p (~~ q)).
    
    rewrite H5 -H4 -H3 -H2.
    apply/eqP. apply H1.                    (* または reflexivity *)
  Qed.

  Theorem theorem_3_12 : forall p : bool,
                           ~~ ~~ p == p.    (* 二重否定 *)
  Proof.
    move=> p.
    use H1 (axiom_3_2 p (~~ ~~ p)).
    use H2 (theorem_3_11 p (~~ p)).
    rewrite -H1 -H2.
    apply/eqP. reflexivity.
  Qed.

  Theorem theorem_3_29 : forall p : bool, p || true == true.
  Proof.
    move=> p.
    use H1 (axiom_3_27 p p p).
    use H2 (axiom_3_3 p).
    use H3 (axiom_3_3 (p || p)).
    rewrite -H2 in H1.
    rewrite -H3 in H1.
    rewrite H1.
    apply/eqP. reflexivity.
  Qed.
  
  Lemma true__p__p : forall p : bool, p == p == true.
  Proof.
    move=> p.
    use H (axiom_3_3 p).
    rewrite H.
    apply/eqP. reflexivity.
  Qed.

  Lemma false__p__not_p : forall p : bool, false == p == ~~ p.
  Proof.
    move=> p.
    use H1 (axiom_3_9 p p).
    use H2 (axiom_3_3 p).
    use H3 axiom_3_8.
    use H4 (axiom_3_2 p (~~ p)).
    rewrite -H2 in H1.
    rewrite -H3 in H1.
    rewrite -H4 in H1.

    rewrite H1. rewrite assoc.
    apply/eqP. reflexivity.
  Qed.

  Theorem theorem_3_30 : forall p : bool, p || false == p.
  Proof.
    move=> p.
    use H1 (axiom_3_27 p p (~~ p)).
    use H2 (axiom_3_26 p).
    use H3 (axiom_3_28 p).
    rewrite H2 in H1.
    rewrite H3 in H1.
    (* H1 : p || (p == ~~ p) = (p == true)  *)
    use H4 (true__p__p p).
    use H5 (false__p__not_p p).
    rewrite -H4 in H1.
    rewrite -H5 in H1.
    rewrite H1.
    
    apply/eqP. reflexivity.
  Qed.

  (* leibniz equation を使用する場合 *)
  Theorem theorem_3_30' : forall p : bool, p || false == p.
  Proof.
    move=> p.
    use H1 (axiom_3_27 p p (~~ p)).
    use H2 (axiom_3_26 p).
    apply (leibniz (fun x => p || (p == ~~ p) == x)) in H2.
    use H3 (axiom_3_9 p p).
    apply (leibniz (fun x => p || x == p)) in H3.
    use H4 (axiom_3_3 p).
    apply (leibniz (fun x => p || ~~ x == p)) in H4.
    use H5 axiom_3_8.
    apply (leibniz (fun x => p || x == p)) in H5.
    use H6 (axiom_3_2 p (~~ p)).
    rewrite H5 H4 H3.
    rewrite -H6.
    rewrite -H2.
    rewrite H1.
    (* (p || p == p || ~~ p) == p || p *)

    use H7 (axiom_3_28 p).
    use H8 (axiom_3_3 (p || p)).
    use H9 (axiom_3_2 (p || p) true).
    rewrite H7.
    rewrite H9.
    rewrite assoc.
    rewrite -H8.
    apply/eqP. reflexivity.
  Qed.
  
  Theorem theorem_3_32 : forall p q : bool,
                           p || q == p || ~~ q == p.
  Proof.
    move=> p q.
    use H1 (axiom_3_27 p (~~ q) q).
    use H2 (false__p__not_p q).
    use H3 (axiom_3_2 q (~~ q)).
    rewrite -H3 in H1.
    rewrite -H2 in H1.
    (* H1 : p || false = (p || ~~ q == p || q) *)
    use H4 (theorem_3_30 p).
    use H5 (axiom_3_2 (p || ~~ q) (p || q)).
    rewrite H4 in H1.
    rewrite H5 in H1.
    
    rewrite -H1.
    apply/eqP. reflexivity.
  Qed.

  Theorem theorem_3_47 : forall p q : bool,
                           ~~ (p && q) == ~~ p || ~~ q. (* De Morgan *)
  Proof.
    move=> p q.
    
    have H0 := (axiom_3_35 p q).
    rewrite assoc in H0.
    rewrite assoc in H0.
    move/eqP in H0.
    rewrite H0.

    have H3 := (theorem_3_32 q p).
    use H31 (axiom_3_2 (q || p) (q || ~~ p)).
    use H32 (axiom_3_2 q (q || p)).
    use H33 (axiom_3_24 p q).
    rewrite H31 in H3.
    rewrite assoc in H3.
    rewrite -H32 in H3.
    rewrite -H33 in H3.
    move/eqP in H3.
    rewrite -H3.

    use H1 (axiom_3_9 p (q || ~~ p)).
    rewrite H1.

    have H4 := (theorem_3_32 (~~ p) q).
    use H41 (axiom_3_2 (~~ p || q) (~~ p || ~~ q)).
    rewrite H41 in H4.
    rewrite assoc in H4.
    use H42 (axiom_3_2 (~~ p || q) (~~ p)).
    rewrite H42 in H4.
    use H43 (axiom_3_24 (~~ p) q).
    rewrite H43 in H4.
    move/eqP in H4.
    
    rewrite H4.
    apply/eqP. reflexivity.
  Qed.

  Theorem theorem_3_59 : forall p q : bool,
                           p ==> q == ~~ p || q. (* よくある含意の式 *)
  Proof.
    move=> p q.
    (* 含意の定義を展開する。 *)
    apply/eqP.
    use H0 (axiom_3_57 p q).
    rewrite H0.

    have H1 := (theorem_3_32 q p).          (* H1のuseがばらされて *)
    use H2 (axiom_3_2 (q || p) (q || ~~ p)).
    use H3 (axiom_3_24 q (~~ p)).
    use H4 (axiom_3_24 q p).
    rewrite H2 in H1.
    rewrite assoc in H1.
    rewrite H3 in H1.
    rewrite H4 in H1.
    move/eqP in H1.
    rewrite H1. reflexivity.
  Qed.

End Equational_logic.

(* END *)
