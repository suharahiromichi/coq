From mathcomp Require Import all_ssreflect.

Set Implicit Arguments.
Unset Strict Implicit.

(**
# 証明を型にはめると 共立出版 bit
*)
Section HanakoTaro.

  Inductive minna : predArgType :=
  | hanako
  | taro.

  Variable loves : minna -> minna -> bool.
  Variable knows : minna -> bool -> bool.

  (* 花子は太郎を愛している。 *)
  Axiom hanako_loves_taro : loves hanako taro.

  (* 誰でも、自分が誰かを愛していれば、そのことを本人は知っている。 *)
  Axiom ax1 : forall x y :
      minna, loves x y -> knows x (loves x y).

  (* 花子は、自分が愛している人は、自分を愛してくれていると思っている。 *)
  Axiom ax2 : forall x :
      minna, knows hanako (loves hanako x ==> loves x hanako).

  (* 誰でも、自分の頭の中で三段論法を行える。 *)
  Axiom ax3 : forall x : minna, forall P Q :
      bool, knows x (P ==> Q) -> knows x P -> knows x Q.

  (* 花子は、太郎が花子を愛していると知っている。 *)
  Lemma th : knows hanako (loves taro hanako).
  Proof.
    apply: ax3.
    - apply: ax2.
    - apply: ax1.
      apply: hanako_loves_taro.
      
    Restart.

    refine (@ax3 hanako (loves hanako taro) (loves taro hanako)
              (@ax2 taro)
              (@ax1 hanako taro hanako_loves_taro)).
  Qed.

End HanakoTaro.

(**
# John の自殺 (高階単一化と証明の一般化 人工知能学会誌 Vol.6 No.3)
*)
Module John.

  Variable i : Type.
  
  Variable depressed : i -> Prop.
  Variable weapon : i -> Prop.
  Variable gun : i -> Prop.
  Variable hate : i -> i -> Prop.
  Variable kill : i -> i -> Prop.
  Variable possess : i -> i -> Prop.
  Variable buy : i -> i -> Prop.
  Variable gun1 : i.
  Variable John : i.
  
  Axiom ax1 : forall x, depressed x -> hate x x.
  Axiom ax2 : forall x y z, hate x y -> possess x z -> weapon z -> kill x y.
  Axiom ax3 : forall x y, buy x y -> possess x y.
  Axiom ax4 : forall z, gun z -> weapon z.
  Axiom ax5 : depressed John.
  Axiom ax6 : buy John gun1.
  Axiom ax7 : gun gun1.
  
  Lemma th : kill John John.
  Proof.
    apply: ax2.
    - apply: ax1.
      apply: ax5.
    - apply: ax3.
      apply: ax6.                     (* ここで gun1 が導入される。 *)
    - apply: ax4.
      apply: ax7.

    Restart.
    refine (ax2 (ax1 ax5) (ax3 ax6) (ax4 ax7)).
    
    Restart.
    refine (@ax2 John John gun1 (@ax1 John ax5)
              (@ax3 John gun1 ax6)
              (@ax4 gun1 ax7)).
  Qed.
  
End John.

(**
# Boomborg-PC マニュアル
 *)
Section And.
  
  Inductive And (A B : Prop) : Prop := Conj : A -> B -> And A B.
  
  Lemma andI (A B : Prop) : A -> B -> And A B.
  Proof.
    intros HA HB.
    now apply Conj.
  Qed.
  
  Lemma andEL X Y : And X Y -> X.
  Proof.
    intros H.
    destruct H.
    apply H.
  Qed.
  
  Lemma andER X Y : And X Y -> Y.
  Proof.
    intros H.
    destruct H.
    apply H0.
  Qed.
  
  Lemma andC X Y : And X Y -> And Y X.
  Proof.
    intro H.
    apply andI.
    - apply andER in H.
      assumption.
    - apply andEL in H.
      assumption.
  Qed.
  
End And.

(* END *)
