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

(* END *)
