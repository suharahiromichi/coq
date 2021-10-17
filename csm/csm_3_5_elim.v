(**
ProofCafe 名古屋 補足資料

萩原学 アフェルト・レナルド 「Coq/SSReflect/MathCompによる定理証明」 森北出版

[http://www.morikita.co.jp/books/book/3287]

3.5 elim タクティク で取り上げられていない 帰納法についての多少高度な使い方を説明します。

@suharahiromichi

2019_07_20
*)

From mathcomp Require Import all_ssreflect.

(** ProofCafe のための追加の説明 *)

Section Even.

  (** 自然数の定義と、自然数についての帰納法 *)

  (*
  Inductive nat : Set :=
  | O : nat
  | S : nat -> nat.
  
  Notation "n .+1" := (S n).
  Notation "n .+2" := (S (S n)).
   *)  
  Check nat_ind
  : forall P : nat -> Prop,
    P 0 -> (forall n : nat, P n -> P n.+1) -> forall n : nat, P n.
  Print nat_ind.
  (*
    fun (P : nat -> Prop) (f : P 0) (f0 : forall n : nat, P n -> P n.+1) =>
    fix F (n : nat) : P n :=
    match n as n0 return (P n0) with
    | 0 => f
    | n0.+1 => f0 n0 (F n0)
    end
   *)
  
  (** 偶数の定義と、偶数についての帰納法 *)
  
  Inductive ev : nat -> Prop :=
  | ev_O : ev O
  | ev_SS (n : nat) : ev n -> ev n.+2.

  Check ev_ind
    : forall P : nat -> Prop,
      P 0 -> (forall n : nat, ev n -> (P n -> P n.+2)) -> forall n : nat, ev n -> P n.
  Print ev_ind.
  (* 
     fun (P : nat -> Prop) (f : P 0) (f0 : forall n : nat, ev n -> P n -> P n.+2) =>
     fix F (n : nat) (e : ev n) {struct e} : P n :=
     match e in (ev n0) return (P n0) with
     | ev_O => f
     | ev_SS n0 e0 => f0 n0 e0 (F n0 e0)
     end
   *)
  
  (** 自然数についての、もうひとつの帰納法 *)
  (** 帰納法を指定して使用する。*)
  (** 使い方 *)
  (** バニラCoq ... induction ... using ... *)
  (** Mathcomp .... elim/.... これは、第3 番めの「/」の使い方。 *)
  
  (** nat_ind2 は、Inductive などから自動生成されないので、自分で定義する。 *)
  (** SF/LF/IndPrinciples.v (Induction Principles) では、Definition で与えられている。 *)
  (** 補題として証明してもよい。*)
(*
  Definition nat_ind2 :
    forall (P : nat -> Prop),
    P 0 ->
    P 1 ->
    (forall n : nat, P n -> P n.+2) ->
    forall n : nat, P n :=
       fun P => fun P0 => fun P1 => fun PSS =>
          fix f (n : nat) := match n return P n with
                             0 => P0
                           | 1 => P1
                           | n'.+2 => PSS n' (f n')
                           end.

*)
  Lemma nat_ind2 :
    forall P : nat -> Prop,
      P 0 ->
      P 1 ->
      (forall n : nat, P n -> P (S (S n))) ->
      forall n : nat, P n.
  Proof.
    move=> P HP0 HP1 IH n.
    have H : (P n /\ P (S n)).
    - elim: n.
      + by split.
      + move=> n [] HPn HPsn.
        split=> //=.
          by apply: IH.
    - by case: H.
  Qed.

  Check nat_ind2 : forall P : nat -> Prop,
      P 0 -> P 1 -> (forall n : nat, P n -> P n.+2) -> forall n : nat, P n.
  
  
  (** 偶数かどうかを判定する関数 *)
  
  Fixpoint evenb (n : nat) : bool :=
    match n with
    | O => true
    | O.+1 => false
    | n.+2 => evenb n
    end.

  (** (1) ev n -> evenb n を自然数の帰納法で証明してみる。 *)
  
  Check nat_ind (fun n => ev n -> evenb n)
    : (ev 0 -> evenb 0) ->
      (forall n : nat, (ev n -> evenb n) -> ev n.+1 -> evenb n.+1) ->
      forall n : nat, ev n -> evenb n.
  (*
    任意のnについて、ev n -> evenb n が成り立つとしても、
    n+1 について成り立つわけではない。 
    XXX この説明は適切か確認せよ。XXX
   *)
  
  Theorem ev_even_1' (n : nat) : ev n -> evenb n.
  Proof.
    apply: (nat_ind (fun n => ev n -> evenb n)).
    - done.
    - move=> n' IHev.
  Admitted.          (* OK *)
  
  Theorem ev_even_1 (n : nat) : ev n -> evenb n.
  Proof.
    move=> Hev.
    elim: n Hev.     (* 自然数 n についての帰納法 *)
    - done.          (* ev 0 -> evenb 0 *)
    - move=> n IHev. (* (ev n -> evenb n) -> ev n.+1 -> evenb n.+1 *)
  Admitted.          (* OK *)
  
  (** (2) ev n -> evenb n を偶数の帰納法で証明してみる。 *)
  
  Check ev_ind (fun n => ev n -> evenb n)
    : (ev 0 -> evenb 0) ->
      (forall n : nat, ev n -> (ev n -> evenb n) -> ev n.+2 -> evenb n.+2) ->
      forall n : nat, ev n -> (ev n -> evenb n).
  (** ev n がひとつ多いけれど問題にならない。前提と同じなので必ず成り立つ。 *)
  
  Theorem ev_even_2' (n : nat) : ev n -> evenb n.
  Proof.
    move=> H. move: (H).                    (* duplicate して残す。 *)
    apply: (ev_ind (fun n => ev n -> evenb n)).
    - done.                          (* ev 0 -> evenb 0 *)
    - move=> n' Hev IHeven.          (* (ev n -> evenb n) -> evenb n.+2 *)
      rewrite /= => Hev2.
      apply: IHeven.
      by apply: Hev.
    - by apply: H.                          (* 残しておいたのを使う。 *)
  Qed.
  
  Theorem ev_even_2 (n : nat) : ev n -> evenb n.
  Proof.
    move=> Hev.
    elim: Hev.                       (* Hev : ev n についての帰納法 *)
    - done.                          (* ev 0 -> evenb 0 *)
    - move=> n' Hev IHeven.          (* (ev n -> evenb n) -> evenb n.+2 *)
      rewrite /=.                    (* evenb n.+2 を計算すると evenb n になる。 *)
      done.                          (* 前提と同じ。 *)
      (* 
         前提 Hev : ev n についての帰納法は、
         ev n の成立する n についてのみ着目することができる。
         （sf. Prop.v 参照）
       *)
  Qed.
  (* まとめる。 *)
  Theorem ev_even (n : nat) : ev n -> evenb n.  
      by elim => [| n' Hev IHeven].
  Qed.

  (** (3) ev n -> evenb n を自然数のもうひとつの帰納法で証明してみる。 *)
  
  Check nat_ind2 (fun n => ev n -> evenb n)
    : (ev 0 -> evenb 0) ->
      (ev 1 -> evenb 1) ->
      (forall n : nat, (ev n -> evenb n) -> ev n.+2 -> evenb n.+2) ->
      forall n : nat, ev n -> evenb n.
  (** ev 1 -> evenb 1 が成り立つことに注意してください。前提の矛盾。 *)
  
  Theorem ev_even_3' (n : nat) : ev n -> evenb n.
  Proof.
    apply: (nat_ind2 (fun n => ev n -> evenb n)).
    - done.                                 (* ev 0 -> evenb 0 *)
    - move=> Hev1.                          (* ev 1 -> evenb 1 *)
        by inversion Hev1.
    - move=> n' IHn Hev2.
      simpl.        (* (ev n -> evenb n) -> ev n.+2 -> evenb n.+2 *)
      apply: IHn.
        by inversion Hev2; subst.
  Qed.
  
  Theorem ev_even_3 (n : nat) : ev n -> evenb n.
  Proof.
    elim/nat_ind2 : n => [Hev0 | Hev1 | n IHn Hev] //=.
    - by inversion Hev1.                    (* 前提の矛盾 *)
    - apply: IHn.
        by inversion Hev.                   (* 前提を分解する。 *)
  Qed.
  
  (** (4) 逆の evenb n -> ev n を自然数のもうひとつの帰納法で証明してみる。 *)
  
  Check nat_ind2 (fun n => evenb n -> ev n)
    : (evenb 0 -> ev 0) ->
      (evenb 1 -> ev 1) ->
      (forall n : nat, (evenb n -> ev n) -> evenb n.+2 -> ev n.+2) ->
      forall n : nat, evenb n -> ev n.

  Theorem even_ev' (n : nat) : evenb n -> ev n.
  Proof.
    apply: (nat_ind2 (fun n => evenb n -> ev n)).
    - move=> Hev0.                          (* evenb 0 -> ev 0 *)
        by apply: ev_O.
    - move=> Hev1.
        by inversion Hev1.                  (* 前提の矛盾 *)
    - move=> n' IHn Hev. (* (envnb n -> ev n) -> evenb n -> ev n.+2 *)
      apply: ev_SS.
      apply: IHn.
      simpl in Hev.
        by apply: Hev.
  Qed.
  
  Theorem even_ev (n : nat) : evenb n -> ev n.
  Proof.
    elim/nat_ind2 : n => // [H | n IHn /= Heven].
    - by apply: ev_O.
    - by apply/ev_SS/IHn.
  Qed.
  
  (** もうひとつの例 *)
  Theorem even_ev_ev1 (n : nat) :
    (evenb n -> ev n) /\ (evenb n.+1 -> ev n.+1).
  Proof.
    elim: n => [| n [IHn1 IHn2]]; split => /= H.
    - by apply: ev_O.
    - by [].
    - by apply/IHn2.
    - by apply/ev_SS/IHn1.
  Qed.
  
  (* これから、even_ev を求めることができる。 *)
  (* 結果として、nat についての帰納法だけで証明できた。 *)
  Lemma l_even_ev : (forall n, (evenb n -> ev n) /\ (evenb n.+1 -> ev n.+1)) <->
                    (forall n, evenb n -> ev n).
  Proof.
    split.
    - move=> H n.
      move: (H n) => {H}.
      case=> Hn Hn1 Heven.
        by apply/Hn/Heven.
    - move=> H n.
      split.
      + by apply: (H n).
      + by apply: (H n.+1).
  Qed.
  
  Theorem even_ev'' (n : nat) : evenb n -> ev n.
  Proof.
    apply/l_even_ev : n.
      by apply: even_ev_ev1.
  Qed.
  
End Even.

Section Test.

  (** Mathcomp の odd は、単純な n => n.+1 の再帰で定義されているので、
      自然数の帰納法で証明できる。(see. ssrnat.v)
      
      Fixpoint odd n := if n is n'.+1 then ~~ odd n' else false.
      これは、偶奇の結果をbool値としてみると、+.1 でfalse/trueが反転することを使う。
      
      odd_add や odd_b なども比較的簡単に証明できる。
   *)
  
  (** evenb に適用してみた場合 *)
  Lemma evenb__not_evenb (n : nat) : evenb n = ~~ evenb n.+1.
  Proof.
    elim: n => [| n IHn] //.
      by rewrite [evenb n.+2]/= IHn Bool.negb_involutive.
  Qed.

  (** odd と evenb の関係  *)
  Lemma odd__not_evenb (n : nat) : odd n = ~~ evenb n.
  Proof.
    elim: n => [| n IHn] //.
    rewrite [odd n.+1]/= IHn negbK.
      by rewrite evenb__not_evenb.
  Qed.

  (** bool値のおいて、二重否定を除去する補題。ついでに覚えておきましょう。 *)
  Check negbK : forall b : bool, ~~ ~~ b = b.
  Check Bool.negb_involutive : forall b : bool, ~~ ~~ b = b.

End Test.

(* END *)
