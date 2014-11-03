(**
DFA (決定性有限オートマトン）を定義してみる。

文献[1]：Tukuba Coq Users' Grup 「Coqによる定理証明」
坂口さん著「反復定理で遊ぼう」

実装にあたっては、
文献[2]: https://www.ps.uni-saarland.de/~doczkal/regular/
を参考にしているが、そのパッケージは使用しない。
 *)

Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq.
Require Import fintype finset div.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

(**
以下のDFA M = (Q, Σ, δ, q0, F) を考える（文献[1]のp.4 例1.9）。

Q = {0, 1, 2, 3, 4, 5}    オートマトンの状態
Σ = {0, 1}                受理するアルファベット
δ(q, a) = (q + 2) mod 6 (a = 0)  状態遷移関数
δ(q, a) = (q + 3) mod 6 (a = 1)
q0 = 0                    初期状態
F = {0}                   終了状態
*)

Record dfa : Type :=
  {
    dfa_state :> finType;                          (* Q *)
    dfa_char :> finType;                           (* Σ *)
    dfa_s : dfa_state;                             (* q0 *)
    dfa_fin : pred dfa_state;                      (* F *)
    dfa_trans : dfa_state -> dfa_char -> dfa_state (* δ *)
  }.

(** オートマトンの状態 *)
Definition Q : predArgType := 'I_6.         (* {0, 1, 2, 3, 4, 5}  *)
(** オートマトンの初期状態はq0 *)
Definition q0 : Q. Proof. have : 0 < 6 by []. apply Ordinal. Defined.
Compute (nat_of_ord q0).                    (* 0 : nat *)
Definition q1 : Q. Proof. have : 1 < 6 by []. apply Ordinal. Defined.
Definition q2 : Q. Proof. have : 2 < 6 by []. apply Ordinal. Defined.
Definition q3 : Q. Proof. have : 3 < 6 by []. apply Ordinal. Defined.
Definition q4 : Q. Proof. have : 4 < 6 by []. apply Ordinal. Defined.
Definition q5 : Q. Proof. have : 5 < 6 by []. apply Ordinal. Defined.
(** nat を Qに変換する。 *)
Lemma lt0_6 : 0 < 6. Proof. by []. Qed.
Definition qn (n : nat) : Q := Ordinal (@ltn_pmod n 6 lt0_6).
Compute (nat_of_ord (qn 1)).                (* 1 : nat *)

(** アルファベット  *)
Definition Sigma : predArgType := 'I_2.     (* {0, 1} *)
Definition a0 : Sigma. Proof. have : 0 < 2 by []. apply Ordinal. Defined.
Definition a1 : Sigma. Proof. have : 1 < 2 by []. apply Ordinal. Defined.
(** nat を Sigmaに変換する。 *)
(* Qのときと、少し違うことをしているが大差はない。 *)
Lemma lt2_pmod (n : nat) : n %% 2 < 2. Proof. by apply ltn_pmod. Qed.
Definition an (n : nat) : Sigma := Ordinal (lt2_pmod n).
Compute (nat_of_ord (an 1)).                (* 1 : nat *)

(** 状態遷移関数 *)
Definition delta (q : Q) (a : Sigma) :=
  match (nat_of_ord a) with
    | 0 => qn (nat_of_ord q).+2
    | _ => qn (nat_of_ord q).+3
  end.
(* テスト  *)
Goal delta q0 a0 == q2. Proof. by []. Qed.
Goal delta q1 a0 == q3. Proof. by []. Qed.
Goal delta q1 a0 == q3. Proof. by []. Qed.

(** オートマトンの終了状態 *)
Definition Fin x := x \in [:: q0].
Compute Fin q0.                             (* true *)
Compute Fin q1.                             (* false *)

(** オートマトンの定義 *)
Definition mydfa := Build_dfa q0 Fin delta.
(* テスト *)
Goal q0 \in @dfa_fin mydfa == true. Proof. by []. Qed.
Goal @dfa_trans mydfa q0 a0 == q2. Proof. by []. Qed.

Section DFA_Acceptance.
  Variable A : dfa.
  
  Fixpoint dfa_accept (x : A) w : bool :=
    if w is a :: w' then
      dfa_accept (dfa_trans x a) w'
    else
      x \in @dfa_fin A.
  
  Lemma dfa_accept_cons (x : A) a w :
    dfa_accept x (a :: w) = dfa_accept (dfa_trans x a) w.
  Proof.
      by rewrite -simpl_predE /=.
  Qed.
End DFA_Acceptance.
  
Arguments dfa_s [d].
Arguments dfa_trans [d] x a.
Arguments dfa_accept [A] x w.
Arguments dfa_accept_cons [A] x a w.

Goal @dfa_accept mydfa dfa_s [::] == true.
Proof.
  by [].
Qed.

Goal @dfa_accept mydfa dfa_s [:: a0; a1; a0; a1; a0] == true.
Proof.
  by [].
Qed.

(**
 その他の 'I_6 についての補題
*)

Definition p3 : 'I_5. Proof. have : 3 < 5 by []. apply Ordinal. Defined.
Compute lift q3 p3.                         (* 'I_6 *)
Compute nat_of_ord (lift q3 p3).            (* 5 : nat *)

Goal #| 'I_6 | = 6.
Proof.
  by apply card_ord.
Qed.

Goal q0 \in enum 'I_6.
Proof.
  apply mem_enum.
Qed.

Goal size (enum 'I_6) = 6.
Proof.
  by apply size_enum_ord.
Qed.

Goal index q0 (enum 'I_6) = q0.
Proof.
  by apply index_enum_ord.
Qed.

Goal [seq val i | i <- enum 'I_6] = [:: 0; 1; 2; 3; 4; 5].
Proof.
  by rewrite val_enum_ord.
Qed.

Goal ord_enum 6 =i enum 'I_6.
Proof.
  move=> x.
  apply/idP/idP => H.
  - by apply mem_enum.
  - by apply mem_ord_enum.
Qed.

Lemma eq_6_6 : 6 = 6. by []. Qed.
Check cast_ord eq_6_6 q0 : 'I_6.            (* 型を変える。 *)
Check lshift 0 q5 : 'I_6.                   (* 型を変える。 *)

Lemma le_6_8 : 6 <= 8. by []. Qed.
Check widen_ord le_6_8 q0 : 'I_8.           (* 型を変える。 *)
Check lshift 2 q5 : 'I_8.                   (* 型を変える。 *)
Check @lshift 6 2 q5 : 'I_8.                (* 型を変える。 *)
Check @rshift 2 6 q5 : 'I_8.                (* 型を変える。 *)

(* END *)
