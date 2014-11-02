(**
DFA (決定性有限オートマトン）を定義してみる。

文献[1]：Tukuba Coq Users' Grup 「Coqによる定理証明」
坂口さん著「反復定理で遊ぼう」

実装にあたっては、
文献[2]: https://www.ps.uni-saarland.de/~doczkal/regular/
を参考にしているが、そのパッケージは使用しない。
 *)

Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq.
Require Import fintype div.

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


(* **************************** *)
(* **************************** *)
(*         以下 作成中           *)
(* **************************** *)
(* **************************** *)

Lemma eq_6_6 : 6 = 6. by []. Qed.
Lemma le_6_7 : 6 <= 7. by []. Qed.

Check cast_ord eq_6_6 q0 : 'I_6.            (* 型を変える *)
Check widen_ord le_6_7 q0 : 'I_7.           (*  *)

Goal #| 'I_6 | = 6.
Proof.
  (* rewrite cardE size_enum_ord. *)
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


(* *********************** *)
  
Require Import misc regexp.

Set Implicit Arguments.

Section FA.
Variable char : finType.
Definition word := seq char.

(** * Finite Automata *)

(** ** Deterministic Finite Automata *)

Record dfa : Type := mkdfa
  {
    dfa_state :> finType;
    dfa_s : dfa_state;
    dfa_fin : pred dfa_state;
    dfa_trans : dfa_state -> char -> dfa_state

  }.

(** For DFAs, we use the direct recursive defintion of acceptance
    as well as a definition in terms of runs. The latter is used
    in the translation of DFAs to regular expressions. *)


Fixpoint dfa_accept (A : dfa) (x : A) w :=
  if w is a :: w' then
    dfa_accept A (dfa_trans A x a) w'
  else
    x \in dfa_fin A.

Arguments dfa_trans [d] x a.
Arguments dfa_accept [A] x w.


Section DFA_Acceptance.
Variable A : dfa.

Lemma dfa_accept_cons (x : A) a w :
  a :: w \in dfa_accept x = (w \in dfa_accept (dfa_trans x a)).
Proof. by rewrite -simpl_predE /=. Qed.


(** We define a run of w on the automaton A
    to be the list of states x_1 .. x_|w|
    traversed when following the edges labeled
    w_1 .. w_|w| starting in x.
    So the run on [x] does not include [x] *)

Fixpoint dfa_run (x : A) (w : word) : seq A :=
  if w is a :: w' then dfa_trans x a :: dfa_run (dfa_trans x a) w' else [::].

Lemma dfa_run_take x w n : take n (dfa_run x w) = dfa_run x (take n w).
Proof. elim: w x n => [|a w IHw] x n //. case: n => [|n] //=. by rewrite IHw. Qed.

Lemma dfa_run_cat x w1 w2 :
  dfa_run x (w1 ++ w2) = dfa_run x w1 ++ dfa_run (last x (dfa_run x w1)) w2.
Proof. elim: w1 w2 x => [|a w1 IHw1] w2 x //. simpl. by rewrite IHw1. Qed.

Definition delta x w := last x (dfa_run x w).

Lemma delta_cons x a w : delta x (a :: w) = delta (dfa_trans x a) w.
Proof. by []. Qed.

Lemma delta_cat x w1 w2 : delta x (w1 ++ w2) = delta (delta x w1) w2.
Proof. by rewrite /delta dfa_run_cat last_cat. Qed.

Definition delta_s w := delta (dfa_s A) w.

Lemma delta_accept (x : A) w : (w \in dfa_accept x) = (delta x w \in dfa_fin A).
Proof. elim: w x => [|a w IHw] x //. by rewrite /= -IHw. Qed.

Lemma dfa_trans1 x w a :
  dfa_trans (delta x w) a = delta x (w ++ [::a]).
Proof. elim: w x a => [|b w IHw] x a //=. by rewrite !delta_cons IHw. Qed.

End DFA_Acceptance.

Definition dfa_lang A := [pred w | dfa_accept (dfa_s A) w].

Arguments delta_s A w.
Arguments delta [A] x w.
Arguments dfa_accept A x w.

(** ** Regular Operations on Automata *)

(** Primitive automata **)
Definition dfa_void :=
  {|
    dfa_s := tt;
    dfa_fin x := false;
    dfa_trans x a := tt
  |}.

Goal forall (x : dfa_void), ~~ dfa_accept x [::].
Proof.
  rewrite /dfa_void /dfa_accept /=.
  move=> x.
  by [].
Qed.  

Lemma dfa_void_correct (x: dfa_void) w: ~~ dfa_accept x w.
Proof. by elim: w x => [|a w IHw] //=. Qed.

Definition dfa_eps :=
 {|
   dfa_s := true;
   dfa_fin := id ;
   dfa_trans x a := false
 |}.

Goal forall (x : dfa_void), ~~ dfa_accept x [::].
Proof.
  rewrite /dfa_void /dfa_accept /=.
  move=> x.
  by [].
Qed.  

Goal forall (x : dfa_eps), dfa_accept x [::].
Proof.
  rewrite /dfa_void /dfa_accept /=.
  move=> x.
  admit.
Qed.  

(* XXXXXXXXXXXXXXX *)

Lemma dfa_eps_correct : dfa_lang dfa_eps =i pred1 [::].
Proof.
  have H: (forall w, ~~ @dfa_accept dfa_eps false w) by elim => [|a v IHv] //=.
  elim => [|a w IHw] //. apply/idP/idP. exact: H.
Qed.

(** Operations on deterministic automata. **)
Section DFAOps.

Variable op : bool -> bool -> bool.
Variable A1 A2 : dfa.

(** Complement automaton **)
Definition dfa_compl :=
 {|
    dfa_s := dfa_s A1;
    dfa_fin := [predC (dfa_fin A1)];
    dfa_trans := (@dfa_trans A1)
  |}.

Lemma dfa_compl_correct w :
  w \in dfa_lang dfa_compl = (w \notin dfa_lang A1).
Proof.
  rewrite /dfa_lang !inE {2}/dfa_compl /=.
  elim: w (dfa_s _) => [| a w IHw] x //=.
Qed.

(** BinOp Automaton *)

Definition dfa_op  :=
  {| dfa_s := (dfa_s A1, dfa_s A2);
     dfa_fin q := let (x1,x2) := q in op (dfa_fin A1 x1) (dfa_fin A2 x2);
     dfa_trans x a := (dfa_trans x.1 a, dfa_trans x.2 a) |}.

Lemma dfa_op_correct w :
  w \in dfa_lang dfa_op = op (w \in dfa_lang A1) (w \in dfa_lang A2).
Proof.
  rewrite /dfa_lang /=. move: (dfa_s A1) (dfa_s A2) => x y.
  elim: w x y => [| a w IHw] //= x y. by rewrite dfa_accept_cons IHw.
Qed.

End DFAOps.

Section Reachability.
  Variable A : dfa.

  Definition dfa_trans_some (x y : A) := [exists a, dfa_trans x a == y].

  Lemma step_someP x y :
    reflect (exists w, delta x w == y) (connect dfa_trans_some x y).
  Proof.
    apply: (iffP connectP) => [[p]|[w]].
    - elim: p x y => [x y _ -> |z p IHp x y /= /andP[H1 H2 e]]; first by exists [::].
      case: (IHp _ _ H2 e) => w e'.
      case/existsP : H1 => [a /eqP Ha]. exists (a::w). by rewrite delta_cons Ha.
    - elim: w x y => [x y /eqP e | a w IHw x y /IHw [p p1 p2]]; first by exists [::].
      exists (dfa_trans x a::p) => //. rewrite /= p1 andbT. by apply/existsP; exists a.
  Qed.

  Definition reachable := connect dfa_trans_some (dfa_s A).
End Reachability.


Definition dfa_lang_empty A := [forall (x | reachable A x), x \notin dfa_fin A].

Lemma dfa_lang_emptyP A :
  reflect (dfa_lang A =i pred0) (dfa_lang_empty A).
Proof.
  apply: (iffP forall_inP) => [H w| H x R].
  - apply/negbTE. rewrite /dfa_lang delta_accept H //.
    apply/step_someP. by exists w.
  - apply/negP => F. case/step_someP : R => w /eqP Hw.
    suff: w \in dfa_lang A by rewrite H.
    by rewrite delta_accept Hw.
Qed.

Section Equivalence.

  Definition dfa_sym_diff A1 A2 := dfa_op addb A1 A2.

  Definition dfa_equiv A1 A2 := dfa_lang_empty (dfa_sym_diff A1 A2).

  Lemma dfa_equiv_correct A1 A2 :
    reflect (dfa_lang A1 =i dfa_lang A2) (dfa_equiv A1 A2).
  Proof.
    apply: (iffP (dfa_lang_emptyP _)) => H w.
    - move/negbT: (H w). rewrite !dfa_op_correct -addNb.
      move/addbP. by rewrite negbK.
    - apply/negbTE. by rewrite !dfa_op_correct H addbb.
  Qed.
End Equivalence.

