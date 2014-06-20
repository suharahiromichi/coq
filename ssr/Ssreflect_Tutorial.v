(** An Ssreflect Tutorial *)

(** http://hal.archives-ouvertes.fr/docs/00/40/77/78/PDF/RT-367.pdf  *)

Require Import ssreflect ssrbool eqtype ssrnat ssrfun.

(** 2 The Coq tutorial brieﬂy translated to ssreﬂect *)

(** 2.1 Hilbert’s axiom S *)

Section HilbertSaxiom.
Variables A B C : Prop.

Lemma HilbertS : (A -> B -> C) -> (A -> B) -> A -> C.
Proof.
  move=> hAiBiC hAiB hA.
  move: hAiBiC.
(**
[move: hAiBiC]

は、Legacy Coqの次と同じ。

[revert hAiBiC]

また、

[move: (hAiBiC)]

は、Legacy Coqの次と同じ。

[generalize hAiBiC]
*)
  apply.
    by [].                                  (** なにもせず done *)
    by apply: hAiB.
(**
[by apply: hAiB]

は、以下の書き換えができる。

[by move: hAiB; apply] ただし [by (move: hAiB; apply)] である。

[move: hAiB; apply; by []]
*)
Qed.

Lemma HilbertS' : (A -> B -> C) -> (A -> B) -> A -> C.
Proof.
  move=> hAiBiC hAiB hA.
  move: hAiBiC.
  by apply; [|apply: hAiB].
(**
最初のapply で分かれるゴールを一度に表す場合だが、
これはLegacy Coqの表記である。
また、[|apply: hAiB]は、「;」に続いているので、複数ゴールへの分岐である。
ただし、apply; by [|apply: hAiB]. とすると、tryの意味になる。
(「.」、do、byに続く場合はtry。「;」に続く場合は、複数ゴールへの分岐）
その証拠に、apply; by [apply: hAiB|]. でも証明を閉じてまう。
firstは、apply: hAiBについでidをtryする。
lastは、apply: hAiBをtryしてうまくいく。
*)
Qed.

Hypotheses (hAiBiC : A -> B -> C) (hAiB : A -> B) (hA : A).

Lemma HilbertS2 : C.
Proof.
(**
最初のゴールから証明する場合。
*)
  apply: hAiBiC; first by apply: hA.
  exact: hAiB.
(**
[exact: hAiB]

は、以下の書き換えができる。

[move: hAiB. exact]
*)
Qed.

Lemma HilbertS2' : C.
Proof.
(**
最後（2番目）のゴールから証明する場合。
*)
  apply: hAiBiC; last exact: hAiB.
  apply: hA.
Qed.

Lemma HilbertS3 : C.
Proof.
(**
[apply: hA]

は、doneで置き換えられるので、全体は次に書き換えができる。

[apply: hAiBiC; last exact: hAiB; done]
*)
  by apply: hAiBiC; last exact: hAiB.
Qed.

Lemma HilbertS4 : C.
Proof.
(**
項を直接適用する場合。
*)
  Check (hAiBiC _ (hAiB _)).                (** C *)
  Check (hAiBiC hA).                        (** B -> C *)
  Check (hAiB hA).                          (** B *)
  Check (hAiBiC hA (hAiB hA)).              (** C *)
  Check (hAiBiC _ (hAiB _)).                (** C *)
  exact: (hAiBiC _ (hAiB _)).
Qed.

Lemma HilbertS5 : C.
Proof.
  exact: hAiBiC (hAiB hA).
  (**
[move: (hAiBiC (hAiB hA)); by apply.] ではなく、
[move: (hAiB hA); move hAiBiC; by apply.] である。
*)
Qed.

Lemma HilbertS6 : C.
Proof.
  exact: HilbertS5.
Qed.
End HilbertSaxiom.

(** 2.2 Logical connectives *)
(**
[
Inductive bool : Set :=
| true : bool
| false : bool.
]
*)

Section Symmetric_Conjunction_Disjunction.
Require Import Datatypes.

(**
[
Inductive and (A : Prop) (B : Prop) : Prop :=
conj : A -> B -> A /\ B.
]
*)

Lemma andb_sym : forall A B : bool, A && B -> B && A.
Proof.
  case.
    by case.
    by [].                                  (** なにもせず done *)
Qed.

Lemma andb_sym2 : forall A B : bool, A && B -> B && A.
Proof.
    by case; case.
Qed.

Lemma andb_sym3 : forall A B : bool, A && B -> B && A.
Proof.
    by do 2! case.
Qed.

Lemma and_sym : forall A B : Prop, A /\ B -> B /\ A.
Proof.
    by move=> A1 B [].
(**
[by move=> A1 B []]

の最後の[[]]は、(A /\ B)で場合分けするcaseであり、
以下の書き換えができる。

[by move=> A1 B; move=> []]

または、

[by move=> A1 B; case=> []]
*)
Qed.

(**
[
Inductive or (A : Prop) (B : Prop) : Prop :=
| or_introl : A -> A \/ B
| or_intror : B -> A \/ B.
]
*)

Lemma or_sym : forall A B : Prop, A \/ B -> B \/ A.
Proof.
    by move=> A B [hA | hB]; [apply: or_intror | apply: or_introl].
(**
[move=> A B [hA | hB]]

は、次と同じである。

[move=> A B; move=> [hA | hB]]

または、

[move=> A B; case=> [hA | hB]]
*)
Qed.

Lemma or_sym2 : forall A B : bool, A \/ B -> B \/ A.
Proof.
  by move=> [] [] AorB;
(**
[move=> [] [] AorB]

は、次と同じである。

[move=> []; move=> []; move=> AorB]

[case=> []; case=> []; move=> AorB]

[case; case; move=> AorB]
 *)
           apply/orP;
(**
これは、lemma orP をreflectする。orPはviewともよばれる。

[lemma orP : reflect (b1 \/ b2) (b1 || b2)]

ただし、

[
Inductive reflect (P : Prop) : bool -> Set :=
  | ReflectT of P : reflect P true
  | ReflectF of ~ P : reflect P false.
]

[true \/ true] が [true || true] に書き換えられる。

[apply]であるのでのゴール全体に対して、
また[;]でつながれているのですべてのゴールに対して行われる。
  *)
           move/orP : AorB.
(**
[move/orP : AorB]

は、次と同じである。

[move: AorB; move/orP]

[move/P]はスタックの先頭を変更するのに対して、

[apply/P]はゴール全体（すべてのゴールではない）を変更する。
 *)
Qed.

Lemma or_sym2' : forall A B : bool, A \/ B -> B \/ A.
Proof.
    (** 展開して書いた例 *)
    move=> [] [] AorB.
    (** [true \/ true] *)
    apply/orP.
    (** [true || true] *)
    move: AorB.
    (** [true \/ true -> true || true] *)
    move/orP.
    (** [true || true -> true || true] *)
    done.
    apply/orP.
    move: AorB. move/orP. done.
    apply/orP.
    move: AorB. move/orP. done.
    apply/orP.
    move: AorB. move/orP. done.
Qed.
End Symmetric_Conjunction_Disjunction.

(** 2.3 Two so-called paradoxes *)

Section R_sym_trans.
Variables (D : Type) (R : D -> D -> Prop).

Hypothesis R_sym : forall x y, R x y -> R y x.
Hypothesis R_trans : forall x y z, R x y -> R y z -> R x z.

Lemma refl_if : forall x : D, (exists y, R x y) -> R x x.
Proof.
  move=> x [y Rxy].
(**
[move=> x [y Rxy]]

は、次と同じである。

[move=> x; case=> y Rxy]

または、

[move=> x [y] Rxy]
*)
    by apply: R_trans _ (R_sym _ y _).
(* by apply: R_trans Rxy (R_sym x y Rxy). *)
Qed.

(* 分解した書き方。move: の順番が逆になっていることに注意！ *)
Lemma refl_if' : forall x : D, (exists y, R x y) -> R x x.
Proof.
  move=> x.
  case=> [y Rxy].
  move: (R_sym x y Rxy).
  move: Rxy.
  move: R_trans.
  apply.
Qed.
End R_sym_trans.

Section Smullyan_drinker.
Variables (D : Type)(P : D -> Prop).

Hypothesis (d : D) (EM : forall A, A \/ ~A). (* 排中律 *)

Lemma drinker : exists x, P x -> forall y, P y.
Proof.
  case: (EM (exists y, ~P y)) => [[y notPy] | nonotPy];
(**
[EM (exists y : D, ~ P y)] は、
[(exists y : D, ~ P y) \/ ~ (exists y : D, ~ P y)]
である。これをスタックの先頭に積んで、それで条件分けする。

[case: (EM (exists y, ~P y))]

は、次と同じである。

[move: (EM (exists y, ~P y)); case]

また、

[case: (EM (exists y, ~P y)) => [[y notPy] | nonotPy]]

は、次と同じである。

[have [[y notPy] | nonotPy] := EM (exists y, ~P y)]

[have H := ...]は、証明を直接与えるものなので、

初めのゴールに対して[y : D]と[notPy : ~ P y]、

次のゴールに対して[nontPy : ~ (exists y : D, ~ P y)]

の証明が与えられる。
*)
  first by exists y.
    exists d => _ y;
(**
[exists d => _ y]

は、次と同じ。

[exists d; move => _ y]
*)
      case: (EM (P y)) => // notPy.
(**
[//] は、[try done] の意味。
*)
      by case: nonotPy; exists y.
(**
前提の、[nonotPy : ~ (exists y : D, ~ P y)] なので、
[case: nonotPy] 

の結果は、

[exists y0 : D, ~ P y0]

となる。
*)
Qed.

(* まとめて書いてみる。 *)
Lemma drinker' : exists x, P x -> forall y, P y.
Proof.
  (* 排中律 (exists y : D, ~ P y) \/ ~ (exists y : D, ~ P y) *)
  move: (EM (exists y, ~P y)).
  (* \/の左右で場合分けする。 左の方は existの場合わけまでする。 *)
  case=> [[y notPy] | nonotPy].
  (* ここまで、ゴールは触っていないことに注意！ *)

    (* 前提が、~ P y のとき *)
      by exists y.
    (* 前提が、~ (exists y, ~ P y) のとき *)
    exists d => _ y.
    (* 排中律 (P y \/ ~ P y) *)
    move: (EM (P y)).
    (* \/の左右で場合分けする。 左が直ちにとける。 *)
    case=> // notPy.
      (* ~ (exists y, ~ P y) で場合分けする。 *)
      by case: nonotPy; exists y.
Qed.

Lemma drinker'' : exists x, P x -> forall y, P y.
Proof.
  have H := EM (exists y, ~P y); move: H.
  case=> [[y notPy] | nonotPy].
  (*
これは、一行でかける。
[have [[y notPy] | nonotPy] := EM (exists y, ~P y)]
 *)
    (* 前提が、~ P y のとき *)
      by exists y.
    (* 前提が、~ (exists y, ~ P y) のとき *)
    exists d => _ y.
    (* 排中律 (P y \/ ~ P y) *)
    move: (EM (P y)).
    (* \/の左右で場合分けする。 左が直ちにとける。 *)
    case=> // notPy.
      (* ~ (exists y, ~ P y) で場合分けする。 *)
      by case: nonotPy; exists y.
Qed.

End Smullyan_drinker.


(* 2.4 Rewriting with (Leibniz) equalities and deﬁnitions *)

Section Equality.
Variable f : nat -> nat.
Hypothesis f00 : f 0 = 0.

Lemma fkk : forall k, k = 0 -> f k = k.
Proof.
  move=> k k0.
    by rewrite k0.
Qed.

Lemma fkk2 : forall k, k = 0 -> f k = k.
Proof.
    by move=> k ->.
(**
[move=> k ->.]

は、次と同じである。スタックの先頭（hyp）を使って書き換える。

[move=> k hyp. rewrite {} hyp]
*)
Qed.

Variable f10 : f 1 = f 0.
Lemma ff10 : f (f 1) = 0.
Proof.
    by rewrite f10 f00.
(**
[rewrite f10 f00]

は、次と同じである。

[rewrite f10; rewrite f100]
*)
Qed.

Variables (D : eqType) (x y : D).

(**
[lemma eqP : reflect (e1 = e2) (e1 == e2)]
*)

Lemma eq_prop_bool : x = y -> x == y.
Proof.
    (* 前提の x = y を x == y にリフレクションする。 *)
    by move/eqP.
Qed.

Lemma eq_bool_prop : x == y -> x = y.
Proof.
    (* 前提の x == y を x = y にリフレクションする。 *)
    by move/eqP.
Qed.
End Equality.

Section Using_Definition.
Variable U : Type.

Definition set := U -> Prop.
Definition subset (A B : set) := forall x, A x -> B x.
Definition transitive (T : Type) (R : T -> T -> Prop) :=
  forall x y z, R x y -> R y z -> R x z.

Lemma subset_trans : transitive set subset.
Proof.
(**
[rewrite /transitive /subset]

は、次と同じである。

[unfold transitive, subset]
*)
  rewrite /transitive /subset => x y z subxy subyz t xt.
(**
[rewrite /transitive /subset => x y z subxy subyz t xt]

は、次と同じである。

[rewrite /transitive /subset; move => x y z subxy subyz t xt]
*)
  by apply: subyz; apply: subxy.
Qed.

Lemma subset_trans2 : transitive set subset.
Proof.
  move=> x y z subxy subyz t.
    (* move/subxy は、前提 x t を y t にリフレクションする。 *)
    (* move/subyz は、前提 y t を z t にリフレクションする。 *)
    by move/subxy; move/subyz.
Qed.

(** 実際は以下と同じ *)
Lemma subset_trans2'' : transitive set subset.
Proof.
  move=> x y z subxy subyz t.
  move=> H.
(**
[subxy : forall x0 : U, x x0 -> y x0]
*)
  apply subxy in H.
(**
[subyz : forall x : U, y x -> z x]
 *)
  apply subyz in H.
  by [].
Qed.
End Using_Definition.

(** 3 Arithmetic for Euclidean division *)

(** 3.1 Basics *)
Variable n : nat.

(* 
[
Inductive nat : Set :=
| O : nat
| S : nat -> nat.
]
*)
Lemma three : S (S (S O)) = 3 /\ 2 = 0.+1.+1.
Proof. by [].
Qed.

Lemma concrete_plus : plus 16 64 = 80.
Proof.
    (* simpl. *)
    by [].
Qed.

(*
Inductive le (n : nat) : nat -> Prop :=
| le_n : (n <= n)
| le_S : forall m : nat, (n <= m) -> (n <= m.+1).
*)

Lemma concrete_le : le 1 3.
Proof.
    by apply: (Le.le_trans _ 2); apply: Le.le_n_Sn.
Qed.

Fixpoint subn_rec (m n : nat) {struct m} :=
  match m, n with
    | m'.+1, n'.+1 => (m' - n')
    | _, _ => m
end.
Eval compute in subn_rec 5 3.               (* 2 *)

Lemma concrete_big_leq : 0 <= 51.
Proof.
    by [].
Qed.


Lemma semi_concrete_leq : forall n m, n <= m -> 51 + n <= 51 + m.
Proof.
    by [].
Qed.

Lemma concrete_arith : (50 < 100) && (3 + 4 < 3 * 4 <= 17 - 2).
Proof.
    by [].
Qed.

(* plusの可換性 *)
Lemma plus_commute : forall n1 m1, n1 + m1 = m1 + n1.
Proof.
    by elim=> [| n IHn m]; [elim | rewrite -[n.+1 + m]/(n + m).+1 IHn; elim: m].
Qed.

(* 展開して書く *)
Lemma plus_commute' : forall n1 m1, n1 + m1 = m1 + n1.
Proof.
  elim=> [| n IHn m].
  + by elim.
  + rewrite -[n.+1 + m]/(n + m).+1.         (* n.+1 + m を (n + m).+1 で置き換える。 *)
    (* change (n.+1 + m) with (n + m).+1. とおなじ。 *)
    (* rewrite -[n.+1 + m]/(n.+1 + m).  これは、 なにもしないが -をとると。。。 *)

(*
No 6455 p.39
rewrite -[ term1 ]/ term2. is equivalent to: change term1 with term.
If term2 is a single constant and term1 head symbol is not term2 , then the head symbol
of term1 is repeatedly unfolded until term2 appears.
*)
    rewrite IHn.
    elim: m.
    - by [].
    - by [].
Qed.

(* 3.2 Deﬁnitions *)

Definition edivn_rec d :=
  fix loop (m q : nat) {struct m} :=
  if m - d is m'.+1 then loop m' q.+1 else (q, m).
Eval compute in edivn_rec 3.-1 10 0.        (* 3 あまり 1 *)
(* 
計算の様子。
d   m   q   m-d   m'  q+1
2  10   0    8    7   1
2   7   1    5    4   2
2   4   2    2    1   3
2   1   3    0    -   - .. else .. (q, m) = (3, 1)
 *)
Definition edivn m d :=
  if d > 0 then edivn_rec d.-1 m 0 else (0, m).
Eval compute in edivn 10 3.                 (* 3 あまり 1 *)

(* *** *)
Definition edivn_rec2 d := fix loop (m q : nat) {struct m} :=
  if m - (d - 1) is m'.+1 then loop m' q.+1 else (q, m).

Definition edivn2 m d :=
  if d > 0 then edivn_rec2 d m 0 else (0, m).
Eval compute in edivn2 10 3.                (* 3 あまり 1 *)

(*
[
Definition edivn_rec3 d := fix loop (m q : nat) {struct m} :=
  if m - d is m'.+1 then term1 else term2.
]
*)

(*
[
CoInductive edivn_spec (m d : nat) : nat * nat -> Type :=
  EdivnSpec q r of m = q * d + r & (d > 0) ==> (r < d) :
    edivn_spec m d (q, r).
]
*)
CoInductive edivn_spec (m d : nat) : nat * nat -> Type :=
  EdivnSpec :
    forall q r, m = q * d + r -> (d > 0 -> r < d) -> edivn_spec m d (q, r).

(* 3.3 Results *)

Lemma edivnP : forall m d, edivn_spec m d (edivn m d).
Proof.
  rewrite /edivn => m [|d] //=; rewrite -{1}[m]/(0 * d.+1 + m).
  elim: m {-2}m 0 (leqnn m) => [|n IHn] [|m] q //=; rewrite ltnS => le_mn.
  rewrite subn_if_gt; case: ltnP => [// | le_dm].
  rewrite -{1}(subnK le_dm) -addnS addnA.
  rewrite addnAC -mulSnr.                   (* addnAC を追加した。  *)
  apply (IHn (m - d) q.+1).                 (* apply: IHn でもよい。 *)
  apply: leq_trans le_mn; exact: leq_subr.
Qed.

CoInductive ltn_xor_geq (m : nat) (n : nat) : bool -> bool -> Set :=
| LtnNotGeq : m < n -> ltn_xor_geq m n false true
| GeqNotLtn : n <= m -> ltn_xor_geq m n true false.

Lemma edivn_eq : forall d q r, r < d -> edivn (q * d + r) d = (q, r).
Proof.
  move=> d q r lt_rd; have d_pos: 0 < d by exact: leq_trans lt_rd.
  case: edivnP lt_rd => q' r'; rewrite d_pos /=.
    wlog: q q' r r' / q <= q' by case (ltnP q q'); last symmetry; eauto.
  rewrite leq_eqVlt; case: eqP => [-> _|_] /=; first by move/addnI->.
    rewrite -(leq_pmul2r d_pos); move/leq_add=> Hqr Eqr _; move/Hqr {Hqr}.
    by rewrite addnS ltnNge mulSn -addnA Eqr addnCA addnA leq_addr.
Qed.

(* 3.4 Parametric type families and alternative speciﬁcations *)

CoInductive edivn_spec3 (m d : nat) : nat * nat -> Type :=
  EdivnSpec3 q r of m = q * d + r & (d > 0) ==> (r < d) :
    edivn_spec3 m d (q, r).

CoInductive edivn_spec_right : nat -> nat -> nat * nat -> Type :=
  EdivnSpec_right m d q r of m = q * d + r & (d > 0) ==> (r < d) :
    edivn_spec_right m d (q, r).

CoInductive edivn_spec_left (m d : nat)(qr : nat * nat) : Type :=
  EdivnSpec_left of m = (fst qr) * d + (snd qr) & (d > 0) ==> (snd qr < d) :
    edivn_spec_left m d qr.

Lemma edivnP_right : forall m d, edivn_spec_right m d (edivn m d).
 (* 証明は、edivnP と同じ。 *)
  rewrite /edivn => m [|d] //=; rewrite -{1}[m]/(0 * d.+1 + m).
  elim: m {-2}m 0 (leqnn m) => [|n IHn] [|m] q //=; rewrite ltnS => le_mn.
  rewrite subn_if_gt; case: ltnP => [// | le_dm].
  rewrite -{1}(subnK le_dm) -addnS addnA.
  rewrite addnAC -mulSnr.                   (* addnAC を追加した。  *)
  apply (IHn (m - d) q.+1).                 (* apply: IHn でもよい。 *)
  apply: leq_trans le_mn; exact: leq_subr.
Qed.

Lemma edivnP_left : forall m d, edivn_spec_left m d (edivn m d).
 (* 証明は、edivnP と同じ。 *)
  rewrite /edivn => m [|d] //=; rewrite -{1}[m]/(0 * d.+1 + m).
  elim: m {-2}m 0 (leqnn m) => [|n IHn] [|m] q //=; rewrite ltnS => le_mn.
  rewrite subn_if_gt; case: ltnP => [// | le_dm].
  rewrite -{1}(subnK le_dm) -addnS addnA.
  rewrite addnAC -mulSnr.                   (* addnAC を追加した。  *)
  apply (IHn (m - d) q.+1).                 (* apply: IHn でもよい。 *)
  apply: leq_trans le_mn; exact: leq_subr.
Qed.

Lemma edivn_eq_right : forall d q r, r < d -> edivn (q * d + r) d = (q, r).
Proof.
  move=> d q r lt_rd; have d_pos: 0 < d by exact: leq_trans lt_rd.
  set m := q * d + r; have: m = q * d + r by [].
  set d' := d; have: d' = d by [].
  case: (edivnP_right m d') => {m d'} m d' q' r' -> lt_r'd' d'd q'd'r'.
  move: q'd'r' lt_r'd' lt_rd; rewrite d'd d_pos {d'd m} /=.
    wlog: q q' r r' / q <= q' by case (ltnP q q'); last symmetry; eauto.
  rewrite leq_eqVlt; case: eqP => [-> _|_] /=; first by move/addnI->.
    rewrite -(leq_pmul2r d_pos); move/leq_add=> Hqr Eqr _; move/Hqr {Hqr}.
  by rewrite addnS ltnNge mulSn -addnA -Eqr addnCA addnA leq_addr.
Qed.

Lemma edivn_eq_left : forall d q r, r < d -> edivn (q * d + r) d = (q, r).
Proof.
  move=> d q r lt_rd; have d_pos: 0 < d by exact: leq_trans lt_rd.
  case: (edivnP_left (q * d + r) d) lt_rd; rewrite d_pos /=.
    set q' := (edivn (q * d + r) d).1; set r' := (edivn (q * d + r) d).2.
  rewrite (surjective_pairing (edivn (q * d + r) d)) -/q' -/r'.
    wlog: q r q' r' / q <= q' by case (ltnP q q'); last symmetry; eauto.
  rewrite leq_eqVlt; case: eqP => [-> _|_] /=; first by move/addnI->.
    rewrite -(leq_pmul2r d_pos); move/leq_add=> Hqr Eqr _; move/Hqr {Hqr}.
  by rewrite addnS ltnNge mulSn -addnA Eqr addnCA addnA leq_addr.
Qed.
(* .1と.2は直積のfstとsndである。これを使うには、ssrfunが必要である。 *)

(* おまけ *)

Inductive list (A : Type) : Type :=
| nil
| cons of A & list A.

Inductive list' (A : Type) : Type :=
| nil' : list' A
| cons' of A & list' A : list' A.

Inductive list'' (A : Type) : Type :=
| nil'' : list'' A
| cons'' : A -> list'' A -> list'' A.

Inductive list''' (A : Type) : Type :=
| nil''' : list''' A
| cons''' (x : A) (l : list''' A) : list''' A.

(* END *)
