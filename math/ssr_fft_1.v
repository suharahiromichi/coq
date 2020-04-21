(**
FFT
========================

@suharahiromichi

2020/04/21
 *)

From mathcomp Require Import all_ssreflect.
(* From mathcomp Require Import all_algebra. *)
Require Import Recdef.
Require Import Wf_nat.                      (* well_founded lt *)
Require Import Program.Wf.                  (* Program Fixpoint *)
Require Import ssr_omega.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
(* Set Print All. *)

Section ZetaFactor.
  
(**
ζ因子 : W^m_N = e^(2πi * m / N) = zeta (m, N) _
 *)
  
  Record zeta : Set :=
    Zeta {
        valz : (nat * nat);
        axiom : (0 < valz.2) && (valz.1 < valz.2) && (coprime valz.1 valz.2)
      }.

  Canonical zeta_subType := Eval hnf in [subType for valz].
  Definition zeta_eqMixin := [eqMixin of zeta by <:].
  Canonical zeta_eqType := EqType zeta zeta_eqMixin.
  Definition zeta_choiceMixin := [choiceMixin of zeta by <:].
  Canonical zeta_choiceType := ChoiceType zeta zeta_choiceMixin.
  Definition zeta_countMixin := [countMixin of zeta by <:].
  Canonical zeta_countType := CountType zeta zeta_countMixin.
  Canonical zeta_subCountType := [subCountType of zeta].
  
  Lemma gcdnlel m n : 0 < m -> gcdn m n <= m.
  Proof.
    move=> H.
    Check dvdn_leq : forall d m : nat, 0 < m -> d %| m -> d <= m.
    Check dvdn_gcdl : forall m n : nat, gcdn m n %| m.
    apply: dvdn_leq => //.
      by apply: dvdn_gcdl.
  Qed.
  
  Lemma gcdnler m n : 0 < n -> gcdn m n <= n.
  Proof.
    move=> H.
    Check dvdn_gcdr : forall m n : nat, gcdn m n %| n.
    apply: dvdn_leq => //.
      by apply: dvdn_gcdr.
  Qed.
  
(* これは、zf_func を修正することで、不要にできる。 *)
(*Lemma divn_modnl m n d : (m %% n) %/ d = (m %/ d) %% (n %/ d). *)
  Lemma divn_modnl : left_distributive divn modn.
  Proof.
    rewrite /left_distributive.
  Admitted.
  Compute (6 %% 4) %/ 2.
  Compute (6 %/ 2) %% (4 %/ 2).
  
  Lemma ltn_gcdn x y : y != 0 -> 0 < y %/ (gcdn x y).
  Proof.
    move=> H.
    rewrite divn_gt0.
    - apply: gcdnler.
        by rewrite lt0n.
    - rewrite gcdn_gt0.
      apply/orP/or_intror.
        by rewrite lt0n.
  Qed.
  
  Lemma coprime_gcdn m d : coprime (m %/ gcdn m d) (d %/ gcdn m d).
  Proof.
    rewrite /coprime.
    apply/eqP.
    Search _ (gcdn _ (gcdn _ _)).
  Admitted.
  
  Definition zf_fact (m d : nat) :=
    if (d == 0) then (0, 1) else ((m %% d) %/ (gcdn m d), d %/ (gcdn m d)).

  Compute zf_fact 0 0.                      (* (0, 1) *)
  Compute zf_fact 1 1.                      (* (0, 1) *)
  Compute zf_fact 0 4.                      (* (0, 1) *)
  Compute zf_fact 1 4.                      (* (1, 4) *)
  Compute zf_fact 2 4.                      (* (1, 2) *)
  Compute zf_fact 3 4.                      (* (3, 4) *)
  Compute zf_fact 4 4.                      (* (0, 1) *)
  Compute zf_fact 5 4.                      (* (1, 4) *)
  Compute zf_fact 6 4.                      (* (1, 2) *)
  Compute zf_fact 7 4.                      (* (3, 4) *)
  Compute zf_fact 8 4.                      (* (0, 1) *)

  Lemma zf_subproof (x : (nat * nat)) :
    let: z := zf_fact x.1 x.2 in
    (0 < z.2) && (z.1 < z.2) && (coprime z.1 z.2).
(*  let (m', d') := zf_fact x.1 x.2 in
    (0 < d') && (m' < d') && (coprime m' d'). *) (* うまくいかない例 *)
  Proof.
    case: x => [m d].
    rewrite /zf_fact.
    case: eqP => /eqP //= H.                (* H : d != 0 *)
    apply/andP; split; [apply/andP; split |]; rewrite /=.
    - by rewrite ltn_gcdn.
    - by rewrite divn_modnl ltn_mod ltn_gcdn.
    - by rewrite divn_modnl coprime_modl coprime_gcdn.
  Qed.
  
  Definition zf (x : (nat * nat)) := @Zeta(_, _) (zf_subproof x).
  (* (x.1, x.2) とするとエラーになる。 *)

  Section Test.
    Definition z1_2 := zf (1, 2).
    Definition z2_4 := zf (2, 4).
    Definition z5_4 := zf (5, 4).    
    Definition z6_4 := zf (6, 4).
    Compute z1_2 == z2_4.                     (* true *)
    Compute z5_4 == z2_4.                     (* false *)
    Compute z6_4 == z2_4.                     (* true *)
    
    Variables i : nat.
    
    Definition zi_4 := zf (i, 4).
    Definition z2i_8 := zf (2 * i, 8).
    Check zi_4 == z2i_8.
  End Test.

End ZetaFactor.


(* ******************************* *)
(* ******************************* *)
(* ******************************* *)
(* ******************************* *)
(* ******************************* *)
(* ******************************* *)
(* ******************************* *)


Section Term.

(** a_0 * W~i_N の項を 示す。 *)

  Record term : Set :=
    Term {
        val : (nat * (nat * nat)) ;
        axiom : (0 < val.2.2) && (coprime val.2.1 val.2.2)
      }.
  

(*
  axiom の2項めがないとき：
  
  Lemma term_subproof (x : (nat * (nat * nat))) :
    let d := if 0 < x.2.2 then x.2.2 else 1 in
    (0 < d).
  Proof.
      by case: ifP => H.                   (* case H : (0 < x.2.2). *)
  Qed.

  Lemma Test0_3 : 0 < 3. Proof. done. Qed.
  Check @Term (1,(2,3)) Test0_3.
  Check term_subproof (1,(2,3)).

  Check Term (term_subproof (1,(2,3))).
  Check @Term (_, (_, _)) (term_subproof (1,(2,3))).
  Definition et (x : (nat * (nat * nat))) :=
    @Term (x.1, (x.2.1, _)) (term_subproof' x). (* x.2.2 とするとエラーになる。 *)
*)  

  Lemma term_subproof (x : nat * (nat * nat)) :
  let n := if x.2.2 == 0 then 0 else (x.2.1 %/ gcdn x.2.1 x.2.2) in
  let d := if x.2.2 == 0 then 1 else (x.2.2 %/ gcdn x.2.1 x.2.2) in
  (0 < d) && (coprime n d).
  Proof.
    case: eqP => H //=.                     (* x.2.2 <> 0 *)
    apply/andP; split=> //.
    - admit.
    - rewrite /coprime.
  Admitted.
  
  Compute term_subproof (1,(2,3)).
  Check @Term (_, (_, _)) (term_subproof (1,(2,3))).
  Fail Check Term (term_subproof (1,(2,3))).
  Definition et (x : (nat * (nat * nat))) :=
    @Term (x.1, (_, _)) (term_subproof x). (* x.2.2 とするとエラーになる。 *)

  Definition e1 := et (1,(2,3)).
  Definition e2 := et (1,(3,6)).
  Compute e1 == e2.                         (* false *)

  Variable i : nat.
  Definition ei := et (1,(2,i)).
  Compute ei == ei.


Section BitRev.
  
  Variable T : Type.
  
  Lemma take_size (n : nat) (s : seq T) : n < size s -> size (take n s) < size s.
  Proof.
    move=> H.
    rewrite size_takel //.
      by ssromega.
  Qed.
  
  Lemma drop_size (n : nat) (s : seq T) :
    0 < size s -> 0 < n -> size (drop n s) < size s.
  Proof.
    move=> Hs Hn.
    rewrite size_drop.
      by ssromega.
  Qed.
  
(**
### リストを反転する。

length は Coq、size は mathcomp である。
*)
  Program Fixpoint binrev (s : seq T) {measure (size s)} : seq T :=
    match (size s <= 1) with
    | true => s
    | _ => let s0 := take (size s %/ 2) s in
           let s1 := drop (size s %/ 2) s in
           binrev s1 ++ binrev s0
    end.
  Obligation 1.
  Proof.
    move/eqP in H.
    apply/ltP/drop_size.
    - by ssromega.
    - rewrite divn_gt0 //.
        by ssromega.
  Qed.
  Obligation 2.
  Proof.
    move/eqP in H.
    apply/ltP/take_size.
    rewrite ltn_Pdiv //.
      by ssromega.
  Qed.
  

(**
### リストをビット逆順にする
*)
  Fixpoint zip2 (s1 s2 : seq T) : seq T :=
    match s1, s2 with
    | [::], _ => [::]
    | _, [::] => [::]
    | c1 :: s1, c2 :: s2 => c1 :: c2 :: zip2 s1 s2
    end.
  Notation "s1 +++ s2" := (zip2 s1 s2) (right associativity, at level 60).

  Program Fixpoint bitrev (s : seq T) {measure (size s)} : seq T :=
    match (size s <= 1) with
    | true => s
    | _ => let s0 := take (size s %/ 2) s in
           let s1 := drop (size s %/ 2) s in
           bitrev s0 +++ bitrev s1
    end.
  Obligation 1.
  Proof.
    move/eqP in H.
    apply/ltP/take_size.
    rewrite ltn_Pdiv //.
      by ssromega.
  Qed.
  Obligation 2.
  Proof.
    move/eqP in H.
    apply/ltP/drop_size.
    - by ssromega.
    - rewrite divn_gt0 //.
        by ssromega.
  Qed.

End BitRev.

Definition data := [:: 0; 1; 2; 3; 4; 5; 6; 7].
Compute binrev data.               (* = [:: 7; 6; 5; 4; 3; 2; 1; 0] *)
Compute bitrev data.               (* = [:: 0; 4; 2; 6; 1; 5; 3; 7] *)

Definition data16 := [:: 0; 1; 2; 3; 4; 5; 6; 7; 8; 9; 10; 11; 12; 13; 14; 15].
Compute binrev data16.
Compute bitrev data16.

Goal bitrev (bitrev data16) == data16.
Proof.
  done.
Qed.

Section Test.

  Variable T : Type.

  Notation "s1 +++ s2" := (zip2 s1 s2) (right associativity, at level 60).
  
  Lemma binrev_cat (s0 s1 : seq T) : binrev s1 ++ binrev s0 = binrev (s0 ++ s1).
  Proof.
  Admitted.


  Lemma cat_ind P :
    P [::] -> (forall (s0 s1 : seq T), P s0 -> P s1 -> P (s0 ++ s1)) -> forall s, P s.
  Proof.
    move=> HP IHs s.
    rewrite -[s]cats0.
    elim: s.

    Check (@cat_take_drop ((size s) %/ 2) T s).
    apply: IHs.
    - elim: s => // a s IHs.
      Search _ take.

  Admitted.
  
  Lemma binrev_binrev (s : seq T) : binrev (binrev s) = s.
  Proof.
    elim/cat_ind : s => // [s0 s1 IHs0 IHs1].
    rewrite -!binrev_cat.
      by rewrite IHs0 IHs1.
  Qed.
  
  
  (* ************* *)
  

  Lemma zip2_ind P :
    P [::] -> (forall (s0 s1 : seq T), P s0 -> P s1 -> P (s0 +++ s1)) -> forall s, P s.
  Proof.
  Admitted.
  
  Lemma bitrev_cat (s0 s1 : seq T) : bitrev s0 +++ bitrev s1 = bitrev (s0 +++ s1).
  Proof.
  Admitted.
  
  Lemma bitrev_bitrev (s : seq T) : bitrev (bitrev s) = s.
  Proof.
    elim/zip2_ind : s => // [s0 s1 IHs0 IHs1].
    rewrite -!bitrev_cat.
      by rewrite IHs0 IHs1.
  Qed.

End Test.

(* END *)
From mathcomp Require Import all_ssreflect.
From mathcomp Require Import all_algebra.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
(* Set Print All. *)

(* 以下全部要る *)
Import intZmod.
Import intOrdered.
Import GRing.Theory.
Open Scope ring_scope.

Check ratz 0 : rat.
Check ratz 1 : rat.

Check fracq (1%:Z, 2%:Z).

Definition ratn (m : int) (n : int) := fracq (m, n).
Check ratn 1 2 : rat.                       (* 1/2 *)

Compute ratn 2 4 == ratn 1 2.               (* true *)
Compute ratn 3 4 == ratn 1 2.               (* false *)

Compute addq (ratn 1 2) (ratn 1 2) == ratz 1.   (* true *)
Compute subq (ratn 1 2) (ratn 1 2) == ratz 0.   (* true *)
Compute mulq (ratn 1 2) (ratn 1 2) == ratn 1 4. (* true *)


Definition norm (z : rat) :=
  let d := denq z in
  let n := numq z in
  let n' := n - d in                        (* 整数引算 *)
  if d <= n then fracq (n', d) else z.      (* 整数比較 *)


Definition sign (z : rat) := norm (addq z (ratn 1 2)). (* 1/2 を足す。-1倍と同じ。 *)
Compute sign (ratn 1 4).                    (* 3/4 *)
Compute sign (ratn 1 8).                    (* 5/8 *)
Compute sign (ratn 3 4).                    (* 5/4 = 1/4 *)

Inductive Term : Type :=
| tcoe (n : nat)
| tmul (t : Term) (z : rat).

Definition sign2 (t : Term) :=
  match t with
  | tcoe n => tmul (tcoe n) (ratn 1 2)
  | tmul t z => tmul t (sign z)
  end.

Inductive Exp : Type :=
| term (t : Term)
| tadd (e : Exp) (t : Term)
| tsub (e : Exp) (t : Term).

Fixpoint tmult (t : Exp) (z : rat) : Exp :=
  match t with
  | term t => match t with
              | tcoe n => term (tmul (tcoe n) z)
              | tmul t z' => term (tmul t (norm (addq z' z)))
              end
  | tadd e t => match t with
                | tcoe n => tadd (tmult e z) (tmul (tcoe n) z)
                | tmul t z' => tadd (tmult e z) (tmul t (norm (addq z' z)))
                end
  | tsub e t => match t with
                | tcoe n => tadd (tmult e z) (tmul (tcoe n) (sign z))
                | tmul t z' => tadd (tmult e z) (tmul t (norm (sign (addq z' z))))
                end
  end.

Compute tmult (tsub (term (tcoe 0)) (tcoe 4)) (ratn 0 8).
Compute tmult (tsub (term (tcoe 2)) (tcoe 6)) (ratn 2 8).
Compute tmult (tsub (term (tcoe 1)) (tcoe 5)) (ratn 1 8).
Compute tmult (tsub (term (tcoe 3)) (tcoe 7)) (ratn 3 8).

Fixpoint taddt (e1 e2 : Exp) : Exp :=
  match e2 with
  | term t => tadd e1 t                       (* e1 + t *)
  | tadd e2 t => tadd (taddt e1 e2) t         (* e1 + (e2 + t) *)
  | tsub e2 t => tadd (taddt e1 e2) (sign2 t) (* e1 + (e2 - t) *)
  end
with tsubt (e1 e2 : Exp) : Exp :=
  match e2 with
  | term t => tadd e1 (sign2 t)               (* e1 - t *)
  | tadd e2 t => tadd (tsubt e1 e2) (sign2 t) (* e1 - (e2 + t) *)
  | tsub e2 t => tadd (tsubt e1 e2) t         (* e1 - (e2 - t) *)
  end.
  

Compute tmult (tsub (term (tcoe 0)) (tcoe 4)) (ratn 0 8).
Compute tmult (tsub (term (tcoe 2)) (tcoe 6)) (ratn 2 8).
Compute tsubt
        (tmult (tsub (term (tcoe 0)) (tcoe 4)) (ratn 0 8))
        (tmult (tsub (term (tcoe 2)) (tcoe 6)) (ratn 2 8)).

Compute tmult
        (tsubt
           (tmult (tsub (term (tcoe 0)) (tcoe 4)) (ratn 0 8))
           (tmult (tsub (term (tcoe 2)) (tcoe 6)) (ratn 2 8)))
        (ratn 0 4).

Compute tsubt
        (tmult (tsub (term (tcoe 1)) (tcoe 5)) (ratn 1 8))
        (tmult (tsub (term (tcoe 3)) (tcoe 7)) (ratn 3 8)).

Compute tmult
        (tsubt
           (tmult (tsub (term (tcoe 1)) (tcoe 5)) (ratn 1 8))
           (tmult (tsub (term (tcoe 3)) (tcoe 7)) (ratn 3 8)))
        (ratn 1 4).

Compute tsubt
        (tmult
           (tsubt
              (tmult (tsub (term (tcoe 0)) (tcoe 4)) (ratn 0 8))
              (tmult (tsub (term (tcoe 2)) (tcoe 6)) (ratn 2 8)))
           (ratn 0 4))
        (tmult
           (tsubt
              (tmult (tsub (term (tcoe 1)) (tcoe 5)) (ratn 1 8))
              (tmult (tsub (term (tcoe 3)) (tcoe 7)) (ratn 3 8)))
           (ratn 1 4)).

(* 
     = tadd
         (tadd
            (tadd
               (tadd
                  (tadd
                     (tadd
                        (tadd (term (tmul (tcoe 0) (Rat (fracq_subproof (0, 1)))))
                           (tmul (tcoe 4) (Rat (fracq_subproof (1, 2))))) (* 4/8 *)
                        (tmul (tcoe 2) (Rat (fracq_subproof (3, 4))))) (* 6/8 *)
                     (tmul (tcoe 6) (Rat (fracq_subproof (5, 4))))) (* 2/8 *)
                  (tmul (tcoe 1) (Rat (fracq_subproof (14, 16))))) (* 7/8 *)
               (tmul (tcoe 5) (Rat (fracq_subproof (22, 16))))) (* 3/8 *)
            (tmul (tcoe 3) (Rat (fracq_subproof (26, 16))))) (* 5/8 *)
         (tmul (tcoe 7) (Rat (fracq_subproof (34, 16)))) (* 1/8 *)
     : Exp
*)

(* 
ノーマライズあと
     = tadd
         (tadd
            (tadd
               (tadd
                  (tadd
                     (tadd
                        (tadd (term (tmul (tcoe 0) (Rat (fracq_subproof (0, 1)))))
                           (tmul (tcoe 4) (Rat (fracq_subproof (1, 2))))) (* 4/8 *)
                        (tmul (tcoe 2) (Rat (fracq_subproof (3, 4))))) (* 6/8 *)
                     (tmul (tcoe 6) (Rat (fracq_subproof (1, 4))))) (* 2/8 *)
                  (tmul (tcoe 1) (Rat (fracq_subproof (14, 16))))) (* 7/8 *)
               (tmul (tcoe 5) (Rat (fracq_subproof (3, 8))))) (* 3/8 *)
            (tmul (tcoe 3) (Rat (fracq_subproof (10, 16))))) (* 5/8 *)
         (tmul (tcoe 7) (Rat (fracq_subproof (1, 8)))) (* 1/8 *)
     : Exp
 *)


Definition CS :=
  [:: term (tcoe 0); term (tcoe 1); term (tcoe 2); term (tcoe 3);
     term (tcoe 4); term (tcoe 5); term (tcoe 6); term (tcoe 7)].

Compute take 4 CS.
Compute drop 4 CS.

Fixpoint map2 op (i : nat) (s1 s2 : seq Exp) : seq Exp :=
  match s1, s2 with
  | [::], _ => [::]
  | _, [::] => [::]
  | c1 :: s1, c2 :: s2 => (op i c1 c2) :: map2 op i.+1 s1 s2
  end.

Check (fun _ c1 c2 => taddt c1 c2).
Check (fun i c1 c2 => tmult (tsubt c1 c2) (ratn i 8)).

(* バタフライ演算 *)
Definition Be (n : nat) s1 s2 := map2 (fun _ c1 c2 => taddt c1 c2) 0 s1 s2.
Compute Be 8 (take 4 CS) (drop 4 CS).

Definition Bo n s1 s2 := map2 (fun i c1 c2 => tmult (tsubt c1 c2) (ratn i n)) 0 s1 s2.
Compute Bo 8 (take 4 CS) (drop 4 CS).

Fixpoint zip2 (s1 s2 : seq Exp) : seq Exp :=
  match s1, s2 with
  | [::], _ => [::]
  | _, [::] => [::]
  | c1 :: s1, c2 :: s2 => c1 :: c2 :: zip2 s1 s2
  end.

Notation "s1 +++ s2" := (zip2 s1 s2) (right associativity, at level 60).

Require Import Recdef.
Require Import Program.Wf.
Program Fixpoint FFT (n : nat) (c : seq Exp) {wf lt n} : seq Exp :=
  if (leq n 1) then c
  else
    let c0 := take (n %/2) c in                  (* 前半 *)
    let c1 := drop (n %/2) c in                  (* 後半 *)
    FFT (n %/2) (Be n c0 c1) +++ FFT (n %/2) (Bo n c0 c1).
Obligations.
Obligation 1.                               (* (n %/ 2 < n)%coq_nat *)
Proof.
  Admitted.
Obligation 2.                               (* (n %/ 2 < n)%coq_nat *)
Proof.
  Admitted.

Compute FFT 8 CS.

(* 結果は手動と一致するようだ。 *)

Coercion term : Term >-> Exp.
Notation "a + b" := (tadd a b).
Notation "a * b" := (tmul a b).

Compute FFT 8 CS.


(* END *)
