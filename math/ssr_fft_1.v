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
  
  Lemma muln_c x c : 0 < c -> x * c = c -> x = 1.
  Proof.
    move=> H0c /eqP H.
    apply/eqP.
      by rewrite -(eqn_pmul2r H0c) mul1n.
  Qed.
  
  Lemma coprime_gcdn m n : 0 < n -> forall d,
      d = gcdn m n -> coprime (m %/ d) (n %/ d).
  Proof.
    move=> H0n d H.
    rewrite /coprime.
    apply/eqP.
    have Hd : 0 < d by rewrite H gcdn_gt0; apply/orP/or_intror/H0n.
    apply: (muln_c Hd).
    rewrite (@muln_gcdl (m %/ d) (n %/d) d).
    have Hm : gcdn m n %| m by rewrite dvdn_gcdl.
    have Hn : gcdn m n %| n by rewrite dvdn_gcdr.
    rewrite H (divnK Hm) (divnK Hn).
    done.
  Qed.
  
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
  Compute (zf_fact 8 4).1.                  (* 0 *)
  Compute (zf_fact 8 4).2.                  (* 1 *)
  
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
    - by rewrite divn_modnl coprime_modl coprime_gcdn //= lt0n.
  Qed.
  
  Definition zf (x : (nat * nat)) := @Zeta(_, _) (zf_subproof x).
  (* (x.1, x.2) とするとエラーになる。 *)

  Section Test1.
    Definition z0_2 := zf (0, 2).
    Definition z1_2 := zf (1, 2).
    
    Definition z0_4 := zf (0, 4).
    Definition z1_4 := zf (1, 4).
    Definition z2_4 := zf (2, 4).
    Definition z3_4 := zf (3, 4).
    Definition z4_4 := zf (2, 4).
    Definition z5_4 := zf (5, 4).    
    Definition z6_4 := zf (6, 4).
    Definition z7_4 := zf (7, 4).
    Definition z8_4 := zf (8, 4).
    
    Goal z1_2 == z2_4. Proof. compute. done. Qed.
    Goal z5_4 != z2_4. Proof. compute. done. Qed.
    Goal z6_4 == z2_4. Proof. compute. done. Qed.
    Goal z0_4 == z8_4. Proof. compute. done. Qed.
    
    Variables j : nat.
    
    Definition zj_4 := zf (j, 4).
    Definition z2j_8 := zf (2 * j, 8).

    Check zj_4 == z2j_8.
  End Test1.
  
  
(* zeta因子の掛け算 *)

  Definition nzf (z : zeta) := (valz z).1.  (* 分子 ζ^n_N の n *)
  Definition dzf (z : zeta) := (valz z).2.  (* 分母 ζ^n_N の N *)
  Definition mulzf (z1 z2 : zeta) :=
    zf (nzf z1 * dzf z2 + dzf z1 * nzf z2, dzf z1 * dzf z2).
  Definition negzf (z : zeta) := mulzf z (zf (1, 2)).

  Section Test2.

    Goal mulzf z1_2 z1_2 == z0_2. Proof. compute. done. Qed.
    Goal mulzf z1_4 z1_4 == z1_2. Proof. compute. done. Qed.
    
    Goal negzf z1_2 == z0_2. Proof. compute. done. Qed.
    Goal negzf z1_4 == z3_4. Proof. compute. done. Qed.
  End Test2.
  
End ZetaFactor.

Section Term.

  Definition term : Set := (nat * zeta)%type.
  
  Definition zt (n : nat) (z : zeta) := (n, z).

  Definition czt (t : term) : nat := t.1.
  Definition fzt (t : term) : zeta := t.2.
  Definition nzt (t : term) : nat := nzf t.2.
  Definition dzt (t : term) : nat := dzf t.2.
  Definition mulzt (t : term) (z : zeta) : term := zt (czt t) (mulzf (fzt t) z).
  Definition negzt (t : term) : term := zt (czt t) (negzf (fzt t)).
  
  Section Test3.

 
    Definition t1_1_4 := zt 1 (zf (1, 4)).
    Definition t1_3_4 := mulzt t1_1_4 (zf (1, 2)).
    Definition t1_3_4' := zt 1 (zf (3, 4)).
    
    Goal t1_3_4 == t1_3_4'. Proof. compute. done. Qed.
    
    Compute czt t1_3_4.                      (* 1 *)
    Compute nzt t1_3_4.                      (* 3 *)
    Compute dzt t1_3_4.                      (* 4 *)

  End Test3.
End Term.

Section Expression.

  Inductive exp : Type :=
  | tt (t : term)
  | tadd (e : exp) (t : term).
         
  Coercion tt : term >-> exp.
  Notation "a + b" := (tadd a b).
  
  Fixpoint mulze (e : exp) (z : zeta) : exp :=
    match e with
    | tt t => mulzt t z
    | tadd e t => tadd (mulze e z) (mulzt t z)
    end.
  
  Fixpoint addze (e1 e2 : exp) : exp :=
    match e2 with
    | tt t => tadd e1 t                         (* e1 + t *)
    | tadd e2 t => tadd (addze e1 e2) t         (* e1 + (e2 + t) *)
    end
  with subze (e1 e2 : exp) : exp :=
         match e2 with
         | tt t => tadd e1 (negzt t)                 (* e1 - t *)
         | tadd e2 t => tadd (subze e1 e2) (negzt t) (* e1 - (e2 + t) *)
         end.

  Section Test4.

    Definition z1 : zeta := zf (1, 4).
    Definition e1 : exp :=
      tt (zt 0 (zf (0, 4))) + zt 1 (zf (1, 4)) + zt 2 (zf (2, 4)) + zt 3 (zf (3, 4)).
    Definition e2 : exp := mulze e1 z1.
    (* 先頭のttのコアーションが効いていない。 *)
    
    Definition e2' : exp :=
      tt (zt 0 (zf (1, 4))) + zt 1 (zf (2, 4)) + zt 2 (zf (3, 4)) + zt 3 (zf (0, 4)).
  End Test4.

End Expression.

Notation "a + b" := (tadd a b).

Section MapZip.

  Variable T : Type.
  
  Fixpoint map2 op (j : nat) (s1 s2 : seq T) : seq T :=
    match s1, s2 with
    | [::], _ => [::]
    | _, [::] => [::]
    | c1 :: s1, c2 :: s2 => (op j c1 c2) :: map2 op j.+1 s1 s2
    end.
  
  Lemma size_map2 (s t : seq T) :
    forall op j, size (map2 op j s t) = minn (size s) (size t).
  Proof.
    elim: s t => [| x s IHs] [| t2 t] //= op j.
      by rewrite IHs -add1n addn_minr.
  Qed.

  Lemma size1_map2 (s t : seq T) :
    forall op j, size (map2 op j s t) <= size s.
  Proof.
    move=> op j.
    rewrite size_map2.
    apply: geq_minl.
  Qed.
  
  Lemma size2_map2 (s t : seq T) :
    forall op j, size (map2 op j s t) <= size t.
  Proof.
    move=> op j.
    rewrite size_map2.
    apply: geq_minr.
  Qed.
  
  Fixpoint zip2 (s1 s2 : seq T) : seq T :=
    match s1, s2 with
    | [::], _ => [::]
    | _, [::] => [::]
    | c1 :: s1, c2 :: s2 => c1 :: c2 :: zip2 s1 s2
    end.
  
  Lemma take_size (n : nat) (s : seq T) :
    n < size s -> size (take n s) < size s.
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

End MapZip.

Notation "s1 +++ s2" := (zip2 s1 s2) (right associativity, at level 60).

Definition CS : seq exp := [:: tt (zt 0 (zf (0, 1)));
                              tt (zt 1 (zf (0, 1)));
                              tt (zt 2 (zf (0, 1)));
                              tt (zt 3 (zf (0, 1)));
                              tt (zt 4 (zf (0, 1)));
                              tt (zt 5 (zf (0, 1)));
                              tt (zt 6 (zf (0, 1)));
                              tt (zt 7 (zf (0, 1)))
                           ].
      
(* リストのサイズを渡す。それにより再帰の停止性を決める。 *)
Section FFT'.

  (* バタフライ演算 *)
  Definition be' (n : nat) s1 s2 := map2 (fun _ c1 c2 => addze c1 c2)
                                         0 s1 s2.
  Definition bo' n s1 s2 := map2 (fun j c1 c2 => mulze (subze c1 c2) (zf (j, n)))
                                 0 s1 s2.

  Section Test5.
    Compute be' 8 (take 4 CS) (drop 4 CS).
    Compute bo' 8 (take 4 CS) (drop 4 CS).
  End Test5.
  
  Program Fixpoint fft' (n : nat) (c : seq exp) {wf lt n} : seq exp :=
    match n with
    | 0 | 1 => c
    | _ => let c0 := take (n %/2) c in      (* 前半 *)
           let c1 := drop (n %/2) c in      (* 後半 *)
           fft' (n %/2) (be' n c0 c1) +++ fft' (n %/2) (bo' n c0 c1)
           (* 偶数番 *)                   (* 奇数番 *)
    end.
  Obligations.
  Obligation 1.
  Proof.
  (* (n %/ 2 < n)%coq_nat *)
    apply/ltP/ltn_Pdiv => //.
      by ssromega.
  Qed.
  Obligation 2.
  Proof.
  (* (n %/ 2 < n)%coq_nat *)
    apply/ltP/ltn_Pdiv => //.
      by ssromega.
  Qed.

  Compute fft' 8 CS.
End FFT'.

(* リストのサイズを使って再帰の停止性を決める。 *)
Section FFT.
  
  (* バタフライ演算 *)
  Definition be s1 s2 := map2 (fun _ c1 c2 => addze c1 c2)
                              0 s1 s2.
  Definition bo s1 s2 := map2 (fun j c1 c2 => mulze (subze c1 c2) (zf (j, (size s1).*2)))
                              0 s1 s2.
  
  Section Test6.
    Compute be (take 4 CS) (drop 4 CS).
    Compute bo (take 4 CS) (drop 4 CS).
  End Test6.
  
  Program Fixpoint fft (c : seq exp) {measure (size c)} : seq exp :=
    match (size c) with
    | 0 | 1 => c
    | _ => let c0 := take (size c %/2) c in      (* 前半 *)
           let c1 := drop (size c %/2) c in      (* 後半 *)
           fft (be c0 c1) +++ fft (bo c0 c1)
           (* 偶数番 *)       (* 奇数番 *)
    end.
  Obligation 1.
  Proof.
    apply/ltP.
    (* size (be (take (size c %/ 2) c) (drop (size c %/ 2) c)) < size c *)
    apply: (@leq_ltn_trans (size (take (size c %/ 2) c))).
    - by apply: size1_map2.
    - apply: take_size.
      move/eqP in H0.
      rewrite eq_sym -lt0n in H0.           (* != のシンメトリにも使える *)
        by apply: ltn_Pdiv.
  Qed.
  Obligation 2.
  Proof.
    apply/ltP.
    (* size (bo (take (size c %/ 2) c) (drop (size c %/ 2) c)) < size c *)
    apply: (@leq_ltn_trans (size (take (size c %/ 2) c))).
    - by apply: size1_map2.
    - apply: take_size.
      move/eqP in H0.
      rewrite eq_sym -lt0n in H0.
        by apply: ltn_Pdiv.
  Qed.
  
  Compute fft CS.
(*
     = [:: (0, {| valz := (0, 1); axiom := zf_subproof (0, 1) |}) +
           (4, {| valz := (0, 1); axiom := zf_subproof (0, 1) |}) +
           (2, {| valz := (0, 1); axiom := zf_subproof (0, 1) |}) +
           (6, {| valz := (0, 1); axiom := zf_subproof (0, 1) |}) +
           (1, {| valz := (0, 1); axiom := zf_subproof (0, 1) |}) +
           (5, {| valz := (0, 1); axiom := zf_subproof (0, 1) |}) +
           (3, {| valz := (0, 1); axiom := zf_subproof (0, 1) |}) +
           (7, {| valz := (0, 1); axiom := zf_subproof (0, 1) |});
           (0, {| valz := (0, 1); axiom := zf_subproof (0, 1) |}) +
           (4, {| valz := (1, 2); axiom := zf_subproof (1, 2) |}) +
           (2, {| valz := (1, 4); axiom := zf_subproof (1, 4) |}) +
           (6, {| valz := (3, 4); axiom := zf_subproof (6, 8) |}) +
           (1, {| valz := (1, 8); axiom := zf_subproof (1, 8) |}) +
           (5, {| valz := (5, 8); axiom := zf_subproof (10, 16) |}) +
           (3, {| valz := (3, 8); axiom := zf_subproof (3, 8) |}) +
           (7, {| valz := (7, 8); axiom := zf_subproof (14, 16) |});
           (0, {| valz := (0, 1); axiom := zf_subproof (0, 1) |}) +
           (4, {| valz := (0, 1); axiom := zf_subproof (0, 1) |}) +
           (2, {| valz := (1, 2); axiom := zf_subproof (1, 2) |}) +
           (6, {| valz := (1, 2); axiom := zf_subproof (1, 2) |}) +
           (1, {| valz := (1, 4); axiom := zf_subproof (1, 4) |}) +
           (5, {| valz := (1, 4); axiom := zf_subproof (1, 4) |}) +
           (3, {| valz := (3, 4); axiom := zf_subproof (6, 8) |}) +
           (7, {| valz := (3, 4); axiom := zf_subproof (6, 8) |});
           (0, {| valz := (0, 1); axiom := zf_subproof (0, 1) |}) +
           (4, {| valz := (1, 2); axiom := zf_subproof (1, 2) |}) +
           (2, {| valz := (3, 4); axiom := zf_subproof (3, 4) |}) +
           (6, {| valz := (1, 4); axiom := zf_subproof (1, 4) |}) +
           (1, {| valz := (3, 8); axiom := zf_subproof (12, 32) |}) +
           (5, {| valz := (7, 8); axiom := zf_subproof (28, 32) |}) +
           (3, {| valz := (1, 8); axiom := zf_subproof (36, 32) |}) +
           (7, {| valz := (5, 8); axiom := zf_subproof (20, 32) |});
           (0, {| valz := (0, 1); axiom := zf_subproof (0, 1) |}) +
           (4, {| valz := (0, 1); axiom := zf_subproof (0, 1) |}) +
           (2, {| valz := (0, 1); axiom := zf_subproof (0, 1) |}) +
           (6, {| valz := (0, 1); axiom := zf_subproof (0, 1) |}) +
           (1, {| valz := (1, 2); axiom := zf_subproof (1, 2) |}) +
           (5, {| valz := (1, 2); axiom := zf_subproof (1, 2) |}) +
           (3, {| valz := (1, 2); axiom := zf_subproof (1, 2) |}) +
           (7, {| valz := (1, 2); axiom := zf_subproof (1, 2) |});
           (0, {| valz := (0, 1); axiom := zf_subproof (0, 1) |}) +
           (4, {| valz := (1, 2); axiom := zf_subproof (1, 2) |}) +
           (2, {| valz := (1, 4); axiom := zf_subproof (1, 4) |}) +
           (6, {| valz := (3, 4); axiom := zf_subproof (3, 4) |}) +
           (1, {| valz := (5, 8); axiom := zf_subproof (5, 8) |}) +
           (5, {| valz := (1, 8); axiom := zf_subproof (1, 8) |}) +
           (3, {| valz := (7, 8); axiom := zf_subproof (7, 8) |}) +
           (7, {| valz := (3, 8); axiom := zf_subproof (3, 8) |});
           (0, {| valz := (0, 1); axiom := zf_subproof (0, 1) |}) +
           (4, {| valz := (0, 1); axiom := zf_subproof (0, 1) |}) +
           (2, {| valz := (1, 2); axiom := zf_subproof (1, 2) |}) +
           (6, {| valz := (1, 2); axiom := zf_subproof (1, 2) |}) +
           (1, {| valz := (3, 4); axiom := zf_subproof (3, 4) |}) +
           (5, {| valz := (3, 4); axiom := zf_subproof (3, 4) |}) +
           (3, {| valz := (1, 4); axiom := zf_subproof (1, 4) |}) +
           (7, {| valz := (1, 4); axiom := zf_subproof (1, 4) |});
           (0, {| valz := (0, 1); axiom := zf_subproof (0, 1) |}) +
           (4, {| valz := (1, 2); axiom := zf_subproof (1, 2) |}) +
           (2, {| valz := (3, 4); axiom := zf_subproof (3, 4) |}) +
           (6, {| valz := (1, 4); axiom := zf_subproof (1, 4) |}) +
           (1, {| valz := (7, 8); axiom := zf_subproof (7, 8) |}) +
           (5, {| valz := (3, 8); axiom := zf_subproof (3, 8) |}) +
           (3, {| valz := (5, 8); axiom := zf_subproof (5, 8) |}) +
           (7, {| valz := (1, 8); axiom := zf_subproof (1, 8) |})]
     : seq exp
   *)

End FFT.

(* END *)

(*
exp をビット逆順でないように、一意に==できるようにする。

zip2をやめて、++してからビット逆順を戻す

DFTを作成する

DFTとFFTが一致することを証明する。
 *)
