(* プログラムの証明2 *)
(* http://www.math.nagoya-u.ac.jp/~garrigue/lecture/2011_AW/coq6.pdf *)
(*
独自の事柄として、proj1_sig と proj2_sig を使って、
プログラムと証明を取り出してみる。 *)

Require Import Arith Euclid Ring Omega.

Definition safe_modulo :                      (* Lamma でもよい。 *)
  forall n : nat,
    n > 0 ->
    forall m : nat, {r : nat | exists q : nat, m = q * n + r /\ n > r}.
Proof.
  intros b H a.
  pattern a.                                (* aをラムダ抽象する。 *)
  apply gt_wf_rec.
  intros n H0.
  elim (le_gt_dec b n).
  (* b <= n -> ... *)
  intro lebn.
  elim (H0 (n - b)); auto with arith.
  intros r Hr.
  exists r. elim Hr.
  intros q Hq.
  elim Hq.
  intros H1 H2.
  exists (S q); simpl.
  elim plus_assoc.
  elim H1.
  auto with arith.
  (* b > n -> ... *)
  intros gtbn.
  exists n.
  exists 0.
  simpl.
  auto with arith.
Defined.                                    (* Qed ではだめ。 *)

Definition mod'      n m :=           (safe_modulo (S m) (lt_O_Sn m) n).
Definition mod_safe  n m := proj1_sig (safe_modulo (S m) (lt_O_Sn m) n).
Definition mod_proof n m := proj2_sig (safe_modulo (S m) (lt_O_Sn m) n).

Require Import Recdef.
Function gcd (m n : nat) {wf lt m} : nat :=
  match m with
    | 0 => n
    | S m' => gcd (mod_safe n m') m         (* ここ *)
  end.
Proof.
(* 減少の証明 *)
  intros.
  destruct (mod_proof n m') as [x H].       (* ここ *)
  simpl.
  destruct H as [Hn Hm].
  apply Hm.
  (* 清楚性の証明 *)
  Search well_founded.
  exact lt_wf.
Defined.
Print gcd_ind.
(* 
gcd_ind = 
fun P : nat -> nat -> nat -> Prop => gcd_rect P
     : forall P : nat -> nat -> nat -> Prop,
       (forall m n : nat, m = 0 -> P 0 n n) ->
       (forall m n m' : nat,
        m = S m' ->
        P (mod_safe n m') m (gcd (mod_safe n m') m) ->
        P (S m') n (gcd (mod_safe n m') m)) -> forall m n : nat, P m n (gcd m n)
 *)

(* divides m n は、 m が n を割り切る。 *)
Inductive divides (m : nat) : nat -> Prop :=
  divi : forall a, divides m (a * m).

(* 上の定義を使いやすくするための補題 *)
Lemma divide : forall a m n, n = a * m -> divides m n.
Proof.
  intros. rewrite H. constructor.
Qed.

Lemma divides_mult : forall m q n, divides m n -> divides m (q * n).
Proof.
  intros m q n H; induction H.              (* induction 1. *)
  apply (divide (q * a)). ring.
Qed.

Lemma divides_plus :
  forall m n p, divides m n -> divides m p -> divides m (n + p).
Proof.
  intros m n p Hmn Hmp.
  induction Hmn as [a1].
  induction Hmp as [a2].
  apply (divide (a1 + a2)).
  rewrite (mult_plus_distr_r a1 a2 m).
  reflexivity.
Qed.
  
Lemma divides_1 : forall n, divides 1 n.
Proof.
  intros n.
  Check (divi 1 n).
  assert (n = n * 1) as H.
    induction n.
    simpl. reflexivity.
    simpl. rewrite <- IHn. reflexivity.
    (* done *)
  rewrite H.
  apply (divi 1 n).
Qed.

Lemma divides_0 : forall n, divides n 0.
Proof.
  intros n.
  apply (divi n 0).
Qed.

Lemma divides_n : forall n, divides n n.
Proof.
  intros n.
  Check (divi n 1).
  assert (n = 1 * n) as H.
    induction n.
    simpl. reflexivity.
    rewrite IHn at 1.
    simpl. reflexivity.
    (* done *)
  rewrite H at 2.
  apply (divi n 1).
Qed.

Hint Resolve divides_plus divides_mult divides_1 divides_0 divides_n.

Theorem gcd_divides : forall m n,
                        divides (gcd m n) m /\ divides (gcd m n) n.
Proof.
  intros m n.
  functional induction (gcd m n).
  auto.
  destruct (mod_proof n m') as [x H].       (* ここ *)
  destruct H as [Hn Hm].
  destruct IHn0 as [H1 H2].
  split.
  assumption.
  rewrite Hn.
    apply divides_plus; rewrite <- Hn.
      apply divides_mult. apply H2.
      apply H1.
Qed.

Lemma plus_inj : forall m n p, m + n = m + p -> n = p.
Proof.
  intros m n p H.
  induction m as [|m']; simpl in H.
  (* m = 0 *)
  apply H.
  (* m = S m' *)
  apply IHm'.
  (* Sm = Sn -> m = n を適用してもよいが、ここは一気に*)
  inversion H.
  reflexivity.
Qed.

Lemma divides_plus' : forall m n p,
                        divides m n -> divides m (n + p) -> divides m p.
Proof.
  induction 1.
  intro.
  induction a. assumption.
  inversion H.
  destruct a0.
  destruct p. auto.
  elimtype False.
  destruct m; destruct a; try discriminate; omega.
  simpl in H1.
  apply IHa.
  rewrite <- plus_assoc in H1.
  rewrite <- (plus_inj _ _ _ H1).
  constructor.
Qed.

(* http://www.math.nagoya-u.ac.jp/~garrigue/lecture/2013_SS/coq8.pdf *)
Theorem gcd_max : forall g m n,
                    divides g m -> divides g n -> divides g (gcd m n).
Proof.
  intros g m n Hgm Hgn.
  functional induction (gcd m n).
  apply Hgn.
  destruct (mod_proof n m') as [q Hnm].     (* ここ *)
  destruct Hnm as [Hn Hm'].
  apply IHn0.
  apply (divides_plus' g (q * S m')).

  (* divides g (q * S m') *)
  apply divides_mult.
  apply Hgm.
  
  (* divides g (q * S m' + mod_safe n m') *)
  Check (divide (q * m')).
  apply (divide (q * m')).
  unfold mod_safe. rewrite <- Hn.
  admit.                                    (* XXXX *)

  (* divides g (S m') *)
  apply Hgm.
Admitted.

(* END *)
