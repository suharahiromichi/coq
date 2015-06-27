Require Import ssreflect ssrfun ssrbool eqtype ssrnat.

(* motivating example *)

Goal forall n, n + n = 2 * n.
elim.
  by rewrite addn0 muln0.
move=> n IH.
rewrite addSn.
rewrite addnS.
rewrite IH.
rewrite mulnS.
rewrite -addn2.
rewrite addnC.
done.
Qed.

(* a note an unification *)

Goal forall a b c d,
  a < b ->
  a < b + c + d.
move=> a b c d.
(* 
ltn_addr : forall m n p : nat, m < n -> m < n + p 
*)
Fail apply ltn_addr.
(* Error: Impossible to unify "b + c" with "b". *)
(* match m<->a, n<->b, p<->d and thus b + c<->n !!! *)
rewrite -addnA.
apply ltn_addr.
Qed.

Goal False.
Proof.
  evar (x : nat).
  have : 2 + x = 4 + 5.
  - rewrite /x.
    by apply refl_equal.
  - rewrite /= in x *.
    compute.                                (* XXX *)
Abort.                                      (* OK *)

Print nat.

Print nat_rect.
Print nat_ind.
Print nat_rec.

Definition mynat_ind_proof := fun (P : nat -> Prop) (f : P 0) (f0 : forall n : nat, P n -> P n.+1) =>
fix F (n : nat) : P n :=
  match n as n0 return (P n0) with
  | 0 => f
  | n0.+1 => f0 n0 (F n0)
  end.

Lemma mynat_ind : forall (P : nat -> Prop), P 0 ->
  (forall n : nat, P n -> P n.+1) ->
  forall n, P n.
exact mynat_ind_proof.
Qed.

(* le vs. leq *)

Print le.
Print leq.

Goal forall n, 0 <= n.
done.
Show Proof.
Qed.

(* compare with: *)
Print Le.le_0_n.

Goal forall n m, n.+1 <= m.+1 -> n <= m.
done.
Show Proof.
Qed.

(* compare with: *)
Print le_S_n.
Print le_pred.

Goal forall n, n <= n.
done.
Qed.

Goal forall n, n <= n.+1.
done.
Qed.

Goal forall n, n < n = false.
by elim.
Qed.

(* 加算の可換性: prove in one line (without using addnC of course) *)

Lemma exo16 n m : m + n = n + m.
Proof.
  by rewrite addnC.
Qed.

(* about leqP *)

Goal forall n : nat, (n <= 5 \/ 5 < n)%coq_nat.
move=> n.
destruct (Compare_dec.le_gt_dec n 5).
(* NB: does not replace n <= 5 with True *)
auto.
auto.
Show Proof.
Qed.

Goal forall n : nat, (n <= 5) || (5 < n).
move=> n.
case H : (n <= 5).
done.
move/negbT : H.
rewrite -ltnNge.
move=> ->.
done.
(* pros: replace (n <= 5) by true, etc.
   cons: rewrite in the 2nd branch because of mismatch with standard library, 
     does not scale to three way case analysis *)
Qed.

Goal forall n : nat, (n <= 5) || (5 < n).
move=> n.
case: (leqP n 5).
done.
done.
Qed.

 (* sum は (_ + _)%type *)
Definition rgb := sum unit bool.            (* (unit + bool)%type *)
Definition red : rgb := inl tt.
Definition green : rgb := inr false.
Definition blue : rgb := inr true.

Print rgb.                                  (* (unit + bool)%type *)
Definition nop (c : rgb) : rgb := 
  match c with
  | inl _ => red
  | inr false => green
  | inr true => blue
  end.
Compute nop red = red.
Compute nop green = green.
Compute nop blue = blue.

Definition shift (c : rgb) : rgb := 
  match c with
  | inl _ => green
  | inr false => blue
  | inr true => red
  end.

(* Prove the following: *)
Lemma exo17 c : shift (shift (shift c)) = c.
Proof.
  by case: c; case.
Qed.

CoInductive rgb_spec : rgb -> bool -> bool -> bool -> Prop := 
| red_spec : rgb_spec red true false false
| green_spec : rgb_spec green false true false
| blue_spec : rgb_spec blue false false true.

(* Prove the following: *)
Lemma rgbP c : rgb_spec c (c == red) (c == green) (c == blue).
Proof.
  case: c.
  - case; apply red_spec.                   (* red *)
  - case; [apply blue_spec | apply green_spec].
Qed.

(* same as exo17 but this time using rgbP: *)
Lemma exo18 c : shift (shift (shift c)) = c.
Proof.
  by case: c; case.
Qed.

(* END *)
