(**
b を2進表現の正整数としたとき、
左シフトが2倍に等しいこと

b << 1 = b * 2

であることをしめせ。
*)
From elpi Require Import elpi.
From HB Require Import structures.
From mathcomp Require Import all_ssreflect.
From mathcomp Require Import all_algebra.


Definition bin := seq bool.

Definition eval (b : bin) := \sum_(0 <= i < size b)((nth false b i) * 2 ^ i).

Definition b10 := [:: false; true; false; true].


Goal eval b10 = 10.
Proof.
  rewrite /eval unlock /bigop.
  rewrite /reducebig /applybig.
  rewrite /=.
  cbv.
  done.
Qed.
  
Lemma eq_sum m n a b : a =1 b ->
                         \sum_(m <= i < n)(a i) = \sum_(m <= j < n)(b j).
Proof.
  move=> Hab.                             (* =1 は第1階の=です。 *)
  apply: eq_big_nat => i Hmn.
  by rewrite Hab.
Qed.

Goal forall b : bin, eval (false :: b) = (eval b).*2.
Proof.
  rewrite /eval.
  elim=> //= [| a l IHl].
  - rewrite [in LHS]big_nat1.
    rewrite [in RHS]big_nil.
    done.
  (* 左辺の最下位のfalseを消し去る。 *)
  - rewrite [in LHS]big_nat_recl //=.
    rewrite mul0n add0n.
    rewrite -muln2.
    rewrite [in RHS]big_distrl //=.
    rewrite (@eq_sum 0 (size l).+1
               (fun i => nth false (a :: l) i * 2 ^ i.+1)
               (fun i => nth false (a :: l) i * 2 ^ i * 2)) //.
    move=> i.
    rewrite -mulnA.
    f_equal.
    by rewrite expnSr.
Qed.

(**
バニラCoqでは、NArithで補題が証明されている。
*)
Module rocq.
  Require Import NArith.
  
  (* NArith/BinNat.v *)
  About N.shiftl_succ_r.
  Check N.shiftl_succ_r
    : forall a n : N, N.shiftl a (N.succ n) = N.double (N.shiftl a n).
  
  Goal forall x : N, N.shiftl x 1 = N.double x.
  Proof.
    move=> x.
    have -> : (1 : N) = N.succ (0 : N) by done.
    by rewrite N.shiftl_succ_r N.shiftl_0_r.
  Qed.

End rocq.

(* END *)
