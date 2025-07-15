(**
ビットとバイナリー
 *)
From mathcomp Require Import all_ssreflect.
(* From mathcomp Require Import all_algebra. *)

(**
b を2進表現の正整数としたとき、
左シフトが2倍に等しいこと

b << 1 = b * 2

であることをしめせ。
*)

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
  
  (* バニラCoqと mathcomp の相互運用性 *)
  Check nat_of_pos (1 : positive) : nat.
  Check nat_of_N (1 : N) : nat.
  Check N_of_nat 1 : N.
  
  Check 1 : nat.
  Check 1 : N.                              (* oercion は効く。 *)
  Check 1%N : N.                            (* 型の指定 *)
  
  (* NArith/BinNat.v *)
  About N.shiftl_succ_r.
  Check N.shiftl_succ_r
    : forall a n : N, N.shiftl a (N.succ n) = N.double (N.shiftl a n).
  
  Goal forall x : N, N.shiftl x 1 = N.double x.
  Proof.
    move=> x.
    have -> : 1%N = N.succ 0%N by done.
    by rewrite N.shiftl_succ_r N.shiftl_0_r.
  Qed.

End rocq.

(**
ルーラー関数
*)
Module rocq2.
  From Equations Require Import Equations.
  Require Import ZArith Lia.
  
  (* n = 0 then 0 *)
  Definition ruler (n : nat) :=
    let x := Z_of_nat n in Z.log2 (Z.land x (- x)%Z).
  
  Equations ruler_rec (n : nat) : Z by wf n :=
    ruler_rec 0 => 0 ;
    ruler_rec n.+1 with odd n.+1 => {
      | true  => 0
      | false => Z.add (ruler_rec n.+1./2) 1%Z
      }.
  Obligation 1.
  apply/ltP.
  rewrite ltn_uphalf_double -muln2.
  by apply: ltn_Pmulr.
  Qed.
  
  Example test (n : nat) := (ruler n = ruler_rec n).

  Goal test 0. Proof. done. Qed.
  Goal test 1. Proof. done. Qed.
  Goal test 2. Proof. done. Qed.
  Goal test 3. Proof. done. Qed.
  Goal test 4. Proof. done. Qed.
  Goal test 5. Proof. done. Qed.
  Goal test 6. Proof. done. Qed.
  Goal test 7. Proof. done. Qed.
  Goal test 8. Proof. done. Qed.

  Compute ruler_rec 0.  
  Compute ruler_rec 1.  
  Compute ruler_rec 2.  
  Compute ruler_rec 3.  
  Compute ruler_rec 4.
  Compute ruler_rec 5.  
  Compute ruler_rec 7.  
  Compute ruler_rec 8.  

  Goal forall (n : nat), ruler n = ruler_rec n.
  Proof.
    move=> n.
    funelim (ruler_rec n) => //=.
    
    (* nが奇数なら、ruler の値は0である。 *)
    Check odd n.+1 = true -> ruler n.+1 = 0%Z.
    - rewrite /ruler.
      rewrite -Z.succ_lnot.
      have <- : Z.log2 1%Z = 0%Z by done.
      f_equal.
      Check Z.land _ (Z.lnot _ + 1)%Z = 1%Z.
      (* 奇数だと、not の LBSが0なので、+ 1 でそこだけ変わる。 *)
      (* 奇数なら、+1 は、land 1 に等しい。 *)
      admit.
    
    - (* n が偶数なら *)
      Check uphalfE : forall n : nat, uphalf n = n.+1./2.
      (* uphalf n で成り立つ *)
      (* n.+1 で成り立つことを証明する。 *)
(*
  n : nat
  H : ruler (uphalf n) = ruler_rec (uphalf n)
  Heq : odd n.+1 = false
  Heqcall : Z.add (ruler_rec n.+1./2) 1%Z = ruler_rec n.+1
  ============================
  ruler n.+1 = Z.add (ruler_rec (uphalf n)) 1%Z
*)
      move: Heq.
      move: Heqcall.
      move: H.
      rewrite uphalfE.
      set m := n.+1.
      move=> H.
      move=> Heqcall.
      move=> Heq.
      (*
  n : nat
  m := n.+1 : nat
  H : ruler m./2 = ruler_rec m./2
  Heqcall : Z.add (ruler_rec m./2) 1%Z = ruler_rec m
  Heq : odd m = false
  ============================
  ruler m = Z.add (ruler_rec m./2) 1%Z
*)

  Admitted.

  
(* END *)
