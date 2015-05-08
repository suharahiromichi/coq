(** cheat sheet ssralg, ssrint *)
(** SSReflect で 整数 Z (int) を扱うときのメモ *)

Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq.
Require Import ssralg ssrint.
Import GRing.Theory.
Open Scope ring_scope.                      (* %Rが不要になる。 *)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Variables x y z t : int.
Variables n m : nat.
Variables b : bool.

Goal x + (y + z) = x + y + z.                     by apply addrA. Qed. (* associative *)
Goal x + y = y + x.                               by apply addrC. Qed. (* commutative *)
Goal 0 + x = x.                                   by apply add0r. Qed. (* left_id *)
Goal -x + x = 0.                                  by apply addNr. Qed. (* left_inverse *)
Goal x + 0 = x.                                   by apply addr0. Qed. (* right_id *)
Goal x + -x = 0.                                  by apply addrN. Qed. (* right_inverse *)
Goal x + -x = 0.                                  by apply subrr. Qed. (* addrN *)
Goal x + (y + z) = y + (x + z).                   by apply addrCA. Qed. (* left_commutative *)
Goal x + y + z = (x + z) + y.                     by apply addrAC. Qed. (* right_commutative *)
Goal (x + y) + (z + t) = (x + z) + (y + t).       by apply addrACA. Qed. (* interchange *)
Goal -x + (x + y) = y.                            by apply addKr. Qed.   (* left_loop *)
Goal x + (-x + y) = y.                            by apply addNKr. Qed. (* rev_left_loop *)
Goal x + y + -y = x.                              by apply addrK. Qed.  (* right_loop *)
Goal x + -y + y = x.                              by apply addrNK. Qed. (* rev_right_loop *)
Goal x + -y + y = x.                              by apply subrK. Qed.  (* addrNK *)
Goal x + y = x + z -> y = z.                      by apply addrI. Qed. (* right_injective *)
Goal x + y = z + y -> x = z.                      by apply addIr. Qed. (* left_injective *)
Goal -(-x) = x.                                   by apply opprK. Qed. (* involutive (= cancel f f) *)
Goal -x = -y -> x = y.                            by apply oppr_inj. Qed. (* injective *)
Goal x = 0%R -> -x = x.                by move=> ->; apply oppr0. Qed.
Goal (-x == 0) = (x == 0).                        by apply oppr_eq0. Qed.
Goal x - 0 = x.                                   by apply subr0. Qed.
Goal 0 - x = -x.                                  by apply sub0r. Qed.
Goal -(x + y) = -x + -y.                          by apply opprD. Qed.    (* morphism_2 *)
Goal -(x - y) = y - x.                            by apply opprB. Qed.
Goal (x - z == y) = (x == y + z).                 by apply subr_eq. Qed.
Goal (x - y == 0) = (x == y).                     by apply subr_eq0. Qed.
Goal (x + y == 0) = (x == -y).                    by apply addr_eq0. Qed.
Goal (-x == -y) = (x == y).                       by apply eqr_opp. Qed.
Goal (-x == y) = (x == -y).                       by apply eqr_oppLR. Qed.

(* "*+" : int -> nat -> int、x * (+n) の意味。 *)
(* "*-" : int -> nat -> int、x * (-n) の意味。 *)
(* "*" : int -> int -> int *)

Goal x *+ 0 = 0.                                  by apply mulr0n. Qed.
Goal x *+ 1 = x.                                  by apply mulr1n. Qed.
Goal x *+ 2 = x + x.                              by apply mulr2n. Qed.
Goal x *+ n.+1 = x + x *+ n.                      by apply mulrS. Qed.
Goal x *+ n.+1 = x *+ n + x.                      by apply mulrSr. Qed.
Goal x *+ b = (if b then x else 0).               by apply mulrb. Qed.
Goal x = 0 -> x *+ n = x.              by move=> ->; apply mul0rn. Qed.
Goal (-x) *+ n = x *- n.                          by apply mulNrn. Qed.
Goal (x + y) *+ n = (x *+ n) + (y *+ n).          by apply mulrnDl. Qed. (* morphism_2 *)
Goal x *+ (m + n) = x *+ m + x *+ n.              by apply mulrnDr. Qed.
Goal (x - y) *+ n = (x *+ n) - (y *+ n).          by apply mulrnBl. Qed. (* morphism_2 *)
Goal n <= m -> x *+ (m - n) = x *+ m - x *+ n.    by apply mulrnBr. Qed.
Goal x *+ (m * n) = x *+ m *+ n.                  by apply mulrnA. Qed.
Goal x *+ m *+ n = x *+ n *+ m.                   by apply mulrnAC. Qed.

Goal x * (y * z) = x * y * z.                     by apply mulrA. Qed. (* associative *)
Goal 1 * x = x.                                   by apply mul1r. Qed. (* left_id *)
Goal x * 1 = x.                                   by apply mulr1. Qed. (* right_id *)
Goal (x + y) * z = x * z + y * z.                 by apply mulrDl. Qed. (* left_distributive *)
Goal x * (y + z) = x * y + x * z.                 by apply mulrDr. Qed. (* right_distributive *)
Goal 0 * x = 0.                                   by apply mul0r. Qed.  (* left_zero *)
Goal x * 0 = 0.                                   by apply mulr0. Qed.  (* right_zero *)

Goal x * (- y) = - (x * y).                       by apply mulrN. Qed.
Goal (- x) * y = - (x * y).                       by apply mulNr. Qed.
Goal (- x) * (- y) = x * y.                       by apply mulrNN. Qed.
Goal -1 * x = - x.                                by apply mulN1r. Qed.
Goal x * -1 = - x.                                by apply mulrN1. Qed.

Goal x ^+ 0 = 1.                                  by apply expr0. Qed.
Goal x ^+ 1 = x.                                  by apply expr1. Qed.
Goal x ^+ 2 = x * x.                              by apply expr2. Qed.
Goal x ^+ n.+1 = x * x ^+ n.                      by apply exprS. Qed.
(* Lemma expr0n n : 0 ^+ n = (n == 0%N)%:R :> R. *)
Goal x = 1 -> x ^+ n = 1.              by move=> ->; apply expr1n. Qed.
Goal x ^+ (m + n) = x ^+ m * x ^+ n.              by apply exprD. Qed.
Goal x ^+ n.+1 = x ^+ n * x.                      by apply exprSr. Qed.

Goal x ^+ (m * n) = x ^+ m ^+ n.                  by apply exprM. Qed.
Goal (x ^+ m) ^+ n = (x ^+ n) ^+ m.               by apply exprAC. Qed.
Goal (- x) ^+ n = (-1) ^+ n * x ^+ n.             by apply exprNn. Qed.
Goal (- x) ^+ 2 = x ^+ 2.                         by apply sqrrN.  Qed.
Goal (x + 1) ^+ 2 = x ^+ 2 + x *+ 2 + 1.          by apply sqrrD1. Qed.
Goal (x - 1) ^+ 2 = x ^+ 2 - x *+ 2 + 1.          by apply sqrrB1. Qed.
Goal x ^+ 2 - 1 = (x - 1) * (x + 1).              by apply subr_sqr_1. Qed.

(* END *)
