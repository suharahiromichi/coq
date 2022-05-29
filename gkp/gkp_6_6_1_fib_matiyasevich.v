(*
コンピュータの数学 6.6

Matiyasevich の補題

マティヤセビッチの補題の一部をCoqで形式化してみる。

GKP p.268 の 13行目の式を証明する。

F_(k*n)   = k * F_n * (F_(n+1))^k-1 mod (F_n)^2
かつ
F_(k*n+1) = (F_(n+1))^k             mod (F_n)^2
 *)

From mathcomp Require Import all_ssreflect.
From mathcomp Require Import all_algebra.
From common Require Import ssromega.

Import GRing.Theory.         (* mulrA などを使えるようにする。 *)
Import Num.Theory.           (* unitf_gt0 などを使えるようにする。 *)
Import intZmod.              (* addz など *)
Import intRing.              (* mulz など *)
Open Scope ring_scope.       (* 環の四則演算を使えるようにする。 *)

Fixpoint fibn (n : nat) : nat :=
    match n with
    | 0 => 0
    | 1 => 1
    | (m.+1 as pn).+1 => fibn m + fibn pn (* fibn n.-2 + fibn n.-1 *)
    end.

Definition fibz (n : nat) : int := fibn n.

Definition mati_1 k n :=
  (fibz (k * n) = k%:Z * fibz n * fibz n.+1 ^ k.-1 %[mod (fibz n)^2])%Z.

Definition mati_2 k n :=
  (fibz (k * n).+1 = fibz n.+1 ^ k %[mod (fibz n)^2])%Z.

Lemma fibn_2 n : fibz n + fibz n.+1 = fibz n.+2.
Proof.
  done.
Qed.

Lemma transpos (a b c : int) : a = c + b -> a - b = c.
Proof.
  move/eqP => H.
  apply/eqP.
  by rewrite subr_eq.
Qed.

Lemma fibz_1 n : (0 < n)%N -> fibz n.-1 = fibz n.+1 - fibz n.
Proof.
  case: n => // n Hn.
  rewrite -pred_Sn -fibn_2.
  apply: esym.
  by apply: transpos.
Qed.

Lemma m_addz m n p q d  :
  (m = n %[mod d])%Z -> (p = q %[mod d])%Z -> (m + p = n + q %[mod d])%Z.
Proof.
Admitted.                                   (* gkp_4_6_modulo.v *)

Lemma m_mulz m n p q d  :
  (m = n %[mod d])%Z -> (p = q %[mod d])%Z -> (m * p = n * q %[mod d])%Z.
Proof.
Admitted.                                   (* gkp_4_6_modulo.v *)

(* 加法定理 *)
Lemma fib_addition n m :
  (0 < n)%N -> fibz (n + m) = fibz n * fibz m.+1 + fibz n.-1 * fibz m.
Proof.
Admitted.                                   (* ssr_fib_2.v *)

Check modzMDl : forall p m d : int, (p * d + m = m %[mod d])%Z.
Lemma modzMDr : forall p m d : int, (m + p * d = m %[mod d])%Z.
Proof.
  move=> p m d.
  rewrite [m + p * d]addrC.
  by rewrite modzMDl.
Qed.

Lemma modzMDr' : forall p m d : int, (m - p * d = m %[mod d])%Z.
Proof.
  move=> p m d.
  rewrite [m - p * d]addrC -mulNr.
  by rewrite modzMDl.
Qed.

Lemma l_mati k n : (1 < n)%N -> mati_1 k n /\ mati_2 k n.
Proof.
  move=> Hn.
  elim: k => /= [| k [IHk1 IHk2]].
  - rewrite /mati_1 /mati_2.
    split.
    + done.
    + by rewrite expr0z.
  - rewrite /mati_1 /mati_2.
    rewrite /mati_1 in IHk1.
    rewrite /mati_2 in IHk2.
    split.
    + rewrite -pred_Sn.
      have -> : (k.+1 * n = n + k * n)%N by done.
      rewrite fib_addition; last ssromega. (* 左辺加法定理 fibn (n + kn) *)
      rewrite fibz_1; last ssromega.
      
      have -> : (fibz n * fibz (k * n).+1 + (fibz n.+1 - fibz n) * fibz (k * n)
                = fibz n * (fibz n.+1 ^ k) +
                    (fibz n.+1 - fibz n) * (k%:Z * fibz n * fibz n.+1 ^ k.-1)
                %[mod fibz n ^ 2])%Z. (* 左辺 IHk1 と IHk2 で書き換える。 *)
      by apply: m_addz; apply: m_mulz.
      
      have -> : fibz n * (fibz n.+1 ^ k) +
                  (fibz n.+1 - fibz n) * (k%:Z * fibz n * fibz n.+1 ^ k.-1)
                = fibz n * (fibz n.+1 ^ k) +
                    k%:Z * fibz n * fibz n.+1 ^ k - k%:Z * fibz n.+1 ^ k.-1 * fibz n ^ 2.
      * rewrite mulrBl.                     (* 左辺展開 *)
        rewrite addrA.
        congr (_ + _ - _). 
        ** rewrite mulrCA -exprSz.
           case: k IHk1 IHk2 => [| k IHk1 IHk2].
           *** by rewrite !mul0r.
           *** by rewrite prednK.
        ** rewrite !mulrA.
           rewrite [fibz n * k]mulrC.
           rewrite -![RHS]mulrA.
           rewrite -[fibz n.+1 ^ k.-1 * (fibz n * fibz n)]mulrC.
           rewrite !mulrA.
           done.
     have -> : (fibz n * (fibz n.+1 ^ k) + k%:Z * fibz n * fibz n.+1 ^ k
                - k%:Z * fibz n.+1 ^ k.-1 * fibz n ^ 2
                = fibz n * (fibz n.+1 ^ k) + k%:Z * fibz n * fibz n.+1 ^ k 
               %[mod fibz n ^ 2])%Z.
        by rewrite modzMDr'.            (* 左辺の fib n ^ 2 を消す。 *)
      
      have -> : fibz n * (fibz n.+1 ^ k) + k%:Z * fibz n * fibz n.+1 ^ k
                = k.+1%:Z * fibz n * fibz n.+1 ^ k
        by rewrite -mulrDl.                    (* 左辺 整理する。 *)
      done.
      
    + have -> : ((k.+1 * n).+1 = (k * n).+1 + n)%N by ssromega.
      rewrite fib_addition; last ssromega. (* 左辺加法定理 fibn (kn+1 + n) *)
      
      have -> : (fibz (k * n).+1 * fibz n.+1 + fibz (k * n) * fibz n
                 = (fibz n.+1 ^ k) * fibz n.+1 + (k%:Z * fibz n * fibz n.+1 ^ k.-1) * fibz n
                %[mod fibz n ^ 2])%Z
        by apply: m_addz; apply: m_mulz. (* 左辺 IHk1 と IHk2 で書き換える。 *)

      have -> : fibz n.+1 ^ k * fibz n.+1 + k%:Z * fibz n * fibz n.+1 ^ k.-1 * fibz n
                = fibz n.+1 ^ k.+1 + k%:Z * fibz n.+1 ^ k.-1 * fibz n ^ 2
        (* 左辺を整理する。 *)
        by rewrite -exprSr; congr (_ + _); rewrite -!mulrA; congr (_ * _); rewrite mulrCA.
      
      have -> : (fibz n.+1 ^ k.+1 + k%:Z * fibz n.+1 ^ k.-1 * fibz n ^ 2
                 = fibz n.+1 ^ k.+1 %[mod fibz n ^ 2])%Z
        by rewrite modzMDr.            (* 左辺の fib n ^ 2 を消す。 *)
      done.
Qed.

(* END *)

