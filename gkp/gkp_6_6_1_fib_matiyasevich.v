(*
コンピュータの数学 6.6

Matiyasevich の補題
 *)
From mathcomp Require Import all_ssreflect.
From mathcomp Require Import all_algebra.
From common Require Import ssromega.

Fixpoint fibn (n : nat) : nat :=
    match n with
    | 0 => 0
    | 1 => 1
    | (m.+1 as pn).+1 => fibn m + fibn pn (* fibn n.-2 + fibn n.-1 *)
    end.

Definition mati_1 k n :=
  fibn (k * n) = k * fibn n * fibn n.+1 ^ k.-1 %[mod (fibn n)^2].

Definition mati_2 k n :=
  fibn (k * n).+1 = fibn n.+1 ^ k %[mod (fibn n)^2].  

Lemma fibn_2 n : fibn n + fibn n.+1 = fibn n.+2.
Proof.
  done.
Qed.

Lemma fibn_1 n : 1 < n -> fibn n.-1 = fibn n.+1 - fibn n.
Proof.
  case: n => // n Hn.
  rewrite -pred_Sn -fibn_2.
  by rewrite -addnBA // subnn addn0.
Qed.

Lemma m_addn m n p q d  :
  m = n %[mod d] -> p = q %[mod d] -> m + p = n + q %[mod d].
Proof.
Admitted.

Lemma m_muln m n p q d  :
  m = n %[mod d] -> p = q %[mod d] -> m * p = n * q %[mod d].
Proof.
Admitted.

(* 加法定理 *)
Lemma fib_addition n m :
  1 <= n ->
  fibn (n + m) = fibn n * fibn m.+1 + fibn n.-1 * fibn m.
Proof.
Admitted.    

(* これは、intdiv.v でないと成り立たいだろう。 *)
Lemma modzMDr : forall p m d : nat, m - p * d = m %[mod d].
Proof.
Admitted.

Lemma modnMDr : forall p m d : nat, m + p * d = m %[mod d].
Proof.
Admitted.

Lemma l_mati k n : 1 < n -> mati_1 k n /\ mati_2 k n.
Proof.
  move=> Hn.
  elim: k => /= [| k [IHk1 IHk2]].
  - rewrite /mati_1 /mati_2.
    split.
    + done.
    + by rewrite expn0.
  - rewrite /mati_1 /mati_2.
    rewrite /mati_1 in IHk1.
    rewrite /mati_2 in IHk2.
    split.
    + rewrite -pred_Sn.
      have -> : k.+1 * n = n + k * n by done.
      rewrite fib_addition; last ssromega. (* 左辺加法定理 fibn (n + kn) *)
      
      have -> : fibn n.-1 = fibn n.+1 - fibn n
        by rewrite -fibn_1.                 (* 左辺fibn の計算 *)
      
      have -> : fibn n * fibn (k * n).+1 + (fibn n.+1 - fibn n) * fibn (k * n)
                = fibn n * (fibn n.+1 ^ k) +
                    (fibn n.+1 - fibn n) * (k * fibn n * fibn n.+1 ^ k.-1)
                %[mod fibn n ^ 2]
        by apply: m_addn; apply: m_muln. (* 左辺 IHk1 と IHk2 で書き換える。 *)
      
      have -> : fibn n * (fibn n.+1 ^ k) +
                  (fibn n.+1 - fibn n) * (k * fibn n * fibn n.+1 ^ k.-1)
                = fibn n * (fibn n.+1 ^ k) +
                    k * fibn n * fibn n.+1 ^ k - k * fibn n.+1 ^ k.-1 * fibn n ^ 2.
      rewrite mulnBl.                 (* 左辺展開 *)
      rewrite addnBA; last admit.     (* 整数でないと成り立たない。 *)
      congr (_ + _ - _).
      * by rewrite mulnCA -expnS prednK; last admit.
      * rewrite mulnCA.
        rewrite -!mulnA.
        congr (k * _).
        rewrite [fibn n.+1 ^ k.-1 * fibn n ^ 2]mulnC.
        by rewrite !mulnA mulnn.
        
      have -> : fibn n * (fibn n.+1 ^ k) + k * fibn n * fibn n.+1 ^ k
                - k * fibn n.+1 ^ k.-1 * fibn n ^ 2
                = fibn n * (fibn n.+1 ^ k) + k * fibn n * fibn n.+1 ^ k 
                  %[mod fibn n ^ 2]
        by rewrite modzMDr.            (* 左辺の fib n ^ 2 を消す。 *)
      
      have -> : fibn n * (fibn n.+1 ^ k) + k * fibn n * fibn n.+1 ^ k
                = k.+1 * fibn n * fibn n.+1 ^ k
        by ssromega.                        (* 左辺 整理する。 *)
      done.
      
    + have -> : (k.+1 * n).+1 = (k * n).+1 + n by ssromega.
      rewrite fib_addition; last ssromega. (* 左辺加法定理 fibn (kn+1 + n) *)
      
      have -> : fibn (k * n).+1 * fibn n.+1 + fibn (k * n) * fibn n
                = (fibn n.+1 ^ k) * fibn n.+1 + (k * fibn n * fibn n.+1 ^ k.-1) * fibn n
                %[mod fibn n ^ 2]
        by apply: m_addn; apply: m_muln. (* 左辺 IHk1 と IHk2 で書き換える。 *)

      have -> : fibn n.+1 ^ k * fibn n.+1 + k * fibn n * fibn n.+1 ^ k.-1 * fibn n
                = fibn n.+1 ^ k.+1 + k * fibn n.+1 ^ k.-1 * fibn n ^ 2
        by rewrite -expnSr; congr (_ + _);
           rewrite -!mulnA; congr (_ * _);
           rewrite mulnCA mulnn.           (* 左辺を整理する。 *) 
      
      have -> : fibn n.+1 ^ k.+1 + k * fibn n.+1 ^ k.-1 * fibn n ^ 2
                = fibn n.+1 ^ k.+1 %[mod fibn n ^ 2]
        by rewrite modnMDr.            (* 左辺の fib n ^ 2 を消す。 *)
      
      done.
Admitted.

(* END *)
