(*
   Prop型のInductive と、inversionタクティクの組み合わせ。
*)


Require Import Omega.


Inductive Label : Set :=
| LblA
| LblB
| LblC
| LblD
| LblE.


Inductive is : Label -> nat -> Prop :=
| is1 : is LblA 1
| is2 : is LblB 2
| is3 : is LblA 3
| is4 : is LblE 4.
Hint Resolve is1 is2 is3 is4 : labels.


(*
   HA : is Lbl n のとき、
   inversion HA.
   で、is Lbl 1 と is Lbl 3 のふたつが選ばれ、サブゴールがふたつ作られる。
   前者(n = 1)は、条件の 3 <= n に反するので、捨てられる（サブゴールの証明が終了）
   *)


Lemma t :
  forall n, (is LblA n) /\ 3 <= n ->
    exists m, is LblB m /\ m < n ->
      exists l, is LblA l /\ l < m.
Proof.
  intros n H.
  destruct H as [HA Hn].
  inversion HA.                             (* HA : is Lbl n *)


  (* is LblA 1 *)
  exists 2.
  intros H1.
  exists 3.                                 (* is LblA 3 を指定する。*)
  split.
  apply is3.                                (* auto with labels. *)
  omega.                                    (* 3 < 2 *)
  (* だが前提が成立しないので、サブゴールの証明は終了する。*)
  
  (* is LblA 3 *)
  exists 2.
  intros H2.
  exists 1.                                 (* is LblA 1 を指定する。*)
  split.
  apply is1.                                (* auto with labels. *)
  omega.                                    (* 1 < 2 *)
Qed.


(*   
   inversionの代わりにinductionとすると、n=1,n=2,n=3,n=4のすべてを展開する。
   おそらく、解けない。
   *)


(* END *)