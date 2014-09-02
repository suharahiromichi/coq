(* http://ilyasergey.net/pnp/ *)

Module FACT.

(** * 「Hoare Type Theory の基礎」から抜粋 *)
(** * Elements of Hoare Type Theory *)

Require Import ssreflect ssrbool ssrnat eqtype seq ssrfun.

Add LoadPath "./../htt".
Require Import prelude pred pcm unionmap heap heaptac stmod stsep stlog stlogR.  

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ** 階乗計算手続 の証明 *)
(* ** Verifying the factorial procedure mechanically *)

(** 純粋関数型の階乗 *)
Fixpoint fact_pure n := if n is n'.+1 then n * (fact_pure n') else 1.

(** ループ不変式 *)
Definition fact_inv (n acc : ptr) (N : nat) h : Prop := 
  exists n' a': nat, 
  [/\ h = n :-> n' \+ acc :-> a' & 
      (fact_pure n') * a' = fact_pure N].

(** 階乗の加算器(accumulator)部分の証明  *)

Definition fact_acc_tp n acc := 
  unit -> {N}, 
     STsep (fact_inv n acc N, 
           [vfun (res : nat) h => fact_inv n acc N h /\ res = fact_pure N]).

Program Definition fact_acc (n acc : ptr): fact_acc_tp n acc := 
  Fix (fun (loop : fact_acc_tp n acc) (_ : unit) => 
    Do (a1 <-- !acc;
        n' <-- !n;
        if n' == 0 then ret a1
        else acc ::= a1 * n';;
             n ::= n' - 1;;
             loop tt)).
Next Obligation. 
  apply: ghR => i N. 
  case=> n' [a'][->{i}] Hi _. 
  heval. 
  case X: (n' == 0). 
  Search _ (verify _ _ _) (ret _).
  - apply: val_ret => /= _. 
    move/eqP: X => Z; subst n'.
    split; first by exists 0, a' => //.
      by rewrite mul1n in Hi.
  - heval.
    apply: (gh_ex N). 
    apply: val_doR => // _.
    exists (n'-1), (a' * n'); split => //=. 
    rewrite -Hi => {Hi}; rewrite [a' * _]mulnC mulnA [_ * n']mulnC.
      by case: n' X => //= n' _; rewrite subn1 -pred_Sn. 
Qed.

(** 全体の証明  *)

Definition fact_tp N :=
  STsep ([Pred h | h = Unit], 
         [vfun res h => res = fact_pure N /\ h = Unit]).

Program Definition fact (N : nat) : fact_tp N :=
  Do (n   <-- alloc N;
      acc <-- alloc 1;
      res <-- fact_acc n acc tt;
      dealloc n;;
      dealloc acc;;
      ret res).
Next Obligation.
  rewrite /conseq => /=.
  move=> _ ->.
  heval=> n; heval=> acc; rewrite joinC unitR.
  apply: bnd_seq => /=; apply: (gh_ex N); apply: val_doR => //.
  - by exists N, 1; rewrite muln1.
  - by move=> _ _ [[n'][a'][->] _ ->] _; heval.
Qed.

End FACT.

(* END *)
