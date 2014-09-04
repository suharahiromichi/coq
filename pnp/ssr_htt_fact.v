(* http://ilyasergey.net/pnp/ *)

(** * 「Hoare Type Theory の基礎」から抜粋 *)
(** * Elements of Hoare Type Theory *)

Require Import ssreflect ssrbool ssrnat eqtype seq ssrfun.

Add LoadPath "./../htt".
Require Import prelude pred pcm unionmap heap heaptac
        stmod stsep stlog stlogR.  

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
        if n' == 0 then
          ret a1
        else
          acc ::= a1 * n';;
          n ::= n' - 1;;
          loop tt)).
Next Obligation. 
  apply: ghR => i N.                        (* conseq を消す。 *)
  case=> n' [a'] []. move=> -> Hi _.        (* case=> n' [a'][->{i}] Hi _.  *)

  Search (verify _ _ _).
  (* (x <-- !x; e x) を2個処理する。 *)
  do 2! [apply: bnd_readR => /=].           (* heval. *)
  
  case X: (n' == 0). 
  
  (* (n' == 0) = true *)  
  Search _ (verify _ _ _) (ret _).
  (* (ret v) を変形する。 *)
  - apply: val_ret => /= _.

    (* fact_inv n acc N (n :-> n' \+ acc :-> a') /\ a' = fact_pure N
       を証明する。 *)
    move/eqP : X => Z; subst n'.            (* 前提のXを n' = 0 にする。 *)
    rewrite mul1n in Hi.
    split.
    + exists 0. exists a'. rewrite /= mul1n. by [].
    + by [].

  (* (n' == 0) = false *)
  (* 代入文の並びなら、heval でよい。 *)
  - heval.
    
    Check (gh_ex N).
    (* (loop tt) を (Do loop tt) にするだけのように見えるが、
     ({N}, STsep (_, _)) を (STbin _) に、Nを追い出している。 *)
    Check (loop tt).
    Check (Do loop tt).
    apply: (gh_ex N). 

    (* Do loop tt からループ不変式を取り出す。 *)
    apply: val_doR => // _.

    (* fact_inv n acc N (n :-> (n' - 1) \+ acc :-> (a' * n'))
       を証明する。 *)
    rewrite /fact_inv. exists (n' - 1). exists (a' * n').
    split => //=. 
    rewrite -Hi=> {Hi}.
    rewrite [a' * _]mulnC mulnA [_ * n']mulnC.
    case: n' X => //= n' _.
    by rewrite subn1 -pred_Sn. 
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
  move=> i ->.                              (* rewriteは、 i = Unit  *)
  heval=> n.                                (* n <-- alloc N をheapに。 *)
  heval=> acc.                              (* acc <-- alloc 1 をheapに。 *)
  (* x \+ y を y \+ x *)
  (* x \+ Unit を x *)
  rewrite joinC unitR.

  Search _ (verify _ _ _).
  (* (x <-- e1; e2 x) を変形する。 *)
  apply: bnd_seq => /=.

  (* (fact_acc n acc tt) を (Do fact_acc n acc tt)  *)
  apply: (gh_ex N).

  (* (Do fact_acc n acc tt) *)
  apply: val_doR => //.

  (* fact_inv n acc N (n :-> N \+ acc :-> 1) の証明 *)
  - by exists N, 1; rewrite muln1.
  (*  *)
  - move=> x m.
    case.
    case=> n'.
    case=> a'.
    case=> H1 _ H2 _.
    (* move=> x m [] [n'] [a'] [] H1 _ H2 _.
       または
       move=> x m [[n'] [a'] [H1] _ H2 _]. *)
    rewrite H1 H2.
    by heval.                               (* e1;; e2;; ret _ *)
Qed.

(* END *)
