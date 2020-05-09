(**
https://github.com/suharahiromichi/coq/blob/master/pearl/ssr_ltac_1.v
 *)
From mathcomp Require Import all_ssreflect.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
(* Set Printing All. *)

Ltac find_neg_hypo :=
  match goal with
  | [ H : _ =  true            |- _ ] => idtac H
  | [ H : _ <> true            |- _ ] => idtac H; move/negP in H
  | [ H : _ =  false           |- _ ] => idtac H; move/negbT in H
  | [ H : _ <> false           |- _ ] => idtac H; move/negPf in H
  | [ H : ~ (is_true _)        |- _ ] => idtac H; move/negP in H
  | [ H : context [_ == true]  |- _ ] => idtac H; rewrite eqb_id in H
  | [ H : context [_ == false] |- _ ] => idtac H; rewrite eqbF_neg in H
  | [ H : context [~~ ~~ _ ]   |- _ ] => idtac H; rewrite negbK in H
  end.

Ltac find_neg_goal :=
  match goal with
  | [ |- _ =  true             ] => idtac
  | [ |- _ <> true             ] => idtac; apply/negP
  | [ |- _ =  false            ] => idtac; apply/negbTE
  | [ |- _ <> false            ] => idtac; apply/Bool.not_false_iff_true
  | [ |- ~ (is_true _)         ] => idtac; apply/negP
  | [ |- context [_ == true]   ] => idtac; rewrite eqb_id
  | [ |- context [_ == false]  ] => idtac; rewrite eqbF_neg
  | [ |- context [~~ ~~ _ ]    ] => idtac; rewrite negbK
  end.

Ltac find_neg :=
  repeat find_neg_hypo;
  repeat find_neg_goal.

(* Sample *)
Section Negative.

  Goal forall (a b : nat), (a == b) = true -> a == b.
  Proof.
    move=> a b H1.
    find_neg_hypo.
    done.    
  Qed.
  
  Goal forall (a b : nat), (a != b) = true -> a != b.
  Proof.
    move=> a b H1.
    find_neg_hypo.
    done.    
  Qed.

  Goal forall (a b : nat), (a == b) <> true -> a != b.
  Proof.
    move=> a b H1.
    find_neg_hypo.
    done.    
  Qed.
  
  Goal forall (a b : nat), (a != b) <> true -> ~~ (a != b).
  Proof.
    move=> a b H1.
    find_neg_hypo.
    done.    
  Qed.
  
  Goal forall (a b : nat), (a == b) = false -> a != b.
  Proof.
    move=> a b H1.
    find_neg_hypo.
    done.    
  Qed.
  
  Goal forall (a b : nat), (a != b) = false -> ~~ (a != b).
  Proof.
    move=> a b H1.
    find_neg_hypo.
    done.    
  Qed.
  
  Goal forall (a b : nat), (a == b) <> false -> a == b.
  Proof.
    move=> a b H1.
    find_neg_hypo.
    done.    
  Qed.
  
  Goal forall (a b : nat), (a != b) <> false -> a != b.
  Proof.
    move=> a b H1.
    find_neg_hypo.
    done.    
  Qed.
  
  Goal forall (a b : nat), ~ (a == b) -> a != b.
  Proof.
    move=> a b H1.
    find_neg_hypo.
    done.    
  Qed.
  
  Goal forall (a b : nat), ~ (a != b) -> ~~ (a != b).
  Proof.
    move=> a b H1.
    find_neg_hypo.
    done.    
  Qed.
  
  Goal forall (a b : nat), (a == b) == true -> a == b.
  Proof.
    move=> a b H1.
    find_neg_hypo.
    done.    
  Qed.
  
  Goal forall (a b : nat), (a != b) == true -> a != b.
  Proof.
    move=> a b H1.
    find_neg_hypo.
    done.    
  Qed.

  Goal forall (a b : nat), (a == b) == false -> a != b.
  Proof.
    move=> a b H1.
    find_neg_hypo.
    done.    
  Qed.
  
  Goal forall (a b : nat), (a != b) == false -> ~~ (a != b).
  Proof.
    move=> a b H1.
    find_neg_hypo.
    done.    
  Qed.

  Goal forall (a b : nat), ~~ ~~ (a == b) -> a == b.
  Proof.
    move=> a b H1.
    find_neg_hypo.
    done.
  Qed.
  
  Goal forall (a b : nat), ~~ (a != b) -> a == b.
  Proof.
    move=> a b H1.
    find_neg_hypo.
    done.
  Qed.
  
(**
## ゴール部 find_neg_goal の単体のテスト
 *)

  Goal forall (a b : nat), a == b -> (a == b) = true.
  Proof.
    move=> a b H1.
    find_neg_goal.
    done.    
  Qed.

  Goal forall (a b : nat), a != b -> (a != b) = true.
  Proof.
    move=> a b H1.
    find_neg_goal.
    done.    
  Qed.

  Goal forall (a b : nat), a != b -> (a == b) <> true.
  Proof.
    move=> a b H1.
    find_neg_goal.
    done.    
  Qed.
  
  Goal forall (a b : nat), ~~ (a != b) -> (a != b) <> true.
  Proof.
    move=> a b H1.
    find_neg_goal.
    done.    
  Qed.
  
  Goal forall (a b : nat), a != b -> (a == b) = false.
  Proof.
    move=> a b H1.
    find_neg_goal.
    done.    
  Qed.  
  
  Goal forall (a b : nat), ~~ (a != b) -> (a != b) = false.
  Proof.
    move=> a b H1.
    find_neg_goal.
    done.    
  Qed.  
  
  Goal forall (a b : nat), a == b -> (a == b) <> false.
  Proof.
    move=> a b H1.
    find_neg_goal.
    done.    
  Qed.  
  
  Goal forall (a b : nat), a != b -> (a != b) <> false.
  Proof.
    move=> a b H1.
    find_neg_goal.
    done.    
  Qed.  
  
  Goal forall (a b : nat), (a != b) -> ~ (a == b).
  Proof.
    move=> a b H1.
    find_neg_goal.
    done.    
  Qed.
  
  Goal forall (a b : nat), ~~ (a != b) -> ~ (a != b).
  Proof.
    move=> a b H1.
    find_neg_goal.
    done.    
  Qed.
  
  Goal forall (a b : nat), a == b -> (a == b) == true.
  Proof.
    move=> a b H1.
    find_neg_goal.
    done.    
  Qed.
  
  Goal forall (a b : nat), a != b -> (a != b) == true.
  Proof.
    move=> a b H1.
    find_neg_goal.
    done.    
  Qed.
  
  Goal forall (a b : nat), a != b -> (a == b) == false.
  Proof.
    move=> a b H1.
    find_neg_goal.
    done.    
  Qed.
  
  Goal forall (a b : nat), ~~ (a != b) -> (a != b) == false.
  Proof.
    move=> a b H1.
    find_neg_goal.
    done.    
  Qed.
  
  Goal forall (a b : nat), a == b -> ~~ (a != b).
  Proof.
    move=> a b H1.
    find_neg_goal.
    done.
  Qed.

  Goal forall (a b : nat), a == b -> ~~ ~~ (a == b).
  Proof.
    move=> a b H1.
    find_neg_goal.
    done.
  Qed.
  
(**
find_neg に変更すると、結果は変わりますが、無限ループになることはありません。
 *)
  
End Negative.

(* END *)
