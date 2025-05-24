(*
Well-founded recursion done right
Xavier Leroy
*)

Require Import BinPos PeanoNat.
Require Export Wf_nat.
Require Import Lia.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(**
(1) Init/Wf.v での Acc の定義

関係Rがあり、``R y x`` のとき y でAccが成り立つならば、x でAccが成り立つ。
*)
Print Acc.
(*
Inductive Acc (A : Type) (R : A -> A -> Prop) (x : A) : Prop :=
    Acc_intro : (forall y : A, R y x -> Acc R y) -> Acc R x.
*)
Check Acc : forall A : Type, (A -> A -> Prop) -> A -> Prop.
Check Acc_rec
  : forall (A : Type) (R : A -> A -> Prop) (P : A -> Set),
    (forall x : A, (forall y : A, R y x -> Acc R y) ->
                   (forall y : A, R y x -> P y) ->
                   P x) ->
    forall x : A, Acc R x -> P x.

Check Acc_intro
  : forall (A : Type) (R : A -> A -> Prop) (x : A),
    (forall y : A, R y x -> Acc R y) -> Acc R x.

(* 関係Rがあり、x でAccが成り立つならば、``R y x`` のとき y でAccが成り立つ。 *)
Check Acc_inv : forall (A : Type)
                       (R : A -> A -> Prop)
                       (x : A),
    Acc R x -> (forall y : A, R y x -> Acc R y).

(**
(2) 補題：bによる剰余はb未満である。
*)
Remark gcd_oblig (a b : nat) (NE : b <> 0) : a mod b < b.
Proof.
  intros.
  apply Nat.mod_bound_pos; lia.
Qed.

(**
(2) 関係ltのもとで、b で Acc が成り立つ (ACC : Acc lt b) ならば、
``a mod b`` でAccが成り立つ。なぜなら ``a mod b < b`` 。
*)
Section a.
  Variable a b : nat.
  Variable ACC : Acc lt b.
  Variable NE : b <> 0.

  (* The second argument to Acc_inv is any (opaque) proof of a mod b < b. *)
  Check @gcd_oblig a b NE : a mod b < b.
  Check @Acc_inv nat lt b ACC : forall y : nat, y < b -> Acc lt y.
  Check @Acc_inv nat lt b ACC (a mod b) (@gcd_oblig a b NE) : Acc lt (a mod b).
  
  Check Acc_inv ACC (@gcd_oblig a b NE) : Acc lt (a mod b).
End a.

(*
(3) gcd_rec の定義

``Acc : Acc lt b`` の証明を引数として加える。
ここで、bは減少引数、lt は整根拠順序である。
この証明において、関数は構造的に再帰的になる。
*)
Fixpoint gcd_rec (a b : nat) (ACC : Acc lt b) {struct ACC} : nat :=
  match Nat.eq_dec b 0 with
  | left EQ  => a
  | right NE => @gcd_rec b (a mod b) (Acc_inv ACC (@gcd_oblig a b NE))
                         (*          ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ *)
                         (*           Acc lt (a mod b)                 *)
  end.
(* ``Acc lt b`` から ``Acc lt (a mod b)`` へは構造的に小さくなっている。 *)

(*
(4) 証明
*)
Definition is_gcd (A B C : nat) : Prop :=
  (* A divides both B and C *)
  Nat.divide A B /\ Nat.divide A C /\
    (* A is the greatest such number: any D that divides both B and C must divide A *)
    (forall D : nat, Nat.divide D B -> Nat.divide D C -> Nat.divide D A).

(**
再帰定義を展開するために、整礎帰納法を実行し、
それに続いてACC引数を destruct するだけです
*)
Lemma gcd_rec_correct (b a : nat) ACC :
  b <= a -> is_gcd (@gcd_rec a b ACC) a b.
Proof.
  induction b using (well_founded_induction lt_wf); (* 整礎帰納法 *)
    intros; destruct ACC; simpl.            (* ACC引数をdestruct *)
  destruct (Nat.eq_dec b 0).
  - (* base case : b = 0 *)
    rewrite e.
    unfold is_gcd.
    split; [| split].
    + now apply Nat.divide_refl.
    + now apply Nat.divide_0_r.
    + easy.
  - (* inductive step : b ≠ 0 *)
    set (b' := a mod b).
    assert (Hb'_lt_b : b' < b).
    {
      apply gcd_oblig; assumption.
    }
    assert (Hb'_le_a : b' <= a).
    {
      apply Nat.Div0.mod_le.
    }
    assert (Acc lt b') as Hb'.
    {
      now apply a0.
    }.
    Check H b' Hb'_lt_b (a0 b' Hb'_lt_b) Hb'_le_a
      : is_gcd (gcd_rec a (a0 b' Hb'_lt_b)) a b'.
    specialize (H b' Hb'_lt_b (a0 b' Hb'_lt_b) Hb'_le_a) as IH'.
    
    Check (H b' Hb'_lt_b Hb' Hb'_le_a)
      : is_gcd (gcd_rec a Hb') a b'.
    specialize (H b' Hb'_lt_b Hb' Hb'_le_a) as IH.
Admitted.

(* END *)
