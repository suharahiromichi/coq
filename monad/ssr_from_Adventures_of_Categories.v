(**
「圏論の歩き方」から
*)

Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq.
Require Import choice fintype.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Unset Printing Implicit.           (* Unset : implicitな引数を表示しない。 D:しない。 A:する。*)
Unset Printing Coercions.          (* Unset : コアーションを表示しない     D:しない。 A:する。*)
Set Printing Notations.            (*   Set : Notation を使って表示する。  D:する。  A:しない。*) 
Unset Printing Universe.           (* Unset : 高階のTypeを表示しない。     D:しない。 A:- *)


Definition c {Z X : Type} (x : X) (_ : Z) := x.

Lemma P4 : forall (Z X Y : Type) (f : X -> Y),
             (forall (x1 x2 : X), f x1 = f x2 -> x1 = x2)
             <->
             (forall (g h : Z -> X), (f \o g) =1 (f \o h) -> g =1 h).
Proof.
  move=> Z X Y f.
  split=> H.
  - move=> g h H1 z.
    have H' := H (g z) (h z).
    by apply/H'/H1.

  - move=> x1 x2 H1.
    have H' := H (c x1) (c x2).
    rewrite /eqfun //= in H'.               (* この行は、なくてもよい。 *)
    apply: H'.
    + move=> x.
      (* c x1 x ==> x1, c x2 x ==> x2 より Goal は x1 = f x2 *)
      by apply: H1.
    + admit.
      (* H' の後件 forall x : Z, c x1 x = c x2 x の (x : Z) が使えずに残ってしまう。 *)
Qed.

(* END *)
