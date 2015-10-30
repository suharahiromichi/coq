(**
「圏論の歩き方」から
*)

Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq.
Require Import choice fintype.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Unset Printing Implicit.  (* Unset: implicitな引数を表示しない。D:しない。 A:する。*)
Unset Printing Coercions. (* Unset: コアーションを表示しない。  D:しない。 A:する。*)
Set Printing Notations.   (* Set: Notation を使って表示する。   D:する。   A:しない。*) 
Unset Printing Universe.  (* Unset: 高階のTypeを表示しない。    D:しない。 A:- *)

(**
命題4 関数fにおいて、以下は同値である。
- fは単射
- g,h : Z -> X について、f・g = f・h ならば g = h
 *)

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

(**
命題6'
X <- Z -> Y の仲介射は、Z = X x Y のとき恒等射(id)である。
*)

Definition product {X Y Z : Type} (f : Z -> X) (g : Z -> Y) :=
  fun (x : Z) => (f x, g x).

Notation "<< f , g >>" := (product f g).

Check <<S, S>> : nat -> nat * nat.
Check product S S.

Check <<S, S>> \o S.
Check <<S \o S, S \o S>>.

Lemma product_dist {X Y Z W : Type} (f : Z -> X) (g : Z -> Y) (h : W -> Z) :
  <<f, g>> \o h =1 <<f \o h, g \o h>>.
Proof.
  done.
Qed.  
(* 左分配則はなりたたない。 *)

Lemma id_uniqness {X : Type} (f : X -> X) : f \o f =1 f -> f =1 id.
Proof.
  admit.
Qed.

Lemma P6' {X Y : Type} (f : X * Y -> X) (g : X * Y -> Y) :
  f \o <<f, g>> =1 f ->
            g \o <<f, g>> =1 g ->
                      <<f, g>> =1 id.
Proof.
  move=> HX HY.
  apply: id_uniqness => x.
  rewrite (product_dist f g <<f, g>> x).
  rewrite /product /=.
  rewrite [f (f x, g x)](HX x).
  rewrite [g (f x, g x)](HY x).
  by [].
Qed.

(* END *)
