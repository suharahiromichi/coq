(**
プログラミング Coq 「証明ができない！ こんなとき」
http://www.iij-ii.co.jp/lab/techdoc/coqt/coqt6.html

帰納法に注意 における、generalize の説明をSSReflectに移してみる。
@suharahiromichi
*)

Require Import ssreflect ssrbool ssrnat seq.

(* Coqでの説明に忠実な例 *)
Theorem fold_symmetric :
  forall (A:Type) (f:A -> A -> A),
    (forall x y z:A, f x (f y z) = f (f x y) z) ->
    (forall x y:A, f x y = f y x) ->
    forall (a:A) (l:list A), foldl f a l = foldr f a l.
Proof.
  move=> A f H  H0 a l.
  case: l.
  done.

  simpl.
  move=> a0 l.
  move: a a0.                               (* generalize *)
  elim l.
    simpl.
    apply H0.

    simpl. clear l.
    move=> a1 l IHl a3 a2.
    rewrite H.
    replace (f (f a3 a2) a1) with (f a3 (f a2 a1)).
    apply IHl.  
    apply H.
Qed.

(* より みなおした例 *)
Theorem fold_symmetric' :
  forall (A:Type) (f:A -> A -> A),
    (forall x y z:A, f x (f y z) = f (f x y) z) ->
    (forall x y:A, f x y = f y x) ->
    forall (a:A) (l:list A), foldl f a l = foldr f a l.
Proof.
  move=> A f H H0 a l. move: a.
  case: l.
    (* l = [] のとき。 *)
    by [].
    
  (* l = a :: l のとき。 *)
  move=> a0 l.
  elim: l a0 => a1 l.                  (* 「:」の右の a0 が 必須のgeneralize。 *)
  (* move: a0; elim: l => a1 l. と同じ。*)
  
    (* l = a1 :: [] のとき。 *)
    by apply H0.

  (* l = a2 :: a1 :: l のとき。 *)
  move=> IHl a2 a3.
  rewrite /= H.
  replace (f (f a3 a2) a1) with (f a3 (f a2 a1)).
    by apply IHl. 

  (* replace できることを証明する。 *)
  by apply H.
Qed.

(* END *)
