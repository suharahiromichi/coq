(**
リフレクションというと、論理式とbool式の関係が重要だが、
それ以外にも、集合演算と論理演算の関係も馴染み深い。
もちろん、SSReflectはその機能を持っている。
そのリフレクションを使って問題を解いてみる。
*)

Require Import ssreflect ssrbool ssrnat.
Require Import fintype finset.

Variable T : finType.

(** 定理：B ⊆ A のとき、A - (A - B) = B *)

Theorem a_a_b__b (A B : {set T}) : B \subset A -> (A :\: (A :\: B)) = B.
Proof.
  (** (B ⊆ A) -> (A - (A - B)) = B *)
  move/setIidPr/setP => H. apply/setP; move: H.
  rewrite /eq_mem.

  (** (x ∈ (A ∩ B)) = (x ∈ B) -> (x ∈ A - (A - B)) = (x ∈ B) *)
  move=> H x; rewrite -(H x) {H}; apply/setDP/idP.

    (** ((x ∈ A) /\ ~(x ∈ (A - B)) -> (x ∈ A ∩ B) *)
    rewrite -in_setC setDE setCI => [[H]].
    move/setUP => H_ab; apply/setIP.
    by split; [ |
                case: H_ab => [H_a | H_b];
                [move/setCP in H_a | rewrite setCK in H_b]].

  (** (x ∈ A ∩ B) -> ((x ∈ A) /\ ~(x ∈ (A - B)) *)
  rewrite -in_setC => /setIP [Ha Hb].
  by split; [ |
              apply/setCP; rewrite /not => /setDP; elim => [_ H_b]; 
              move: H_b; rewrite -in_setC; move/setCP].
Qed.

(**
 実は、finsetの中の定理を使用すると、reflectionを使わずに解けてしまう。
 もちろん、これらの定理はreflectionで証明されているのだけれど。
 *)
Theorem a_a_b__b' (A B : {set T}) : B \subset A -> (A :\: (A :\: B)) = B.
Proof.
  move=> H.
  rewrite setDDr setDv set0U.
  by apply/setIidPr.
Qed.

(* END *)
