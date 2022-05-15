(**
MUパズル (MU Puzzle) の証明
======

2022_05_14 @suharahiromichi

*)

From mathcomp Require Import all_ssreflect.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(**
# MUパズルの証明
*)
Section MU_Puzzle.

(**
MUパズルで使用する文字を定義する。
*)
  Inductive MIU :=
  | M
  | I
  | U.

(**
MUパズルの規則による文字列の生成規則を定義する。
*)
  Inductive MU : seq MIU -> Prop :=
  | S_MU  : MU [:: M; I]
  | S_xIU : forall x, MU (x ++ [:: I]) -> MU (x ++ [:: I; U])
  | S_Mxx : forall x, MU ([:: M] ++ x) -> MU ([:: M] ++ x ++ x)
  | S_xUy : forall x y, MU (x ++ [:: I; I; I] ++ y) -> MU (x ++ [:: U] ++ y)
  | S_xy  : forall x y, MU (x ++ [:: U; U] ++ y) -> MU (x ++ y)
  .

(**
文字列の I の数を算える関数 ci を定義する。
*)
  Fixpoint ci (s : seq MIU) : nat :=
    match s with
    | [::] => 0
    | I :: s => (ci s).+1
    | _ :: s => (ci s)
    end.
  
(**
ci が、文字列の連結(cat)について分配則を満たすことを証明する。
*)
  Lemma ci_cat (x y : seq MIU) : ci (x ++ y) = ci x + ci y.
  Proof.
    elim: x => //.                        (* x = a :: x の場合 *)
    case=> x IHx //=.                     (* a による場合分けする。 *)
    rewrite addSn.
    by rewrite IHx.
  Qed.
  
(**
補題の証明で使用するモジュラスについての補題を証明しておく。
これは一般に成立するわけではなく、
``3 %| 2 * n`` の2と3が互いに素だからである。
*)
  Lemma l_mod_2n_eq (n : nat) : (3 %| n + n) = (3 %| n).
  Proof.
    rewrite addnn -mul2n.
    by apply: Gauss_dvdr.
  Qed.
  
(**
補題を証明する。

``MU s`` に対する帰納法を適用する。
解りやすさのために、一律に対偶を適用する。
*)
  Lemma miu_inv (s : seq MIU) : MU s -> ~~ (3 %| ci s).
  Proof.
    elim=> //= [x | x | x y | x y] _;
           apply: contraTT; rewrite 2!negbK.
    
    (* 3 %| ci (x ++ [:: I; U]) -> 3 %| ci (x ++ [:: I]) *)
    - have -> : x ++ [:: I; U] = (x ++ [:: I]) ++ [:: U]
        by rewrite -catA cat1s.
      by rewrite ci_cat //= addn0.
      
    (* 3 %| ci (x ++ x) -> 3 %| ci x *)
    - by rewrite ci_cat l_mod_2n_eq.

    (* 3 %| ci (x ++ U :: y) -> 3 %| ci (x ++ [:: I, I, I & y]) *)
    - have -> : x ++ (U :: y) = x ++ [:: U] ++ y by done.
      rewrite 2!ci_cat /= add0n.
      have -> : x ++ (I :: I :: I :: y) = x ++ [:: I; I; I] ++ y by done.
      rewrite 2!ci_cat /=.
      have -> : ci x + (3 + ci y) = ci x + ci y + 3
        by rewrite -addnACl [ci y + ci x]addnC.
      by move=> H; rewrite dvdn_addl.
      
    (* 3 %| ci (x ++ y) -> 3 %| ci (x ++ [:: U, U & y]) *)
    - have -> : x ++ (U :: U :: y) = x ++ [:: U; U] ++ y by done.
      by rewrite 3!ci_cat /= add0n.
  Qed.
  
(**
補題を適用して背理法を適用すると、

``3 %| ci [:: M; U]``

を証明すればよい。これは計算すれば、

``3 %| 0``

であり、成立することは自明である。
*)
  Theorem mu : ~ MU [:: M; U].
  Proof.
    move/miu_inv/negP.
    by apply.
  Qed.
  
End MU_Puzzle.

(**

# 参考

[1] MUパズル https://www.principia-m.com/doc/0/

[1] MUパズル https://zenn.dev/hatsugai/articles/dacd6c19bbd210

 *)

(* END *)
