(**
Mathcomp の「不等式問題」を解決する
======
2019/05/06

この文書のソースコードは以下にあります。


https://github.com/suharahiromichi/coq/blob/master/pearl/ssr_ltac_1.v

 *)

(**
OCaml 4.07.1, Coq 8.9.0, MathComp 1.9.0
 *)

(**
# 説明

不等式について。Standard Coqの場合は、``a <> b`` は、
``~ (a = b)`` の表記（構文糖衣）にすぎません。また、二重否定もあまり出てきません。

これに対して、Mathcomp は、``a != b``  が ``~~ (a == b)`` であるのはともかくとして、
そもそもの、``a == b`` 自体が、``(a == b) = true`` の ``= true``
を略した形（コアーション）で、``(a == b) <> false`` もあり、という具合に
百花繚乱の状態です。二重否定も普通に出現することも事態を複雑にます。

これを、Mathcompの「不等式問題」と呼ばれています（提唱者は私です）。

Mathcomp ライブラリには、これらを解消するための補題
（ビューまたrewriteで使う）
が用意されてるわけですが、覚えることも、探すことも大変です。

そこで、もっとも簡単かかたちに変換するタクティクを作ってみました。
*)

(**
# コード例

タクティクスの定義に難しい点はありません。ゴール部と前提部に対して
繰り返しえ実行するようにしています。

Prop型の否定 ``~`` の出現にも対応してますが、
また、Ltac の定義のなかではコアーションが使えないため、
is_true を明示する必要があります。


``Definition is_true b := (b = true)``

でした。
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

(**
# 補足説明

Ltac の定義のなかで何をしているか見てみましょう。
以下の表だけで、便利につかえるかもしれせんね。


## 前提が...なら

| 前   | タクティク | 後 |

|:-------------------|:-----------------|:---------------|

| (a == b) = true    | なももしない      | a == b         |

| (a != b) = true    | なにもしない      | a != b         |

| (a == b) <> true   | move/negP        | a != b         |

| (a != b) <> true   | move/negP        | ~~ (a != b)    |

| (a == b) = false   | move/negbT       | a != b         |

| (a != b) = false   | move/negbT       | ~~ (a != b)    |

| (a == b) <> false  | move/negpF       | a == b         |

| (a != b) <> false  | move/negbF       | a != b         |

| ~ (a == b)         | move/negP        | a != b         |
                
| ~ (a != b)         | move/negP        | ~~ (a != b)    |

| (a == b) == true   | rewrite eqb_id   | a == b         |

| (a != b) == true   | rewrite eqb_id   | a != b         |

| (a == b) == false  | rewrite eqbF_n   | a != b         |

| (a != b) == false  | rewrite eqbF_n   | ~~ (a != b)    |

| ~~ ~~ (a == b)     | rewrite negbK    | a == b         |

| ~~ (a != b)        | rewrite negbK    | (a == b) = true |

 *)

(**
## ゴールが...なら

| 前   | タクティク | 後 |

|:-------------------|:-----------------|:---------------|
| (a == b) = true    | なにもしない      | a == b         |

| (a != b) = true    | なにもしない      | a != b         |

| (a == b) <> true   | apply/negP       | a != b         |

| (a != b) <> true   | apply/negP       | ~~ (a != b)    |

| (a == b) = false   | apply/negbTE     | a != b         |

| (a != b) = false   | apply/negbTE     | ~~ (a != b)    |

| (a == b) <> false  | apply/Bool.not_false_iff_true | a == b |

| (a != b) <> false  | apply/Bool.not_false_iff_true | a != b |

| ~ (a == b)         | apply/negP       | a != b         |
                
| ~ (a != b)         | apply/negP       | ~~ (a != b)    |

| (a == b) == true   | rewrite eqb_id   | a == b         |

| (a != b) == true   | rewrite eqb_id   | a != b         |

| (a == b) == false  | rewrite eqbF_n   | a != b         |

| (a != b) == false  | rewrite eqbF_n   | ~~ (a != b)    |

| ~~ ~~ (a == b)     | rewrite negbK    | a == b         |

| ~~ (a != b)        | rewrite negbK    | (a == b) = true |

*)


(**
# 実行例

以下に実行例を示します。

Standard Coqのように、ゴールはできるだけ前提に上げて（introして）
から、このタクティクを実行してください。

Mathcomp のタクティクのようにゴールのスタックトップに適用する、
というわけではありません。
*)

Section Negative.

  Goal forall (a b : nat), ~ (~~ ~~ (a == b) = false) -> (~~ (a == b)) <> true.
  Proof.
    move=> a b H1.
    find_neg.
    done.
  Qed.
  
(**
前提部 find_neg_hypo の単体のテスト
 *)

  Goal forall (a b : nat), (a == b) = true -> (a == b).
  Proof.
    move=> a b H1.
    find_neg_hypo.
    done.    
  Qed.

  Goal forall (a b : nat), (a == b) <> true -> (a != b).
  Proof.
    move=> a b H1.
    find_neg_hypo.
    done.    
  Qed.

  Goal forall (a b : nat), ~((a == b) = true) -> (a != b).
  Proof.
    move=> a b H1.
    find_neg_hypo.
    done.    
  Qed.
  
  Goal forall (a b : nat), (a == b) = false -> (a != b).
  Proof.
    move=> a b H1.
    find_neg_hypo.
    done.    
  Qed.
  
  Goal forall (a b : nat), (a == b) <> false -> (a == b).
  Proof.
    move=> a b H1.
    find_neg_hypo.
    done.    
  Qed.

  Goal forall (a b : nat), ~ ((a == b) = false) -> (a == b).
  Proof.
    move=> a b H1.
    find_neg_hypo.
    done.    
  Qed.

  Goal forall (a b : nat), ~ (a == b) -> (a != b).
  Proof.
    move=> a b H1.
    find_neg_hypo.
    done.    
  Qed.
  
  Goal forall (a b : nat), (a == b) == true -> (a == b).
  Proof.
    move=> a b H1.
    find_neg_hypo.
    done.
  Qed.

  Goal forall (a b : nat), (a == b) == false -> (a != b).
  Proof.
    move=> a b H1.
    find_neg_hypo.
    done.
  Qed.

  Goal forall (a b : nat), ~~ ~~ (a == b) -> (a == b).
  Proof.
    move=> a b H1.
    find_neg_hypo.
    done.
  Qed.
  
(**
ゴール部 find_neg_goal の単体のテスト
 *)

  Goal forall (a b : nat), (a == b) -> (a == b) = true.
  Proof.
    move=> a b H1.
    find_neg_goal.
    done.    
  Qed.

  Goal forall (a b : nat), (a != b) -> (a == b) <> true.
  Proof.
    move=> a b H1.
    find_neg_goal.
    done.    
  Qed.

  Goal forall (a b : nat), (a != b) -> ~((a == b) = true).
  Proof.
    move=> a b H1.
    find_neg_goal.
    done.    
  Qed.
  
  Goal forall (a b : nat), (a != b) -> (a == b) = false.
  Proof.
    move=> a b H1.
    find_neg_goal.
    done.    
  Qed.
  
  Goal forall (a b : nat), (a == b) -> (a == b) <> false.
  Proof.
    move=> a b H1.
    find_neg_goal.
    done.    
  Qed.

  Goal forall (a b : nat), (a == b) -> ~ ((a == b) = false).
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
  
  Goal forall (a b : nat), (a == b) -> (a == b) == true.
  Proof.
    move=> a b H1.
    find_neg_goal.
    done.
  Qed.

  Goal forall (a b : nat), (a != b) -> (a == b) == false.
  Proof.
    move=> a b H1.
    find_neg_goal.
    done.
  Qed.

  Goal forall (a b : nat), (a == b) -> ~~ ~~ (a == b).
  Proof.
    move=> a b H1.
    find_neg_goal.
    done.
  Qed.
  
End Negative.

(* END *)
