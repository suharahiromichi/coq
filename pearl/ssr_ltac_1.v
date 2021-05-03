(**
MathComp の「等号問題」を解決する
======
2019/05/06
2019/08/12 Prop型の等式 /eqP について追記した。


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
これに対して、MathComp は、``a != b``  が ``~~ (a == b)`` 
であるのはともかくとして、``(a != b) <> false`` 
もあれば、``~~ (a != b) = false`` も可能という具合に、
百花繚乱の状態です。二重否定も普通に出現することも事態を複雑にします。


このことは MathComp の「等号問題」と呼ばれています（提唱者は私です）。

なお、ここでの「等号」は、「EQUAL」と「NOT EQUAL」の両方を指しています。


MathComp ライブラリには、これらを解消するための補題
が用意されてるわけですが、覚えるのも探すことも大変です。
そこで、もっとも簡単な ``==`` や ``!=`` の式に自動的に変換するタクティクを作ってみました。


（補足）

演算子 ``<=`` や ``<`` の定義は、Standard Coq とMathComp で異なりますが、
演算子 ``=`` と ``<>`` の定義は、Standard Coq とMathComp で同じです。
今回は、大小（順序）関係を表す``<=`` や ``<``の不等式については扱いません。

（補足終）
*)

(**
# コード例

タクティクスの定義に難しい点はありません。ゴール部と前提部のそれぞれに対して
繰り返して実行するようにしています。

Prop型の否定 ``~`` の出現にも対応してますが、
Ltac の定義のなかではコアーションが使えないため、
is_true を明示する必要があります。


``Definition is_true b := (b = true)``

でした。

また、``_ != true`` が出現しないのは、``~~ (_ == true)`` とおなじなので、
括弧の中身がコンテキストにマッチして、
処理されるからです。``_ != false`` も同様です。
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
# 詳細説明

Ltac の定義のなかで何をしているか見てみましょう。
この表だけで便利につかえるかもしれせんね。


これらのタクティクをできるだけ繰り返して、もっとも簡単なかたちにします。
一般に、``a != b`` に ``move/negP`` を
repeat で繰り返し適用すると、``a != b`` と ``~ (a == b)`` の間を
限りなく往復して終了しません。
ここでは、条件を適切にすることでそれを回避しています。

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

| (a == b) == false  | rewrite eqbF_neg | a != b         |

| (a != b) == false  | rewrite eqbF_neg | ~~ (a != b)    |

| ~~ ~~ (a == b)     | rewrite negbK    | a == b         |

| ~~ (a != b)        | rewrite negbK    | a == b        |

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

| (a == b) == false  | rewrite eqbF_neg | a != b         |

| (a != b) == false  | rewrite eqbF_neg | ~~ (a != b)    |

| ~~ ~~ (a == b)     | rewrite negbK    | a == b         |

| ~~ (a != b)        | rewrite negbK    | a == b         |

*)

(**
# Prop型の等式について

/eqP は bool型の等式をProp型の等式(Leibnizの等式)に変換するので、
Prop型が与えられた場合は必ずこれを使います。

一方、Prop型が欲しいときは、
find_neg を実行したあとに、別途、``move/eq`` または ``apply/eqP`` 
を実行することになります。

``_ = false`` にも対応ていて、二重否定の除去もおこなわれるので、
find_neg が不要の場合もあります（参考：elimTF または introTF が補完されるため）。

次の表を参考に使ってください。
 *)

(**
## 前提が...なら

| 前   | タクティク | 後 |

|:-------------------|:----------------|:---------------|

| a = b              | move/eqP        | a == b         |

| a <> b             | move/eqP        | a != b         |

| a == b             | move/eqP        | a = b          |

| a != b             | move/eqP        | a <> b         |

| (a == b) = false   | move/eqP        | a <> b         |

| (a != b) = false   | move/eqP        | a = b          |

 *)

(**
## ゴールが...なら

| 前   | タクティク | 後 |

|:-------------------|:-----------------|:---------------|

| a = b              | apply/eqP        | a == b         |

| a <> b             | apply/eqP        | a != b         |

| a == b             | apply/eqP        | a = b          |

| a != b             | apply/eqP        | a <> b         |

| (a == b) = false   | apply/eqP        | a <> b         |

| (a != b) = false   | apply/eqP        | a = b          |

 *)



(**
# 実行例

以下に実行例を示します。

Standard Coqのように、ゴール（のスタック）は
できるだけコンテキストに上げて（introして）から、
このタクティクを実行してください。

MathComp のタクティクのようにゴールのスタックトップに適用する、
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
# おまけ・テストコード
 *)
  
(**
## 前提部 find_neg_hypo の単体のテスト
 *)
  
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
