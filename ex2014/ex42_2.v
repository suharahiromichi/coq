(**
# 第9回 タクティックの定義と利用/停止性証明 (2014/06/08)

http://qnighy.github.io/coqex2014/

## 課題42 (種別:A / 締め切り : 2014/06/15)

自然数におけるlog関数(底は2)を以下のテンプレートに従って定義せよ。
テンプレートを改変しているので、このままで応募してはいけない。
*)

Require Import ssreflect ssrbool ssrnat div eqtype.
Require Import Recdef.

(*
Require Import Arith.
Require Import Omega.
Require Import Recdef.
*)

Require Import Lt.

(* http://gcg00467.xii.jp/wp/archives/891 *)
(* http://www.cse.chalmers.se/research/group/logic/TypesSS05/resources/coq/CoqArt/gen-rec/SRC/chap15.v *)
Theorem lt_Acc : forall n:nat, Acc lt n.
Proof.
 induction n.
 split; intros p H; inversion H.
 split. 
 intros y H0.
 case (le_lt_or_eq _ _ H0).
 intro; apply Acc_inv with n; auto with arith.
 intro e; injection e; intro e1; rewrite e1; assumption. 
Qed.

Function log (n:nat) {wf lt n} :=
  match n with
    | 0 => 0
    | 1 => 0
    | n => (log (n %/ 2)).+1
  end.
Proof.
  + move=> n2 n1 n Hn1 Hn2.
    rewrite -!Hn2.
    apply/leP.
    Search (_ %/ _ < _).
    apply ltn_Pdiv.
      - by [].
      - by rewrite Hn2.
  + rewrite /well_founded.
    by apply lt_Acc.
Qed.

(*
ヒント

Fixpointでは構造に基づく帰納法しか書けませんでした。Coqが自動的に停止性を判断できないような
関数の定義をするために、Functionコマンドが用意されています。停止性はwf (パラメーターのうち
の1つが整礎的な関係に従って降下していくことを示す) または measure (パラメーターのうちの1つ
に自然数の重みを定める関数があり、再帰呼び出しはこの重みが減る方向に進むということを示す)
の2つの方法があります。

*)

(* END *)
