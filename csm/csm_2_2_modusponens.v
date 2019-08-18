From mathcomp Require Import all_ssreflect.
(* mathcomp/ssreflect 一式をインポートする。おすすめ。 *)

  (**

## 論理ゲーム(1)

### goalsウィンドウの説明

  X, Y : Prop
  XtoY_is_true : X -> Y
  X_is_true : X
  ============================
  Y

===== の上がコンテキストで、変数の型や、前提である名前のついた命題があります。

===== の下がゴールで、一般に A->B->C のかたちです。
最も外側の->の左(A)をスタックトップといいます。
->は右結合なので、A->(B->C)であることに注意してください。
ゴールが(A->B)->Cなら、(A->B)がスタックトップです。


### 証明の終わり（ゴールの解消）

前提のどれかとゴールとが同じになったら。または、
ゴールが A->A になったら

done

で証明は終了する。by [] でもおなじ。



### intro、generaralize、apply

- move          これ自体はなにもしない。
- move=> H      スタックトップを前提H 移す。「=>」の機能。intro とも。
- move: H       前提Hをスタックトップに移す。「:」の機能。generaralize とも。

- apply         スタックトップをゴールの残りの部分に適用する。単独ではあまり使わない。
- apply: H      前提 H をゴールに適用する。move: H; apply の意味。

  move: H1; apply; move=> H2 は、apply: H1 => H2 とかける。


### 適用について

- ゴールへの適用
ゴールが Y のとき、 前提 H: X->Y を適用して X を得る。
例： apply: H

- 前提への適用
前提 H1 : X->Y、前提 H2 : X のとき、(H1 H2) は Y である。関数の書き方と同じ。
例： move: (H1 H2)   (H1 H2) の結果をスタックトップに移す。
     move: H1 H2 とは異なる。括弧が必要。



両者の違いは、同じ証明図を下から上のみるか、上から下にみるかの違いによる。

  X     X -> Y
---------------
             Y


### Section セクション

Section のなかの宣言は、Section から出ると、

- Variable X : Prop は、forall (X : Prop), 。。。。
- Hypothesis H : X は、 X -> 。。。。 

Section の中では、最初から intro されているといえる。
   *)

Section ModusPonens.

  Variable X Y : Prop.

  Hypothesis XtoY_is_true : X -> Y.
  Hypothesis X_is_true : X.
  
  (* Goal を X -> Y にする例。 *)
  
  Theorem MP : Y.
  Proof.
    move: X_is_true.
      by [].                                (* done *)
  Qed.

  (* Goal を X にする例。 *)
  
  Theorem MP2 : Y.
  Proof.
    move: XtoY_is_true.
    apply.
      by [].                                (* done *)
  Qed.
  
  (* 一行にまとめられる。 *)
  Theorem MP2' : Y.
  Proof.
    apply: XtoY_is_true.
      by [].                                (* done *)
  Qed.
  
  (* 前提に適用する例。 *)
  Theorem MP3 : Y.
  Proof.
    move: (XtoY_is_true X_is_true).         (* 括弧を忘れないこと。 *)
    move=> Y_is_true.
      by [].                                (* done *)
  Qed.
  
  (* おまけ *)
  Theorem MP2'': Y.
  Proof.
    debug auto.
    (* 
Debug: (* debug auto: *)
Debug: * assumption. (*fail*)
Debug: * intro. (*fail*)
Debug: * simple apply XtoY_is_true. (*success*)
Debug: ** assumption. (*success*)
     *)
  Qed.
  
  Check MP : Y.
  Check MP2 : Y.
  Check MP2' : Y.
  Check MP3 : Y.
  Check MP2'' : Y.
  
End ModusPonens.

(* セクションから出ると。 *)
Check MP : forall X Y : Prop, (X -> Y) -> X -> Y.
Check MP2 : forall X Y : Prop, (X -> Y) -> X -> Y.
Check MP2' : forall X Y : Prop, (X -> Y) -> X -> Y.
Check MP3 : forall X Y : Prop, (X -> Y) -> X -> Y.
Check MP2'' : forall X Y : Prop, (X -> Y) -> X -> Y.

(* END *)
