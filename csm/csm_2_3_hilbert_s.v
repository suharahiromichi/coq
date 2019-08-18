From mathcomp Require Import all_ssreflect.

(* ここでは ModusPonens は使いません。 *)

  (**

## 論理ゲーム(2)

前提 HABC : A -> B -> C のとき、あるいは、ゴールのスタックトップが A -> B -> C のとき。

### ゴールへの適用

ゴール C に適用すると、ふたつのサブゴール A と B に分岐する。

これに対して、H : (A -> B) -> C を ゴール C に適用すると、ゴールは A -> B になる。


### 前提への適用

HA : A
HB : B
HABC : A -> B -> C

HABC HA : B -> C
HABC HA HB : C


証明図はどちらも同じ。

サブ2   サブ1
-----  ------  
          A   A -> B -> C
       -------------------
  B                B -> C
--------------------------
                        C

### まとめて intro、generaralize 

- move=> H1 H2 スタックトップを前提H1、H2に移す。intro とも。
- move: H1 H2 前提H1、H2をスタックトップに移す。generaralize とも。
- apply スタックトップをゴールの残りの部分に適用する。

- move: H2; move: H1; move; move=> H1; move=> H2 は、move: H1 H2 => H1 H2 とかける。


### 適用について (その2)

- apply/H ゴール全体への適用、ビュー付き。
- move/H スタックトップへの適用、ビュー付き。
   *)

Section HilbertSAxiom.

  Variables A B C : Prop.
  
  (* 前提への適用を使う例 *)
  
  (* A->B->C -> A->B->C を求める例 *)
  
  Theorem HS3 : (A -> B -> C) -> (A -> B) -> A -> C.
  Proof.
    move=> AtoBtoC_is_true.
    move=> AtoB_is_true.
    move=> A_is_true.
    move: (AtoB_is_true A_is_true).        (* スタックに B を積む。 *)
    move: A_is_true.                       (* スタックに A を積む。 *)
      by [].                               (* Goal A -> B -> C *)
      
    Undo 3.
      by move: A_is_true (AtoB_is_true A_is_true).
      
    Undo 1.
    move: (A_is_true).     (* スタックに Aを積む。 *)
    move/AtoB_is_true.     (* スタックに B : AtoB_is_true A_is_true *)
    move: A_is_true.       (* スタックに Aを積む。 *)
      by [].
  Qed.
  
  (* C -> C を求める例 *)

  Theorem HS3' : (A -> B -> C) -> (A -> B) -> A -> C.      
  Proof.
    move=> AtoBtoC_is_true.
    move=> AtoB_is_true.
    move=> A_is_true.
      by move: (AtoBtoC_is_true A_is_true (AtoB_is_true A_is_true)).
  Qed.
  
  (* ゴールへの適用を使う例 *)
  
  Theorem HS4 : (A -> B -> C) -> (A -> B) -> A -> C.
  Proof.
    (* 前提の「->」の右と、Goalが一致するまで intros する。 *)
    move=> AtoBtoC_is_true.
    move=> AtoB_is_true.
    move=> A_is_true.
    
    (* Goal : C *)
    apply: AtoBtoC_is_true. (* 「->」の右とGoalが一致した前提を apply する。 *)
    
    (* ふたつのサブゴールに分岐する。 *)
    (* Goal : A *)
    - by [].               (* Goalと前提が一致なので done *)
      
    (* Goal : B *)
    - apply: AtoB_is_true. (* 「->」の右とGoalが一致した前提を apply する。 *)
      
        (* Goal : A *)
        by [].             (* Goalと前提が一致なので done *)
  Qed.
  
  (* じつは auto タクティクの動作とおなじ。導出原理という自動証明の技法。 *)
  (* CPDT の Chapter 12 論理プログラミングによる証明探索 を参照してください。 *)
  
  Theorem HS5 : (A -> B -> C) -> (A -> B) -> A -> C.
  Proof.
    debug auto.
    (* 
Debug: (* debug auto: *)
Debug: * assumption. (*fail*)
Debug: * intro. (*success*)
Debug: * assumption. (*fail*)
Debug: * intro. (*success*)
Debug: * assumption. (*fail*)
Debug: * intro. (*success*)
Debug: * assumption. (*fail*)
Debug: * intro. (*fail*)
Debug: * simple apply H. (*success*)
Debug: ** assumption. (*success*)
Debug: ** assumption. (*fail*)
Debug: ** intro. (*fail*)
Debug: ** simple apply H0. (*success*)
Debug: *** assumption. (*success*)
     *)

    Restart.
    intro H.
    intro H0.
    intro H1.
    apply H.
    assumption.
    apply H0.
    assumption.
  Qed.
  
  Theorem HS : (A -> B -> C) -> (A -> B) -> A -> C.
  Proof.
    move=> AtoBtoC_is_true AtoB_is_true A_is_true.
      by apply: AtoBtoC_is_true;  [ | apply: AtoB_is_true].
  Qed.
  
End HilbertSAxiom.

(* END *)
