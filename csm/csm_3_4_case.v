(**
ProofCafe 名古屋 補足資料

萩原学 アフェルト・レナルド 「Coq/SSReflect/MathCompによる定理証明」 森北出版

[http://www.morikita.co.jp/books/book/3287]

3.4 case タクティク で取り上げられていない case の便利な使い方も説明します。

@suharahiromichi

2019_07_20
*)

From mathcomp Require Import all_ssreflect.

(**
# 3.4 case タクティク
 *)

Section Test.

(**
## case の原理は Inductive な定義に基づく場合分けである。その場合分けは、0個以上である。
0個の場合分けは False だけである。しかし、1個の場合分けは頻出する。
ここでは、1個のコンストラクタによる場合分けを「展開」と呼ぶ。
*)

Inductive Test :=
| one
| two
| tree
| four.

Goal forall a : Test, (a = one) \/ (a = two) \/ (a = tree) \/ (a = four).
Proof.
  case.
  - by left.                                (* a = one *)
  - by right; left.                         (* a = two *)
  - by right; right; left.                  (* a = tree *)
  - by right; right; right.                 (* a = four *)
Qed.

(** apply/ を使ってまとめて書く書き方。3.16 参照 *)
Goal forall a : Test, (a = one) \/ (a = two) \/ (a = tree) \/ (a = four).
Proof.
  case.
  - by apply/or_introl.                     (* a = one *)
  - by apply/or_intror/or_introl.           (* a = two *)
  - by apply/or_intror/or_intror/or_introl. (* a = tree *)
  - by apply/or_intror/or_intror/or_intror. (* a = four *)
Qed.

End Test.

(**
## 3.4.1 bool
 *)
Print bool.
(* Inductive bool : Set :=  true : bool | false : bool *)

Goal forall b1, forall b2, forall b3,
        b1 && (b3 || b2) = b1 && b3 || b1 && b2.
Proof.
  Print bool.                     (* true と false による場合分け。 *)
  case.                           (* move=> b1. case H : b1. *)
  (**
     subgoal 1 is: forall b2 b3 : bool, true && (b3 || b2) = true && b3 || true && b2
   *)
  - done.
  (**
    subgoal 2 is: forall b2 b3 : bool, false && (b3 || b2) = false && b3 || false && b2
   *)
  - done.
Qed.

(** 同じ命題をPropで定義した場合。次節以降を参照してください。  *)

Goal forall P1, forall P2, forall P3,
        P1 /\ (P3 \/ P2) <-> P1 /\ P3 \/ P1 /\ P2.
Proof.
  move=> P1 P2 P3.
  split.
  - case=> HP1 [HP3 | HP2].
    + left.
        by split.
    + right.
        by split.
  - case=> [[H1 H3] | [H1 H3]].
    + split=> //.
        by left.
    + split=> //.
        by right.
Qed.

Section Case1.

Variable P Q : Prop.

(**
## 3.4.2 or
 *)
Goal P \/ Q -> Q \/ P.
Proof.
  Print or.                  (* or_introl と or_intror の場合分け。 *)
  (* 
     Inductive or (A B : Prop) : Prop :=
     | or_introl : A -> A \/ B
     | or_intror : B -> A \/ B.
   *)
  
  (* ふたつでしか場合分けできないことに注意！ *)
  case.
  (**
     subgoal 1 is: P -> Q \/ P
   *)
  - move=> HP. by right.
    
  (**
    subgoal 2 is: Q -> Q \/ P
   *)
  - move=> HQ. by left.
Qed.

(**
## 3.4.3 and
 *)
Goal P /\ Q -> Q /\ P.
Proof.
  Print and.              (* 唯一のコンストラクタ conj を展開する。 *)
  (* 
     Inductive and (A B : Prop) : Prop :=
     conj : A -> B -> A /\ B.
   *)
  
  case.
  (**
     goal is: P -> Q -> Q /\ P
   *)
  move=> HP HQ.
  split.                                    (* apply: conj *)
  - done.
  - done.
Qed.

(**
## 3.4.4 True
 *)
Goal True -> P -> P.
Proof.
  Print True.             (* 唯一のコンストラクタ I を展開する。 *)
  (* 
     Inductive True : Prop :=
     I : True.
   *)
  
  case.
  (**
     goal is: P -> P
   *)
  done.
Qed.

(**
## 3.4.5 False
 *)
Goal False -> P.
Proof.
  Print False.                              (* 0個のコンストラクタ *)
  (**
     Inductive False : Prop :=  .           (* := の右辺が空 *)
   *)
  case.
  (**
     goal is: none
   *)
Qed.

End Case1.

(**
## 3.4.6 ex
*)
Section Case2.
  
Variable A : Type.
Variable P : A -> Prop.

Goal (exists a, P a) -> ~ (forall a, ~ P a).
Proof.
  Print ex.           (* 唯一のコンストラクタ ex_intro を展開する。 *)
  (*
  Inductive ex (A : Type) (P : A -> Prop) : Prop :=
  | ex_intro : forall x : A, P x -> exists y, P y
   *)
  
  case.
  (**
     goal is: forall x : A, P x -> ~ (forall a : A, ~ P a)
   *)
  move=> x HP Hc.
  apply: (Hc x).
  done.
Qed.

End Case2.

(**
## 3.4.7 nat
 *)
Goal forall n : nat, n + 1 = 1 + n.
Proof.
  Print nat.                             (* O と S で場合分けする。 *)
  (* 再帰的に定義された型については、elimを使うべき。帰納法の仮定を残してくれるから。 *)
  (* 再帰的でない型については、elimとcaseは同じになる。 *)
  case.
  (**
     subgoal 1 is: 0 + 1 = 1 + 0
   *)
  (**
     subboal 2 is: forall n : nat, n.+1 + 1 = 1 + n.+1
   *)
Admitted.                                 (* これは使わないだろう。 *)

(**
## 3.4.x （追加） if
 *)
Section Case3.

Variable n : nat.

(** bool の場合を同じだが、場合を前提として覚えておく。 *)
Goal if n == 42 then true else true.
Proof.
  (* (n == 42) = true と (n == 42) = false で場合分けする。 *)
  case H : (n == 42).                       (* 括弧を忘れない。 *)
  (**
     H : (n == 42) = true
     subgial 1 is: true
   *)
  - done.
  (**
     H : (n == 42) = false
     subgial 2 is: true
   *)
  - done.
Qed.

(** おまけ。前提の偽を証明することが多い。 *)
Goal if 0 <= n then true else false.
Proof.
  case H : (0 <= n).
  (** subgoal 1 is: 0 <= n -> true *)
  - done.
  (** subgoal 2 is: (0 <= n) = false -> false *)
  - move/negbT in H.
    move/negP in H.
    done.
Qed.

(** 補題ifPを使う。知らないと使えない例 *)
Goal if n == 42 then true else true.
Proof.
  Check @ifP bool (n == 42) true true
  : if_spec (n == 42) true true ((n == 42) = false) (n == 42)
            (if n == 42 then true else true).
  Print if_spec.      (* IfSpecTrue と IfSpecFalse で場合分けする。 *)
  
  case: ifP.
  (**
     subgoal 1 is: (n == 42) = true -> true
   *)
  - done.
  (**
     subgoal 2 is: (n == 42) = false -> true
   *)
  - done.
Qed.

(** 補題eqPを使う。知らないと使えない例 *)
Goal if n == 42 then true else true.
Proof.
  Check @eqP nat_eqType n 42 : reflect (n = 42) (n == 42).
  Print Bool.reflect.      (* ReflectT と ReflectF で場合分けする。 *)
  
  case: eqP.
  (**
     subgoal 1 is: (n = 42) -> true
   *)
  - done.
  (**
     subgoal 2 is: (n <> 42) -> true
   *)
  - done.
Qed.

(*
Set Printing All.
*)

(**
## 3.4.x （追加） let
*)
Goal let: (x, y) := (n, n) in x = y.
(* Goal match (n, n) with (x, y) => x = y end. *)
Proof.
  (**
     let を展開するにも、case を使う。
   *)
  case H : (n, n).
  
  (**
     直積型 prod も、Inductiveで定義されているので、caseで展開できる。
   *)
  Print prod.                          (* 唯一のコンストラクタ pair を展開する。 *)
  case: H => H1 H2.
  rewrite -H1 -H2.
  done.
Qed.

(* let: は letに変換 または 直接書き換えする。 ??? *)
(* let は match の場合分けが唯一の場合。match と case の関係を調べること。 *)
(* match の場合分けができるわけではない。 *)
Goal match (n, n) with (0, 0) => 1 | (1, 1) => 2 | _ => 0 end == 1.
Proof.
  case H : (n, n).
  case: H => H1 H2.
  rewrite -H1 -H2.
Admitted.

End Case3.

Section Case4.

Variable P Q : Prop.

(**
## 3.4.x case=> [H1 H2]
*)
Goal P /\ Q -> Q /\ P.
Proof.
  case=> HP HQ.
  (* case. move=> HP HQ. と同じ。これだけ原則とおり。 *)
  (* case=> [HP HQ] でもよい。 *)
  (* move=> [HP HQ] でもよい。 *) 
  split.
  - done.
  - done.
Qed.

Goal P /\ Q -> Q /\ P.
Proof.
  move=> [HP HQ].
  split.
  - done.
  - done.
Qed.

(**
## 3.4.8 case=> [H1 | H2]
*)
Goal P \/ Q -> Q \/ P.
Proof.
  case=> [HP | HQ].
  - by right.
  - by left.
Qed.

Goal P \/ Q -> Q \/ P.
Proof.
  move=> [HP | HQ].
  - by right.
  - by left.
Qed.

(** 複雑なネストも可能である。 *)
Variable P1 P2 Q1 Q2 Q3 R1 R2 : Prop.

(** P /\ Q /\ R は P /\ (Q /\ R) であることに注意！  *)
Goal P1 /\ Q1 /\ R1 -> True.
Proof.
  case=> [HP1 [HQ2 HR3]].
  done.
Qed.

Goal (P1 /\ P2) /\ (Q1 /\ (Q2 \/ Q3)) /\ (R1 \/ R2) -> True.
Proof.
  case=> [[HP1 HP2] [[HQ1 [HQ2 | HQ3]] [HR1 | HR2]]].
  - done.
  - done.
  - done.
  - done.
Qed.

End Case4.

(* END *)
