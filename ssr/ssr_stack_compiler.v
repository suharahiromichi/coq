(**
スタックコンパイラの証明
========
@suharahiromichi

2014_04_30
 *)
Require Import ssreflect ssrbool ssrnat seq eqtype ssrfun.
(**
スタック言語のための stack compiler が正しく動作することの証明をする。
*)
(**
状態(state)はプログラムの実行のある時点のすべての変数の現在値を表す。
 *)
Inductive id : Type := 
  Id of nat.

Definition state := id -> nat.

(**
ソースコードにあたる算術式 [aexp] を定義する。
 *)
Inductive aexp : Type :=
| ANum of nat
| AId of id
| APlus of aexp & aexp
| AMinus of aexp & aexp
| AMult of aexp & aexp.

(**
変数の略記法:
 *)
Definition X : id := Id 0.
Definition Y : id := Id 1.
Definition Z : id := Id 2.

(**
スタック指向のプログラミング言語
 *)
(**
スタック言語の命令セットは、以下の命令から構成される:

- [SPush n]: 数 [n] をスタックにプッシュする。
- [SLoad X]: ストアから識別子 [X] に対応する値を読み込み、スタックにプッシュする。
- [SPlus]:   スタックの先頭の 2 つの数をポップし、それらを足して、結果をスタックにプッシュする。
- [SMinus]:  上と同様。ただし引く。
- [SMult]:   上と同様。ただし掛ける。
*)

Inductive sinstr : Type :=
| SPush of nat
| SLoad of id
| SPlus
| SMinus
| SMult.

Fixpoint aeval (st : state) (e : aexp) : nat :=
  match e with
  | ANum n => n
  | AId X => st X
  | APlus a1 a2 => (aeval st a1) + (aeval st a2)
  | AMinus a1 a2 => (aeval st a1) - (aeval st a2)
  | AMult a1 a2 => (aeval st a1) * (aeval st a2)
  end.

(**
スタック言語のプログラムを評価するための関数を書く。
 *)
Fixpoint s_exec (st : state) (ins : sinstr) (stack : seq nat) : seq nat :=
  match ins with
    | SPush n =>  n :: stack
    | SLoad idx => (st idx) :: stack
    | SPlus => match stack with
                 | b :: a :: stack' => (a + b) :: stack'
                 | _ => stack
               end
    | SMinus => match stack with
                 | b :: a :: stack' => (a - b) :: stack'
                 | _ => stack
               end
    | SMult => match stack with
                 | b :: a :: stack' => (a * b) :: stack'
                 | _ => stack
               end
  end.
(**
補足：stack underflow の判定をまとめて前に出すと、証明がたいへんになるだろう。
また、そのときの例外処理を行わないが、それによって、s_compile_correct_app 
の証明が簡単になっていると思う。
 *)

Fixpoint s_execute (st : state) (stack : seq nat) (prog : seq sinstr) : seq nat :=
  match prog with
    | [::] =>
      stack
    | ins :: prog' =>
      s_execute st (s_exec st ins stack) prog'
  end.

(**
[aexp] をスタック機械のプログラムにコンパイルする関数を書く。
 *)
Fixpoint s_compile (e : aexp) : seq sinstr :=
  match e with
    | ANum n => [:: SPush n]
    | AId id => [:: SLoad id]
    | APlus a b =>  (s_compile a) ++ (s_compile b) ++ [:: SPlus]
    | AMinus a b => (s_compile a) ++ (s_compile b) ++ [:: SMinus]
    | AMult a b =>  (s_compile a) ++ (s_compile b) ++ [:: SMult]
  end.

(**
[compile] 関数が正しく振る舞うことを述べている定理を証明する。
 *)
(**
補題として、スタック言語の命令列が append できることを証明する。
 *)
Lemma s_compile_correct_app : forall (st : state)
  (stack1 stack2 stack3: seq nat)
  (prog1 prog2 : seq sinstr),
  s_execute st stack1 prog1 = stack2 -> 
  s_execute st stack2 prog2 = stack3 -> 
  s_execute st stack1 (prog1 ++ prog2) = stack3.
Proof.
  move=> st stack1 stack2 stack3 prog1.
  elim: prog1 stack1 stack2 stack3.
    by move=> stack1 stack2 stack3 prog2; rewrite cat0s; move=> <- <-.
  move=> a prog1' IHprog1' stack1 stack2 stack3.
  elim: a;
    by move=> ?; apply IHprog1' with (stack2 := stack2).
Qed.

(**
より一般的な、stackが任意の状態の場合について証明する。
 *)
Lemma s_compile_correct_stack : forall (st : state) (stack : seq nat) (e : aexp),
  s_execute st stack (s_compile e) = [:: aeval st e] ++ stack.
Proof.
  move=> st stack e.
  elim: e stack;                            (* 「stack」をpushするのが肝。 *)
    (* ANum, AId の場合 *)
    try by [];
  (* APlus, AMinus, AMult の場合 *)
  try move=> e1 IHe1 e2 IHe2 st0;
    apply s_compile_correct_app with (stack2 := aeval st e1 :: st0);
    by [rewrite IHe1 |
       apply s_compile_correct_app with (stack2 := aeval st e2 :: aeval st e1 :: st0);
            [rewrite (IHe2 (aeval st e1 :: st0)) |]].
Qed.

(**
最後に、stackが初期状態（空[]）の場合について証明する。
 *)
Theorem s_compile_correct : forall (st : state) (e : aexp),
  s_execute st [::] (s_compile e) = [:: aeval st e ].
Proof.
  intros st e.
  apply s_compile_correct_stack.
Qed.

(* END *)
