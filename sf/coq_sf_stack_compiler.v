(** ソフトウエアの基礎 Benjamin C. Pierceさん他、梅村さん他訳
   Imp_J : 単純な命令型プログラム より抜粋
 *)
(** 練習問題の回答例
   @suharahiromichi
 *)

(** HP の電卓、Forth や Postscript などのプログラミング言語の
stack_compilerが正しく動作することの証明
*)

(* 本ファイル単独で動作することを確認しています。*)
Require Export SfLib_J.

(** 状態(state)はプログラムの実行のある時点のすべての変数の現在値を表します。
 *)
Definition state := id -> nat.

Definition empty_state : state :=
  fun _ => 0.

Definition update (st : state) (X:id) (n : nat) : state :=
  fun X' => if beq_id X X' then n else st X'.

Inductive aexp : Type :=
  | ANum : nat -> aexp
  | AId : id -> aexp
  | APlus : aexp -> aexp -> aexp
  | AMinus : aexp -> aexp -> aexp
  | AMult : aexp -> aexp -> aexp.

Tactic Notation "aexp_cases" tactic(first) ident(c) :=
  first;
  [ Case_aux c "ANum" | Case_aux c "AId" | Case_aux c "APlus"
  | Case_aux c "AMinus" | Case_aux c "AMult" ].

(** 変数の略記法: *)
Definition X : id := Id 0.
Definition Y : id := Id 1.
Definition Z : id := Id 2.

(** HP の電卓、Forth や Postscript などのプログラミング言語
 *)
(**
  スタック言語の命令セットは、以下の命令から構成されます:
     - [SPush n]: 数 [n] をスタックにプッシュする。
     - [SLoad X]: ストアから識別子 [X] に対応する値を読み込み、スタックにプッシュする。
     - [SPlus]:   スタックの先頭の 2 つの数をポップし、それらを足して、
                  結果をスタックにプッシュする。
     - [SMinus]:  上と同様。ただし引く。
     - [SMult]:   上と同様。ただし掛ける。
*)

Inductive sinstr : Type :=
| SPush : nat -> sinstr
| SLoad : id -> sinstr
| SPlus : sinstr
| SMinus : sinstr
| SMult : sinstr.

Fixpoint aeval (st : state) (e : aexp) : nat :=
  match e with
  | ANum n => n
  | AId X => st X
  | APlus a1 a2 => (aeval st a1) + (aeval st a2)
  | AMinus a1 a2  => (aeval st a1) - (aeval st a2)
  | AMult a1 a2 => (aeval st a1) * (aeval st a2)
  end.

(** スタック言語のプログラムを評価するための関数を書く。
 *)
Fixpoint s_exec (st : state) (ins : sinstr) (stack : list nat) : list nat :=
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
(* 補足：stack(overflow)の判定を前に出すと、証明が立ち行かなくなる。
また、stack overflow時の処理を無視することで、s_compile_correct_app の証明が簡単になっている、
と思う。*)

Fixpoint s_execute (st : state) (stack : list nat) (prog : list sinstr) : list nat :=
  match prog with
    | [] =>
      stack
    | ins :: prog' =>
      s_execute st (s_exec st ins stack) prog'
  end.

(** [aexp] をスタック機械のプログラムにコンパイルする関数を書く。
 *)
Fixpoint s_compile (e : aexp) : list sinstr :=
  match e with
    | ANum n => [SPush n]
    | AId id => [SLoad id]
    | APlus a b =>  (s_compile a) ++ (s_compile b) ++ [SPlus]
    | AMinus a b => (s_compile a) ++ (s_compile b) ++ [SMinus]
    | AMult a b =>  (s_compile a) ++ (s_compile b) ++ [SMult]
  end.

(** [compile] 関数が正しく振る舞うことを述べている定理を証明する。
 *)
(* 補助定理として、スタック言語の命令列がappendできることを証明する。 *)
Lemma s_compile_correct_app : forall (st : state)
  (stack1 stack2 stack3: list nat)
  (prog1 prog2 : list sinstr),
  s_execute st stack1 prog1 = stack2 -> 
  s_execute st stack2 prog2 = stack3 -> 
  s_execute st stack1 (prog1 ++ prog2) = stack3.
Proof.
  intros st stack1 stack2 stack3 prog1.
  generalize dependent stack1.
  generalize dependent stack2.
  generalize dependent stack3.
  induction prog1 as [| a prog1'].
  Case "prog1 = []".
    intros. rewrite app_nil_l. simpl in H. subst. reflexivity.
  Case "prog1 = a :: prog1'".
    intros. destruct a;
      (simpl; apply IHprog1' with (stack2 := stack2); assumption).
Qed.

(* より一般的な、stackが任意の状態の場合について、証明する。 *)
Lemma s_compile_correct_stack : forall (st : state) (stack : list nat) (e : aexp),
  s_execute st stack (s_compile e) = [ aeval st e ] ++ stack.
Proof.
  intros st stack e.
  generalize stack as stack0.               (* ここが肝 *)
  aexp_cases (induction e) Case;
    try reflexivity;                        (* ANum, AId *)
    try (intros st0; simpl;                 (* APlus, AMinus, AMult *)
     apply s_compile_correct_app with (stack2 := aeval st e1 :: st0);
     [rewrite IHe1; reflexivity |
      apply s_compile_correct_app with (stack2 := aeval st e2 :: aeval st e1 :: st0);
        [rewrite (IHe2 (aeval st e1 :: st0)); reflexivity | (* generalizeが役立つ *)
         reflexivity]]).
Qed.

(* stackが初期状態（空[]）の場合について、証明する。 *)
Theorem s_compile_correct : forall (st : state) (e : aexp),
  s_execute st [] (s_compile e) = [ aeval st e ].
Proof.
  intros st e.
  apply s_compile_correct_stack.
Qed.

(* end *)
