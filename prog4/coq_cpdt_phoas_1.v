(**
-http://adam.chlipala.net/cpdt/
CPDT の 17.2 章の PHOAS の解説のうち、termDenote と ident の関数を抜き出す。

- https://qiita.com/mrkbc/items/89b034dadc69df2ad274
PHOASでshift/resetのCPS変換 in Rocq(旧Coq)
の前半部分、ホスト言語の説明の箇所とほぼ同じ。
 *)

Require Import FunctionalExtensionality List. (* ext *)
Require Import Coq.Program.Equality.        (* dep_destruct E *)

Set Implicit Arguments.
Set Asymmetric Patterns.

Ltac ext := let x := fresh "x" in extensionality x.

Ltac dep_destruct E :=
  let x := fresh "x" in
  remember E as x; simpl in x; dependent destruction x;
  try match goal with
    | [ H : _ = E |- _ ] => try rewrite <- H in *; clear H
    end.

(** * 型の定義 *)

Inductive type : Type :=
| Nat : type
| Func : type -> type -> type.

(** 型を考える。  *)
Check Func Nat.
Check Func Nat Nat.

Fixpoint typeDenote (t : type) : Type :=
  match t with
  | Nat => nat
  | Func t1 t2 => typeDenote t1 -> typeDenote t2
  end.

(** 先の型をCoqの型に変換する。 *)
Compute typeDenote Nat.                     (* nat *)
Compute typeDenote (Func Nat Nat).          (* nat -> nat *)


(** * 17.2 Parametric Higher-Order Abstract Syntax *)

Module HigherOrder.

  Section var.
    Variable var : type -> Type.

    Inductive term : type -> Type :=
    | Var : forall t, var t -> term t
    | Const : nat -> term Nat
    | Plus : term Nat -> term Nat -> term Nat
    | Abs : forall dom ran, (var dom -> term ran) -> term (Func dom ran)
    | App : forall dom ran, term (Func dom ran) -> term dom -> term ran
    | Let : forall t1 t2, term t1 -> (var t1 -> term t2) -> term t2.
  End var.

  Arguments Var [var t] _.
  Arguments Const [var] _.
  Arguments Abs [var dom ran] _.

  Definition Term (t : type) := forall (var : type -> Type), term var t.
  
  (** 最初に ``Term t`` 型を考える。 *)
  Check Term Nat.                         (** これは、次に等しい。  *)
  Check forall var, term var Nat.
  
  Check Term (Func Nat Nat).              (** これは、次に等しい。  *)
  Check forall var, term var (Func Nat Nat).
  
  (** この型を持つ値として、以下がある。 *)
  Check (fun var => Const 1) : Term Nat.
  Check (fun var => Abs (fun x : var Nat => Var x)) : Term (Func Nat Nat).
  Check (fun var => (App (Abs (fun x : var Nat => Var x)) (Const 1))) : Term Nat.
  (** 省略を補う。  *)
  Check (fun var : type -> Type => @Const var 1) : Term Nat.
  Check (fun var : type -> Type => @Abs var Nat Nat (fun x : var Nat => @Var var Nat x))
    : Term (Func Nat Nat).
  Check (fun var : type -> Type => @App var Nat Nat
                                     (@Abs var Nat Nat (fun x : var Nat => @Var var Nat x))
                                     (@Const var 1))
    : Term Nat.
  
  (** ** 17.2.1 Functional Programming with PHOAS *)

  (** *** termDenote 表示的意味論を与える関数 *)
  
  Fixpoint termDenote (t : type) (e : term typeDenote t) : typeDenote t :=
    match e with
    | Var t0      v => v
    | Const       n => n
    | Plus        e1 e2 => termDenote e1 + termDenote e2
    | Abs dom ran e1    => fun (x : typeDenote dom) => termDenote (e1 x)
    | App dom ran e1 e2 => (termDenote e1) (termDenote e2)
    | Let t1  t2  e1 e2 => termDenote (e2 (termDenote e1))
    end.
  (* t0, t1, t2, dom, ran は type である。 *)
  (* x : typeDenote dom は、dom に対応する Type である。 *)
  (* Set Printing All. *)
  Print termDenote.
  
  Definition TermDenote (t : type) (E : Term t) : typeDenote t := termDenote (E typeDenote).

  (** termDenote の引数は、Term t に typeDenote を適用したもの。 *)
  Check (fun var => (App (Abs (fun x : var Nat => Var x)) (Const 1))) typeDenote.
  Compute (fun var => (App (Abs (fun x : var Nat => Var x)) (Const 1))) typeDenote.
  Set Printing All.
  Check @App typeDenote Nat Nat
    (@Abs typeDenote Nat Nat (fun x : typeDenote Nat => @Var typeDenote Nat x))
    (@Const typeDenote 1) : term typeDenote Nat.
  Check App (Abs (fun x : typeDenote Nat => Var x)) (Const 1)
    : term typeDenote Nat.
  
  (**
     Abs の中身は、``typeDenote Nat -> term typeDenote Nat`` 型である。
     ``x : typeDenote Nat`` は  nat であるから、x は 自然数であってよい。
     むしろ x を与えないと ``Term Nat`` にならない。
   *)
  
  (** TermDenote を実行してみる。引数は Term t  *)
  Check (fun var => (App (Abs (fun x : var Nat => Var x)) (Const 1))) : Term Nat.
  Compute TermDenote (fun var => (App (Abs (fun x : var Nat => Var x)) (Const 1))).
  (* 結果は *)
  Check 1 : typeDenote Nat.
  Check 1 : nat.
  
  (** **** ident 関数 *)

  Fixpoint ident (var : type -> Type) (t : type) (e : term var t) : term var t :=
    match e with
    | Var t0      v => Var v
    | Const       n     => Const n
    | Plus        e1 e2 => Plus (ident e1) (ident e2)
    | Abs dom ran e1    => Abs (fun x: var dom => ident (e1 x))
    | App dom ran e1 e2 => App (ident e1) (ident e2)
    | Let t1  t2  e1 e2 => Let (ident e1) (fun x => ident (e2 x))
    end.
  (* Set Printing All. *)
  Print ident.

  Definition Ident (t : type) (E : Term t) : Term t := fun var => ident (E var).
  
  (** TermDenote を実行してみる。引数は Term t  *)
  Check (fun var => (App (Abs (fun x : var Nat => Var x)) (Const 1))) : Term Nat.
  Compute Ident (fun var => (App (Abs (fun x : var Nat => Var x)) (Const 1))).
  (* 結果は *)
  Check (fun var : type -> Type => App (Abs (fun x : var Nat => Var x)) (Const 1)) : Term Nat.
  
  (** **** 証明 *)

  Lemma identSound : forall t (e : term typeDenote t),
      termDenote (ident e) = termDenote e.
  Proof.
    induction e; try easy.
    - simpl.
      now rewrite IHe1, IHe2.
    - ext.
      simpl.
      now rewrite H.
    - simpl.
      now rewrite IHe1, IHe2.
    - simpl.
      now rewrite H, IHe.
  Qed.
  
  Theorem IdentSound : forall t (E : Term t),
    TermDenote (Ident E) = TermDenote E.
  Proof.
    intros; apply identSound.
  Qed.

End HigherOrder.

(* END *)
