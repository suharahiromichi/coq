(**
Parametric Higher-Order Abstract Syntax (PHOAS) などの 変数束縛を扱う構文の表現の比較

2025_04_12


PHOASの必要性

- ホスト言語(Coq)は、Lispのようなメタ表現がないので、
  ホスト言語をソース言語やターゲット言語にするわけにいかない。
- Named ASTと同等以上の表現力が欲しいが、Substをホスト言語の機能を利用して楽をしたい。
- PHOAS は、Named ASTの変数をパラメタライズしたもの。これにより、Subst を自分で実装しなくてもよい。
- パラメタライズを行う際、ソース言語やターゲット言語の型を表す場合と、
  ソース言語やターゲット言語の型からホスト言語の型への変換を表す場合がある。
  Typed PHOAS、TPHOAS と呼ばれる後者の方が、ホスト言語への埋め込みが容易です。CPDT では、後者を PHOAS と呼んでいる。
 *)

Require Import String.
Require Import List.
Import ListNotations.

Open Scope string_scope.

(**
# De Bruijn Index
*)
Module DeBrujin.
  Section DeBrujin.
    
    Inductive expr : Type :=
    | Var : nat -> expr
    | App : expr -> expr -> expr
    | Lam : expr -> expr.
  End DeBrujin.

  Definition I := Lam (Var 0).
  Definition K := Lam (Lam (Var 1)).
  Definition S := Lam (Lam (Lam
                              (App (App (Var 2) (Var 0))
                                 (App (Var 1) (Var 0))))).
End DeBrujin.

(**
# Named AST
 *)
Module NAST.
  Section NAST.
    
    Inductive expr : Type :=
    | Var : string -> expr
    | App : expr -> expr -> expr
    | Lam : string -> expr -> expr.
  End NAST.

  Definition I := Lam "x" (Var "x").
  Definition K := Lam "x" (Lam "y" (Var "x")).
  Definition S := Lam "x"
                    (Lam "y"
                       (Lam "z"
                          (App (App (Var "x") (Var "z"))
                             (App (Var "y") (Var "z"))))).
End NAST.

(**
# 使えないHOAS

これはCoqでは実装できない。
*)
Module HOAS'.
  Section HOAS'.
    
    Fail Inductive expr : Type :=
    | App : expr -> expr -> expr
    | Lam : (expr -> expr) -> expr.
  End HOAS'.
  
  Fail Definition I := Lam (fun x => x).
  Fail Definition K := Lam (fun x => Lam (fun y => x)).
  Fail Definition S := Lam (fun x =>
                              Lam (fun y =>
                                     Lam (fun z =>
                                       App (App x z)
                                         (App y z)))).
End HOAS'.

(**
# HOAS

- NAST と比べると、似ていて異なる。
- x y z は string型
 *)
Module HOAS.
  Section HOAS.
    
    Inductive expr : Type :=
    | Var : string -> expr
    | App : expr -> expr -> expr
    | Lam : (string -> expr) -> expr.
  End HOAS.
  
  Definition I := Lam (fun x => Var x).
  Definition K := Lam (fun x => Lam (fun y => Var x)).
  Definition S := Lam (fun x =>
                         Lam (fun y =>
                                Lam (fun z =>
                                       App (App (Var x) (Var z))
                                         (App (Var y) (Var z))))).
End HOAS.

(**
# PHOAS

- var型を引数にとる。var型は後で決めることができる。
- x y z は var 型。
 *)
Module PHOAS.
  Section PHOAS.
    Variable var : Type.
    
    Inductive expr : Type :=
    | Var : var -> expr
    | App : expr -> expr -> expr
    | Lam : (var -> expr) -> expr.
  End PHOAS.
  
  Definition I := fun var => Lam var (fun x => Var var x).
  Definition K := fun var => Lam var (fun x => Lam var (fun y => Var var x)).
  Definition S := fun var => Lam var (fun x =>
                                        Lam var (fun y =>
                                                   Lam var (fun z =>
                                                              App var (App var (Var var x) (Var var z))
                                                                (App var (Var var y) (Var var z))))).
End PHOAS.

(**
# Typed PHOAS (TPHOAS)

- CPDTなどのPHOASはこれ。
- 型ファミリ（依存型）を引数にとる。
*)
Module TPHOAS.
  Section TPHOAS.
    
    Inductive type : Type :=
    | Nat
    | Arrow : type -> type -> type.
    
    Variable var : type -> Type.
    
    Inductive expr : type -> Type :=
    | Var : forall {t}, var t -> expr t
    | App : forall {t1 t2}, expr (Arrow t1 t2) -> expr t1 -> expr t2
    | Lam : forall {t1 t2}, (var t1 -> expr t2) -> expr (Arrow t1 t2).
  End TPHOAS.

  Definition I := fun var => Lam var (fun x : var Nat => Var var x).
  Definition K := fun var => Lam var (fun x : var Nat => Lam var (fun y : var Nat => Var var x)).
  Definition S := fun var => Lam var (fun x : var (Arrow Nat (Arrow Nat Nat)) =>
                                        Lam var (fun y : var (Arrow Nat Nat) =>
                                                   Lam var (fun z : var Nat =>
                                                              App var (App var (Var var x) (Var var z))
                                                                (App var (Var var y) (Var var z))))).

  Definition I' := fun var => @Lam var Nat Nat (fun x : var Nat => @Var var Nat x).
  Definition K' := fun var => @Lam var Nat (Arrow Nat Nat)
                                (fun x : var Nat => @Lam var Nat Nat
                                                      (fun _ : var Nat => @Var var Nat x)).
  Definition S' := fun var : forall _ : type, Type =>
                    @Lam var (Arrow Nat (Arrow Nat Nat)) (Arrow (Arrow Nat Nat) (Arrow Nat Nat))
                      (fun x : var (Arrow Nat (Arrow Nat Nat)) =>
                         @Lam var (Arrow Nat Nat) (Arrow Nat Nat)
                           (fun y : var (Arrow Nat Nat) =>
                              @Lam var Nat Nat
                                (fun z : var Nat =>
                                   @App var Nat Nat
                                     (@App var Nat (Arrow Nat Nat)
                                        (@Var var (Arrow Nat (Arrow Nat Nat)) x)
                                        (@Var var Nat z))
                                     (@App var Nat Nat (@Var var (Arrow Nat Nat) y) (@Var var Nat z))))).
End TPHOAS.

(* END *)
