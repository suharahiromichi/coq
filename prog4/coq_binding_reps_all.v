(**
Parametric Higher-Order Abstract Syntax (PHOAS) などの 変数束縛を扱う構文の表現の比較

2025_04_12
 *)
Require Import String.
Require Import List.
Import ListNotations.

Open Scope string_scope.

Module HOAS.
  Section HOAS.
    
    Fail Inductive expr : Type :=
    | App : expr -> expr -> expr
    | Lam : (expr -> expr) -> expr.
  End HOAS.
End HOAS.

(**
De Bruijn Index
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
  Definition S := Lam (Lam (Lam (App (App (Var 2) (Var 0))
                                   (App (Var 1) (Var 0))))).
End DeBrujin.

(**
Named AST
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
  Definition S := Lam "x" (Lam "y"
                             (Lam "z" (App (App (Var "x") (Var "z"))
                                         (App (Var "y") (Var "z"))))).
End NAST.

(**
PHOAS

型を引数にとる。
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
  (* x y z は var 型 *)
End PHOAS.

(**
Typed PHOAS

CPDTなどのPHOASはこれ。
型ファミリ（依存型）を引数にとる。
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
End TPHOAS.

(* END *)
