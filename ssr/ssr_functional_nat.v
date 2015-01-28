Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Compute
  (let: x := 1 in
   let: f := (fun y => x + y) in
   let: x := 2 in
   f (x + 3)).                              (* 6 *)

Compute
  (let: x := 10 in
   let: f := (fun y => x - y) in
   let: x := 5 in
   f (x - 3)).                              (* 8 *)


Inductive id :=
| Id of nat.

Inductive exp :=
| None
| Var of id
| Nat of nat
| Add of exp * exp
| If of exp * exp * exp * exp
| Sub of exp * exp
| Fun of id * exp
| App of exp * exp.

Definition x := Id 1.
Definition y := Id 2.
Definition z := Id 3.
Definition f := Id 4.
Definition g := Id 5.
Definition h := Id 6.
Definition n := Id 7.
Definition m := Id 8.
Definition sum := Id 9.

Definition eq_id (x y : id) : bool :=
  let: Id n := x in
  let: Id m := y in
  n == m.

Fixpoint subst (e0 : exp) (x : id) (v : exp) :=
  match e0 with
    | None => None
    | Var y =>
      if eq_id x y then v                   (* 同じ変数名か？ *) 
      else Var y                            (* 置き換える *) 
    | Nat n => Nat n
    | Add(e1, e2) =>
      Add(subst e1 x v, subst e2 x v)
    | Sub(e1, e2) =>
      Sub(subst e1 x v, subst e2 x v)
    | If(e1, e2, e3, e4) =>
      If(subst e1 x v, subst e2 x v,
         subst e3 x v, subst e4 x v)        (* 単に再帰的に代入 *)
    | App(e1, e2) =>
      App(subst e1 x v, subst e2 x v)       (* 単に再帰的に代入 *)
    | Fun(y, e) =>
      if eq_id x y then e0
      else Fun(y, subst e x v)
  end.

Fixpoint eval' (e : exp) (t : nat) {struct t} : exp :=
  if t is t'.+1 then
    match e with
      | None => None
      | Var id => Var id
      | Nat n => Nat n
      | Add(e1, e2) =>
        if eval' e1 t' is Nat n then
          if eval' e2 t' is Nat m then
            Nat (n + m)
          else
            None
        else
          None
      | Sub(e1, e2) =>
        if eval' e1 t' is Nat n then
          if eval' e2 t' is Nat m then
            Nat (n - m)
          else
            None
        else
          None
      | If(e1, e2, e3, e4) =>
        if eval' e1 t' is Nat n then
          if eval' e2 t' is Nat m then
            if n <= m then
              eval' e3 t'
            else
              eval' e4 t'
          else
            None
        else
          None
      | Fun(x, e) => Fun(x, e)
      | App(e1, e2) =>
        if eval' e1 t' is Fun(x, e) then
          let: v := eval' e2 t' in eval' (subst e x v) t'
        else
          None
    end
  else
    None.

Definition eval (e : exp) : exp := eval' e 100.

Definition _Let (e0 : id * exp * exp) : exp :=
  let: (x, e1, e2) := e0 in App(Fun(x, e2), e1).

Definition ex :=
  _Let(x, Nat 1,
       _Let(f, Fun(y, Add(Var x, Var y)),
            _Let(x, Nat 2,
                 App(Var f, Add(Var x, Nat 3))))).
Compute (eval ex).                         (* 6 *)

Definition ex2 :=
  _Let(x, Nat 10,
       _Let(f, Fun(y, Sub(Var x, Var y)),
            _Let(x, Nat 5,
                 App(Var f, Sub(Var x, Nat 3))))).
Compute (eval ex2).                         (* 8 *)


(* **** *)

(* 再帰を実現するための魔訶不思議な式
     （不動点演算子(fixed-point operator)と言います） *)

Definition _fix :=
  Fun(f,
      App(Fun(x,
              App(Var f,
                  Fun(y, App(App(Var x, Var x), Var y)))),
          Fun(x,
              App(Var f,
                  Fun(y, App(App(Var x, Var x), Var y)))))).

(* let rec f(x) = e1 in f(e2) に相当 *)
Definition _Rec (e : id * id * exp * exp) : exp :=
  let: (f, x, e1, e2) := e in
  App(App(_fix, Fun(f, Fun(x, e1))), e2).

(**
プログラム例4：1から10000までの整数の総和
*)
(* let rec sum(n) = if n<=0 then 0 else sum(n-1)-(0-n) in sum(10000) *)
Definition sum10000 :=
  _Rec(sum, n,
       If(Var n, Nat 0, Nat 0,
          Add(Var sum, Nat 1)),
       Nat 10000).
Compute (eval sum10000).

      
(* END *)
