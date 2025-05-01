(*
PHOASでshift/resetのCPS変換 in Rocq(旧Coq)

@mrkbc

https://qiita.com/mrkbc/items/89b034dadc69df2ad274

https://gist.github.com/mir-ikbch/4784caa2c6d5b29e99b9ab80b7849e82
 *)
Set Implicit Arguments.

(**
# 変換元のソース言語・Shift/Reset を持つ。
*)
Inductive type : Type :=
| Nat : type
| Unit : type
| Func : type -> type -> type -> type -> type.
(* answer type 付きの関数型 *)
Notation "t / a --> s / b" := (Func t s a b) (at level 40, a at next level, s at next level).
(* ``t --> s`` が本来の関数型、a と b は answer型、実行前後のコンテキスト。 *)
  
Section Var.
  Variable var : type -> Type.

  Inductive value : type -> Type :=
  | Var : forall t, var t -> value t
  | ConstN : nat -> value Nat
  | Tt : value Unit
  | Abs : forall dom ran a b, (var dom -> term ran a b) -> value (Func dom ran a b)
  with term : type -> type -> type -> Type :=
  | Val : forall t a, value t -> term t a a
  | Succ : forall a b, term Nat a b -> term Nat a b
  | App : forall dom ran a b c d, term (dom / a --> ran / b) c d -> term dom b c -> term ran a d
  | Shift : forall t a b c x, (var (Func t a x x) -> term c c b) -> term t a b
  | Reset : forall c t a, term c c t -> term t a a.

End Var.

Arguments Var [var t] _.
Arguments Tt {var}.
Arguments ConstN [var] _.
Arguments Abs [var dom ran a b] _.
Arguments Val [var t a] _.
Arguments Shift [var t] _ [b c] _ _.


(** [x : Term t a b] means that the term [x] has type [t] and evaluation of it changes the answer type from [a] to [b]. *)
(* Term t a b は，型 t を持つ項で，answer type を a から b へ変化させるようなものからなる型です。 *)
Definition Term t a b := forall var, term var t a b.
Definition Value t := forall var, value var t.

Notation "'λs' x ==> e" := (Abs (fun x => e)) (at level 30).
Notation "'λs' x : t ==> e" := (Abs (fun (x:t) => e)) (at level 30, x at next level).
Notation "x @ y" := (App x y) (at level 29).


(** Target language of CPS translation *)
(**
変換先のターゲット言語・Shift/Reset を持たない。
*)

(* ここから。。。。 *)

Inductive ttype : Type :=
| TNat : ttype
| TUnit : ttype
| TFunc : ttype -> ttype -> ttype.

Section TVar.
  Variable var : ttype -> Type.

  Inductive tterm : ttype -> Type :=
  | TVar : forall t, var t -> tterm t
  | TConstN : nat -> tterm TNat
  | TTt : tterm TUnit
  | TAbs : forall dom ran, (var dom -> tterm ran) -> tterm (TFunc dom ran)
  | TSucc : tterm TNat -> tterm TNat
  | TApp : forall dom ran, tterm (TFunc dom ran) -> tterm dom -> tterm ran
  | TLet : forall t1 t2, tterm t1 -> (var t1 -> tterm t2) -> tterm t2.

End TVar.

Definition TTerm t := forall var, tterm var t.

Arguments TVar [var t] _.
Arguments TConstN [var] _.
Arguments TAbs [var dom ran] _.

Notation "a --> b" := (TFunc a b) (at level 40).
Notation "'λ' x ==> e" := (TAbs (fun x => e)) (at level 30).
Notation "x @@ y" := (TApp x y) (at level 29).
Notation "'tlet' x :== e1 'in' e2" := (TLet e1 (fun x => e2)) (at level 35).


(** Translation of [tterm]s to Gallina terms. *)
Fixpoint ttypeDenote (t : ttype) : Type :=
  match t with
  | TNat => nat
  | TUnit => unit
  | TFunc t1 t2 => ttypeDenote t1 -> ttypeDenote t2
  end.

Fixpoint ttermDenote t (e : tterm ttypeDenote t) : ttypeDenote t :=
  match e with
  | TVar x => x
  | TConstN n => n
  | TTt _ => tt
  | TAbs f => fun x => ttermDenote (f x)
  | TSucc n => S (ttermDenote n)
  | TApp e1 e2 => ttermDenote e1 (ttermDenote e2)
  | TLet e1 e2 => ttermDenote (e2 (ttermDenote e1))
  end.

Definition TTermDenote t (E : TTerm t) := ttermDenote (E _).

(* 。。。。ここまでが、coq_cpdt_phoas_1.v の内容に等しい *)


(** CPS translation *)
(**
ソース言語 Term をターゲット言語 TTerm に変換する関数

ソース言語は ``term (fun s => var (cps_type s))`` である。
ターゲット言語は ``tterm var`` で表現される。
両者の var は同じものであるが、ソース言語の ``s`` をターゲット言語の ``cps_type s`` に変換している。
typeDenote と termDenote は使っていない。
*)

Fixpoint cps_type (t : type) : ttype :=
  match t with
  | Nat => TNat
  | Unit => TUnit
  | a / c --> b / d => cps_type a --> ((cps_type b --> cps_type c) --> cps_type d)
  end.

Fixpoint cps_value var t (v : value (fun s => var (cps_type s)) t) : tterm var (cps_type t) :=
  match v with
  | Var x => TVar x
  | ConstN n => TConstN n
  | Tt => TTt _
  | Abs f => TAbs (fun x => cps_term _ (f x))
  end
with cps_term var t a b (e : term (fun s => var (cps_type s)) t a b)
  : tterm var ((cps_type t --> cps_type a) --> cps_type b) :=
       match e with
       | Val v =>  (λ k ==> TVar k @@ cps_value _ v)
       | Succ e' =>
           (λ k ==> cps_term _ e' @@ (λ n ==> TVar k @@ TSucc (TVar n)))
       | App e1 e2 =>
           (λ k ==>
              cps_term _ e1 @@
              (λ m ==>
                 cps_term _ e2 @@
                 (λ n ==> (TVar m @@ TVar n) @@ TVar k)))
       | Shift _ _ f =>
           (λ k ==>
              tlet k'' :== ((λ n ==> (λ k' ==> TVar k' @@ (TVar k @@ TVar n)))) in
              (cps_term _ (f k'') @@ (λ m ==> TVar m)))
       | Reset _ e =>
           TAbs (fun k => TApp (TVar k) (TApp (cps_term _ e) (TAbs (fun m => TVar m))))
       end.

Definition CPS_Term t a b (e : Term t a b) : TTerm ((cps_type t --> cps_type a) --> cps_type b) :=
  fun var => cps_term var (e _).
(* ソース言語の Term t a b が CPS 変換によって、
   ターゲット言語の TTerm ((cps_type t --> cps_type a) --> cps_type b) と型を保存して定義できている。 *)

(** Examples *)
(**
実行例 - ttermDenote (e : tterm ttypeDenote t) を使う。
ターゲット言語のパラメータに ttypeDenote を与えて確認する。
ホスト言語 (gallina) のEvalを使用する。
*)

(* Shift k. (λ(_ : Unit). k 0) というソース言語の項は以下のように書けます。 *)
Example foo A B : Term _ _ _ :=
  fun (var : type -> Type) =>
    Shift A B (fun k => Val (λs _ : var Unit ==> Val (Var k) @ Val (ConstN 0))).
Check foo : forall A B : type, Term Nat A (Unit / B --> A / B).
(*
 foo : forall A B : type, Term Nat A (Unit / B --> A / B)
*)

(*
k の返り値の型を A とすると，まず，
k 0 (コードでは Val (Var k) @ (Val (ConstN 0)))
の部分は answer type を変化させないため，任意の B で Term A B B 型を持つはずです．
それに λ(_ : Unit) を付けた λ(_ : Unit). k 0 は Value (Unit / B --> A / B) になり，
さらにそれに Shift k を付けた全体の項は
answer type を A から Unit / B --> A / B に変化させるため，
Term Nat A (Unit / B --> A / B) と正しく型が推論されていることが分かります．
*)

Example foo' := CPS_Term (foo Nat Unit).
Eval compute in foo'.
Eval compute in (TTermDenote foo').
(*
     = fun (x : nat -> nat) (_ : unit) (x0 : nat -> unit) => x0 (x 0)
*)

(*
この foo を使って Reset (Succ foo) という項を考えます．
つまり，全体では Reset (Succ (Shift k. (λ(_ : Unit). k 0)) です．
*)
Example bar B C : Term _ _ _ :=
  fun (var : type -> Type) =>
    Reset C (Succ (foo _ B var)).
Check bar : forall B C : type, Term (Unit / B --> Nat / B) C C.
(*
  bar : forall B C : type, Term (Unit / B --> Nat / B) C C
 *)

(*
この bar を B := Unit, C := Unit とした上でCPS変換してみます．
*)
Example bar' B C := CPS_Term (bar B C).
Eval compute in bar' Unit Unit.
Eval compute in (TTermDenote (bar' Unit Unit)).
(*
     = fun x : (unit -> (nat -> unit) -> unit) -> unit =>
       x (fun (_ : unit) (x0 : nat -> unit) => x0 1)
 *)
(*
TTermDenote は前の節と同様に定義した表示的意味論です．
CPS変換した結果がちゃんとRocqのλ項として出てきました．
*)

(* END *)
