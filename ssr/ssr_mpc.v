(** Monadic Parser Combinators *)
(** モナディック パーサー コンビネータ *)

(* @suharahiromichi 2014_01_08 *)

(** paeser T の定義は sf/ImpParser_J を使用した。
    コンビネータの型は pcl.pdf、処理の内容は ocamlAda を参考にした。*)

(* http://proofcafe.org/sf/ImpParser_J.html *)
(* https://github.com/yoshihiro503/ocamlAda/blob/master/src/parserMonad.ml *)
(* https://ocaml.janestreet.com/files/pcl.pdf *)

Require Import ssreflect ssrbool ssrnat seq.
Require Import ssrfun.
Require Import String.
Require Import Ascii.

Definition token := string.

(* エラーメッセージのためのoption。 *)
Inductive optionE (T : Type) : Type :=
  | SomeE : T -> optionE T
  | NoneE : string -> optionE T.

Implicit Arguments SomeE [[T]].
Implicit Arguments NoneE [[T]].

Definition parser (T : Type) :=
  list token -> optionE (T * list token).
(* Tとしてとるものは、unit(予約語)、id、nat、bexp、aexp、com
   bexpがどこからくるのかは、自明ではない。 *)
Print unit.
Check unit.
Check (parser unit).
Check (parser nat).

(* ret : T -> parser T *)
Definition ret {T : Type} (t : T) : parser T :=
  fun (xs : list token) => SomeE (t, xs).
Check ret.

(* bind : parser T -> (T -> parser S) -> parser S *)
Definition bind_ {T S : Type} (p : parser T) (f : T -> parser S) : parser S :=
  fun (xs : list token) =>
    match p xs with
      | SomeE (t, xs') => f t xs'
      | NoneE err => NoneE err
    end.
Infix ">>=" := bind_ (left associativity, at level 61).
  
(* or : parser T -> parser T -> parser T *)
Definition or_ {T : Type} (p1 p2 : parser T) : parser T :=
  fun (xs : list token) =>
    match p1 xs with
      | SomeE (t, xs') => SomeE (t, xs')
      | NoneE err1 =>
        match p2 xs with
          | SomeE (t, xs') => SomeE (t, xs')
          | NoneE err2 => NoneE (err1 ++ err2) (* エラー文字列の連結 *)
        end
    end.
Infix "<|>" := or_ (right associativity, at level 71).

(* and : parser T -> parser S -> parser (T * S) *)
Definition and_ {T S : Type} (p1 : parser T) (p2 : parser S) : parser (T * S) :=
  p1
    >>= fun x => p2
                   >>= fun y => ret (x, y).
Infix ">*<" := and_ (right associativity, at level 71).

(* many : parser T -> parser (list T) *)
Fixpoint many {T : Type} (steps : nat) (p : parser T) : parser (list T) :=
  match steps with
    | 0 => 
      fun _ => NoneE "Too_many_recursive_calls"
    | S steps' =>
      p
        >>= fun x => many steps' p
                          >>= fun xs => ret (x :: xs)
      <|>
      ret nil
  end.

(* END *)
