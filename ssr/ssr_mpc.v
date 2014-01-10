(** Monadic Parser Combinators *)
(** モナディック パーサー コンビネータ *)

(* @suharahiromichi 2014_01_08 *)

(** paeser T の定義は sf/ImpParser_J を使用した。
    コンビネータの型は pcl.pdf、処理の内容は ocamlAda を参考にした。*)

(* http://proofcafe.org/sf/ImpParser_J.html *)
(* https://github.com/yoshihiro503/ocamlAda/blob/master/src/parserMonad.ml *)
(* https://ocaml.janestreet.com/files/pcl.pdf *)

Require Import ssreflect ssrbool ssrnat seq eqtype.
Require Import ssrfun.
Require Import String.
Require Import Ascii.

(** ** 字句解析 *)
Definition isWhite (c : ascii) : bool :=
  let n := nat_of_ascii c in
  (n == 32) ||                              (* space *)
            (n ==  9) ||                    (* tab *)
            (n == 10) ||                    (* linefeed *)
            (n == 13).                      (* Carriage return. *)

Definition isLowerAlpha (c : ascii) : bool :=
  let n := nat_of_ascii c in
  (97 <= n) && (n <= 122).

Definition isAlpha (c : ascii) : bool :=
  let n := nat_of_ascii c in
  (65 <= n) && (n <= 90) ||
            (97 <= n) && (n <= 122).

Definition isDigit (c : ascii) : bool :=
  let n := nat_of_ascii c in
  (48 <= n) && (n <= 57).

Inductive chartype := white | alpha | digit | other.

Definition classifyChar (c : ascii) : chartype :=
  if isWhite c then
    white
  else if isAlpha c then
    alpha
  else if isDigit c then
    digit
  else
    other.

Fixpoint list_of_string (s : string) : list ascii :=
  match s with
  | EmptyString => [::]
  | String c s => c :: (list_of_string s)
  end.

Fixpoint string_of_list (xs : list ascii) : string :=
  foldr String EmptyString xs.

Definition token := string.

Fixpoint tokenize_helper (cls : chartype) (acc xs : list ascii)
                       : list (list ascii) :=
  let tk :=
      match acc with
        | [::] => [::]
        | _::_ => (rev acc) :: [::]
      end in
  match xs with
    | [::] => tk
    | (x::xs') =>
      match cls, classifyChar x, x with
        | _, _, "("      => tk ++ [:: "("] :: (tokenize_helper other [::] xs')
        | _, _, ")"      => tk ++ [:: ")"] :: (tokenize_helper other [::] xs')
        | _, white, _    => tk ++ (tokenize_helper white [::] xs')
        | alpha,alpha,x  => tokenize_helper alpha (x::acc) xs'
        | digit,digit,x  => tokenize_helper digit (x::acc) xs'
        | other,other,x  => tokenize_helper other (x::acc) xs'
        | _,tp,x         => tk ++ (tokenize_helper tp [:: x] xs')
      end
  end %char.
(* "("と")"だけ別になっているのは、"("と")"の前後にはスペースがなくても、
 トークンの区切りと解釈するため。　他の記号はスペースが必要。
 つまり、"--" は"-"ふたつとは解釈されないが、"-("は、"-"と"("と区別される。 *)

(* ***トークンのパースのメイン*** *)
Definition tokenize (s : string) : list string :=
  map string_of_list (tokenize_helper white [::] (list_of_string s)).

Example tokenize_ex1 :
  tokenize "abc12==3  223*(3+(a+c))"%string
  = [:: "abc"; "12"; "=="; "3"; "223";
       "*"; "("; "3"; "+"; "(";
       "a"; "+"; "c"; ")"; ")" ]%string.
Proof. reflexivity. Qed.

(** Option と Error *)
Inductive optionE (T : Type) : Type :=
  | SomeE : T -> optionE T
  | NoneE : string -> optionE T.

Implicit Arguments SomeE [[T]].
Implicit Arguments NoneE [[T]].

(** *** Symbol Table *)
Fixpoint forallb {A} f (l:list A) : bool :=
  match l with
    | nil => true
    | a::l => f a && forallb f l
  end.

Fixpoint build_symtable (xs : list token) (n : nat) : (token -> nat) :=
  match xs with
  | [::] => (fun s => n)
  | x::xs =>
    if (forallb isLowerAlpha (list_of_string x)) then
      (fun s => if string_dec s x then n else (build_symtable xs (S n) s))
     else
       build_symtable xs n
  end.

Eval compute in build_symtable [::] 0.      (* 空のシンボルテーブル *)
Eval compute in build_symtable [:: "aaa"; "+"; "bbb"; "+"; "ccc"]%string
                               0 "aaa"%string . (* 0 *)
Eval compute in build_symtable [:: "aaa"; "+"; "bbb"; "+"; "ccc"]%string
                               0 "bbb"%string. (* 1 *)
Eval compute in build_symtable [:: "aaa"; "+"; "bbb"; "+"; "ccc"]%string
                               0 "ccc"%string. (* 2 *)
Eval compute in build_symtable [:: "aaa"; "+"; "bbb"; "+"; "ccc"]%string
                               0 "xxx"%string. (* 3 *)

(** コンビネータ *)
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

(* bind2 : parser T -> parser S -> parser S *)
Definition bind2_ {T S : Type} (p1 : parser T) (p2 : parser S) : parser S :=
  p1 >>= fun _ => p2.
Infix ">>>" := bind2_ (left associativity, at level 61).

(* bind1 : parser T -> parser S -> parser T *)
Definition bind1_ {T S : Type} (p1 : parser T) (p2 : parser S) : parser T :=
  p1 >>= fun x => p2 >>> ret x.
Infix "<<<" := bind1_ (left associativity, at level 61).

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
      ret [::]
  end.

(* A parser which expects a given token, followed by p *)
(* pの前のトークン（補足例："IF"、"("、"*"など）を引数とするパーサ *)
Definition firstExpect {T} (t : token) (p : parser T) : parser T :=
  fun xs =>
    match xs with
      | x::xs' =>
        if string_dec x t then
          p xs'
        else
          NoneE ("expected '" ++ t ++ "'.")
      | [::] =>
        NoneE ("expected '" ++ t ++ "'.")
    end.

(* A parser which expects a particular token *)
(* 特定のトークンを引数とするパーサ *)
(* T = unit
   補足：parse reserved word とおもってよい。 *)
Definition expect (t : token) : parser unit :=
  firstExpect t (fun xs => SomeE (tt, xs)).
Check tt.                                   (* unit *)
Check (expect ")"%string).                  (* parser unit *)
Check (expect ")"%string [::]).             (* optionE (unit * list token) *)
Check (expect "true"%string).               (* parser unit *)

(** 抽象構文 *)
Inductive id : Type :=
  Id : nat -> id.

Inductive aexp : Type :=
  | ANum : nat -> aexp
  | AId : id -> aexp
  | APlus : aexp -> aexp -> aexp
  | AMinus : aexp -> aexp -> aexp
  | AMult : aexp -> aexp -> aexp.

Inductive bexp : Type :=
  | BTrue : bexp
  | BFalse : bexp
  | BEq : aexp -> aexp -> bexp
  | BLe : aexp -> aexp -> bexp
  | BNot : bexp -> bexp
  | BAnd : bexp -> bexp -> bexp.

Inductive com : Type :=
  | CSkip : com
  | CAss : id -> aexp -> com
  | CSeq : com -> com -> com
  | CIf : bexp -> com -> com -> com
  | CWhile : bexp -> com -> com.

(*
Notation "'SKIP'" :=
  CSkip.
Notation "X '::=' a" :=
  (CAss X a) (at level 60).
Notation "c1 ; c2" :=
  (CSeq c1 c2) (at level 80, right associativity).
Notation "'WHILE' b 'DO' c 'END'" :=
  (CWhile b c) (at level 80, right associativity).
Notation "'IFB' e1 'THEN' e2 'ELSE' e3 'FI'" :=
  (CIf e1 e2 e3) (at level 80, right associativity).
*)

(* *** A Recursive-Descent Parser for Imp *)
(** *** Impの再帰下降パーサ *)

(* Identifiers *)
(* 識別子 *)
Definition parseIdentifier (symtable :string->nat) : parser aexp :=
  fun xs =>
    match xs with
      | [::] =>
        NoneE "Expected identifier"
      | x::xs' =>
        if forallb isLowerAlpha (list_of_string x) then
          SomeE (AId (Id (symtable x)), xs')
        else
          NoneE ("Illegal identifier:'" ++ x ++ "'")
    end.
(* Numbers *)
(* 数値 *)
Definition parseNumber : parser aexp :=
  fun xs =>
    match xs with
      | [::] =>
        NoneE "Expected number"
      | x::xs' =>
        if forallb isDigit (list_of_string x) then
          SomeE (ANum
                   (foldl (fun n d =>
                             10 * n + (nat_of_ascii d - nat_of_ascii "0"%char))
                          0
                          (list_of_string x)),
                 xs')
        else
          NoneE "Expected number"
    end.

(* Parse arithmetic expressions *)
(* 算術式の構文解析 *)
Fixpoint parsePrimaryExp (steps : nat) symtable : parser aexp :=
  match steps with
    | 0 =>
      fun _ => NoneE "Too_many_recursive_calls"
    | S steps' =>
      (parseIdentifier symtable)
        <|>
        parseNumber
        <|>
        expect "("%string
        >>> parsePrimaryExp steps' symtable
        <<< expect ")"%string
  end.

Eval compute in parseNumber [:: "123"]%string.
Eval compute in parseIdentifier 
                  (build_symtable [::]%string 0)
                  [:: "X"]%string.
Eval compute in parsePrimaryExp 1000
                                (build_symtable [::] 0)
                                [:: "123"]%string.
Eval compute in parsePrimaryExp 1000
                                (build_symtable [::] 0)
                                [:: "("; "123"; ")"]%string.

(* END *)
