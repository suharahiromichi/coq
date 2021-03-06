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

(** (1) 字句解析 *)
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

(** (2) Symbol Table *)
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

(** (3) パーサ コンビネータ *)
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
Infix ">>=" := bind_ (left associativity, at level 71).
(* OCamlにあわせて、>,<から始まる演算子は、すべて左結合で同一優先順位とする。
実際は、右結合のほうが使いやすいとおもう。 *)

(* bind2 : parser T -> parser S -> parser S *)
Definition bind2_ {T S : Type} (p1 : parser T) (p2 : parser S) : parser S :=
  p1 >>= fun _ => p2.
Infix ">>>" := bind2_ (left associativity, at level 71).

(* bind1 : parser T -> parser S -> parser T *)
Definition bind1_ {T S : Type} (p1 : parser T) (p2 : parser S) : parser T :=
  p1 >>= fun x => p2 >>> ret x.
Infix "<<<" := bind1_ (left associativity, at level 71).

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
Infix "<|>" := or_ (left associativity, at level 71).

(* and : parser T -> parser S -> parser (T * S) *)
Definition and_ {T S : Type} (p1 : parser T) (p2 : parser S) : parser (T * S) :=
  p1
    >>= fun x => p2
                   >>= fun y => ret (x, y).
Infix ">*<" := and_ (left associativity, at level 71).

(* many : parser T -> parser (list T) *)
Fixpoint many {T : Type} (steps : nat) (p : parser T) : parser (list T) :=
  match steps with
    | 0 => 
      fun _ => NoneE "Too_many_recursive_calls"
    | S steps' =>
      (p                                    (* ここの括弧は必要！ *)
         >>= fun x => many steps' p
                           >>= fun xs => ret (x :: xs))
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

(** Impの再帰下降パーサ を「モナディック パーサー コンビネータ」で書き換えた。 *)

(* Identifiers *)
(* 識別子 *)
Definition parseIdentifier symtable (xs : list token) : optionE (id * list token) :=
    match xs with
      | [::] =>
        NoneE "Expected identifier"
      | x::xs' =>
        if forallb isLowerAlpha (list_of_string x) then
          SomeE (Id (symtable x), xs')
        else
          NoneE ("Illegal identifier:'" ++ x ++ "'")
    end.
(* Numbers *)
(* 数値 *)
Definition parseNumber (xs : list token) : optionE (nat * list token) :=
    match xs with
      | [::] =>
        NoneE "Expected number"
      | x::xs' =>
        if forallb isDigit (list_of_string x) then
          SomeE (foldl (fun n d => 10 * n + (nat_of_ascii d - nat_of_ascii "0"%char))
                       0
                       (list_of_string x),
                 xs')
        else
          NoneE "Expected number"
    end.

(* parser (seq T) を parser T に変換するユーティリティ *)
Definition foldlParser {T : Type}
           (f : T -> T -> T) (e : T) (p : parser (seq T)) : parser T :=
  fun (xs : list token) =>
    match p xs with
      | SomeE (es, rest') =>
        SomeE (foldl f e es, rest')         (* T * token list *)
      | NoneE err =>
        NoneE err
    end.

(* Parse arithmetic expressions *)
(* 算術式の構文解析 *)
Fixpoint parsePrimaryExp (steps : nat) symtable : parser aexp :=
  match steps with
    | 0 =>
      fun _ => NoneE "Too_many_recursive_calls"
    | S steps' =>
      (parseIdentifier symtable >>= fun x => ret (AId x))
                      <|>
                      (parseNumber >>= fun x => ret (ANum x))
                      <|>
                      (expect "("%string
                              >>>
                              parseSumExp steps' symtable
                              <<<
                              expect ")"%string)
  end
with parseProductExp (steps : nat) symtable : parser aexp :=
  match steps with
    | 0 =>
      fun _ => NoneE "Too_many_recursive_calls"
    | S steps' =>
      parsePrimaryExp steps' symtable
                      >>=
                      fun (x : aexp) =>
                        foldlParser AMult
                                    x
                                    (many steps' (expect "*"%string
                                                         >>>
                                                         parsePrimaryExp steps' symtable))
  end
with parseSumExp (steps : nat) symtable : parser aexp :=
  match steps with
    | 0 =>
      fun _ => NoneE "Too_many_recursive_calls"
    | S steps' =>
      parseProductExp steps' symtable
                      >>=
                      fun (x : aexp) =>
                        foldlParser APlus
                                    x
                                    (many steps' (expect "+"%string
                                                         >>>
                                                         parseProductExp steps' symtable))
  (* AMinus ("-") は、未実装。foldlParser で挿入するコンストラクタをどう選べばよいのか。 *)
  end.

Definition parseAExp := parseSumExp.

Fixpoint parseAtomicExp (steps : nat) symtable : parser bexp :=
  match steps with
    | 0 =>
      fun _ => NoneE "Too_many_recursive_calls"
    | S steps' =>
      (expect "true"%string
              >>>
              ret BTrue)
        <|>
        (expect "false"%string
                >>>
                ret BFalse)
        <|>
        (expect "not"%string
                >>>
                parseAtomicExp steps' symtable)
        <|>
        (expect "("%string
                >>>
                parseConjunctionExp steps' symtable
                <<<
                expect ")"%string)
        <|>
        (parseProductExp steps' symtable
                         >>=
                         fun x =>
                           (expect "=="%string
                                   >>>
                                   (parseAExp steps' symtable)
                                   >>=
                                   fun x' => ret (BEq x x'))
                             <|>
                             (expect "<="%string
                                     >>>
                                     (parseAExp steps' symtable)
                                     >>=
                                     fun x' => ret (BLe x x')))
  end
with parseConjunctionExp (steps : nat) symtable : parser bexp :=
  match steps with
    | 0 =>
      fun _ => NoneE "Too_many_recursive_calls"
    | S steps' =>
      parseAtomicExp steps' symtable
                     >>=
                     fun (x : bexp) =>
                       foldlParser BAnd
                                    x
                                    (many steps' (expect "&&"%string
                                                         >>>
                                                         parseAtomicExp steps' symtable))
  end.

Definition parseBExp := parseConjunctionExp.

Fixpoint parseSimpleCommand (steps : nat) symtable : parser com :=
  match steps with
    | 0 =>
      fun _ => NoneE "Too_many_recursive_calls"
    | S steps' =>
      (expect "SKIP"%string
              >>>
              ret CSkip)
        <|>
        (expect "IF"%string
                >>>
                (parseBExp steps' symtable
                           >>=
                           fun x =>
                             expect "THEN"%string
                                    >>>
                                    (parseSequencedCommand steps' symtable
                                                           >>=
                                                        fun x' =>
                                                          expect "ELSE"%string
                                                                 >>>
                                                                 (parseSequencedCommand steps' symtable
                                                                                     >>=
                                                                                     fun x'' =>
                                                                                       expect "END"%string
                                                                                              >>>
                                                                                              ret (CIf x x' x'')))))
        <|>
        (expect "WHILE"%string
                >>>
                (parseBExp steps' symtable
                           >>=
                           fun x =>
                             expect "DO"%string
                                    >>>
                                    (parseSequencedCommand steps' symtable
                                                        >>=
                                                        fun x' =>
                                                          expect "END"%string
                                                                 >>>
                                                                 ret (CWhile x x'))))
        <|>
        (parseIdentifier symtable
                         >>=
                         fun x =>
                           expect ":="%string
                                  >>>
                                  (parseAExp steps' symtable
                                             >>=
                                             fun x' => ret (CAss x x')))
  end
with parseSequencedCommand (steps : nat) symtable : parser com :=
  match steps with
    | 0 =>
      fun _ => NoneE "Too_many_recursive_calls"
    | S steps' =>
      (parseSimpleCommand steps' symtable
                          >>=
                          fun x =>
                            (expect ";"%string
                                    >>> 
                                    (parseSequencedCommand steps' symtable
                                                           >>=
                                                           fun x' => ret (CSeq x x')))
                              <|>
                              ret x)
        
  end.

Definition parse (str : string) : optionE (com * list token) :=
  let tokens := tokenize str in             (* (1) *)
    parseSequencedCommand 20                (* (3) *)
    (build_symtable tokens 0)               (* (2) *)
    tokens.

(* Sample *)
Eval compute in build_symtable [:: "a"; "+"; "b"]%string.
Eval compute in build_symtable [:: "a"; "+"; "b"]%string 0 "a"%string. (* 0 *)
Eval compute in build_symtable [:: "a"; "+"; "b"]%string 0 "b"%string. (* 1 *)

Eval compute in parseNumber [:: "123"]%string.
Eval compute in parseIdentifier (build_symtable [:: "a"]%string 0)
                                [:: "a"]%string.
Eval compute in parsePrimaryExp 1000 (build_symtable [::] 0)
                                [:: "123"]%string.
Eval compute in parsePrimaryExp 1000 (build_symtable [::] 0)
                                [:: "("; "123"; ")" ]%string.
Eval compute in parseProductExp 1000 (build_symtable [::] 0)
                                [:: "123" ]%string.
Eval compute in parseProductExp 1000 (build_symtable [::] 0) (* 左結合になっている。 *)
                                [:: "123"; "*"; "456"; "*"; "789"]%string.
Eval compute in parseSumExp 1000 (build_symtable [::] 0) (* 左結合になっている。 *)
                            [:: "123"; "+"; "456"; "+"; "789"]%string.
Eval compute in parseAExp 1000 (build_symtable [::] 0)
                          [:: "("; "123"; "+"; "345"; ")"; "*"; "679" ]%string.
Eval compute in parseAExp 1000 (build_symtable [::] 0)
                          [:: "123"; "+"; "345"; "*"; "679" ]%string.

Eval compute in parseBExp 10 (build_symtable [::] 0)
                          [:: "123"; "=="; "345" ]%string.
Eval compute in parseBExp 10 (build_symtable [::] 0)
                          [:: "123"; "=="; "345"; "&&"; "321"; "=="; "543"]%string.
Eval compute in parseBExp 10 (build_symtable [::] 0) (* 左結合になっている。 *)
                          [:: "1"; "=="; "2"; "&&"; "3"; "<="; "4"; "&&";
                           "5"; "<="; "6"; "&&"; "7"; "=="; "8"]%string.

Eval compute in parseSimpleCommand 10 (build_symtable [::] 0)
                                   [:: "IF"; "1"; "=="; "1"; "THEN"; "SKIP"; "ELSE"; "SKIP"; "END"]%string.
Eval compute in parseSimpleCommand 10 (build_symtable [::] 0)
                                   [:: "WHILE"; "1"; "=="; "1"; "DO"; "SKIP"; "END"]%string.
Eval compute in parseSimpleCommand 10 (build_symtable [:: "a"; "="; "1"]%string 0)
                                   [:: "a"; ":="; "1"]%string.
Eval compute in parseSequencedCommand 10 (build_symtable [::] 0) (* 右結合になっている。 *)
                                      [:: "SKIP"; ";"; "SKIP"; ";"; "SKIP"]%string.

Eval compute in parse "
    IF x == y + 1 + 2 + y * 6 + 3 THEN
      x := x * 1;
      y := 0
    ELSE
      SKIP
    END  ".

Eval compute in parse "
    SKIP;
    z:=x*y*(x*x);
    WHILE x==x DO
      IF z <= z*z && not x == 2 THEN
        x := z;
        y := z
      ELSE
        SKIP
      END;
      SKIP
    END;
    x:=z  ".

(* END *)
