(* -*- coding: utf-8 -*- *)
From mathcomp Require Import all_ssreflect.
Require Import Coq.Lists.Streams.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(**
# Standard Coq の Stream
*)
(*
Section Streams.

  Variable A : Type.

  CoInductive Stream : Type := Cons : A -> Stream -> Stream.

  Definition hd (x : Stream) :=
    match x with
    | Cons a _ => a
    end.

  Definition tl (x : Stream) :=
    match x with
    | Cons _ xs =>xs
    end.
    
  CoInductive EqSt (s1 s2 : Stream) : Prop :=
  | eqst : hd s1 = hd s2 -> EqSt (tl s1) (tl s2) -> EqSt s1 s2.

  CoFixpoint EqSt_reflex (s : Stream) : EqSt s s :=
    eqst (erefl (hd s)) (EqSt_reflex (tl s)).

End Streams.
*)

(**
# CoFix を使った定義
*)
Section MyUnfold.
  Variable A B : Type.  
(**
参考：

- Ryusei's Notes (a.k.a. M59のブログ)

- npca2012年部誌KOF号_データ構造の畳み込みと展開
 *)

(**
## 補助関数
*)
  Fixpoint takeStream (n : nat) (s : Stream A) : list A :=
    match n with
    | O => nil
    | S n1 => (hd s) :: takeStream n1 (tl s)
    end.

(**
## Anamorphism - coFix で定義した。
*)
  CoFixpoint unfold (f : B -> A) (g : B -> B) (b : B) : Stream A :=
    Cons (f b) (unfold f g (g b)).
  
(**
## Hylomorphism - ダミー変数 で定義した。suhara
*)  
  Fixpoint fold (h : nat) (b : B) (f : A -> B -> B) (s : Stream A) : B :=
    match h with
    | 0 => b
    | h'.+1 => f (hd s) (fold h' b f (tl s))
    end.

End MyUnfold.

(**
# unfold と fold の組み合わせ
*)
Section Summation.

  Definition gen := unfold id (fun x => x.+1).
  Compute takeStream 10 (gen 1). (* = [:: 1; 2; 3; 4; 5; 6; 7; 8; 9; 10] *)

(**
## Summuation
*)
  Definition sum h := fold h 0 addn.
  Definition sumi m n := sum n (gen m).
  Compute sumi 1 3.                         (* 6 *)
  Compute sumi 1 4.                         (* 10 *)
  Compute sumi 1 5.                         (* 15 *)
  Compute sumi 1 10.                        (* 55 *)
  
(**
## Factorial
*)
  Definition mul h := fold h 1 muln.
  Definition fact m n := mul n (gen m).
  Compute fact 1 3.                         (* 6 *)
  Compute fact 1 4.                         (* 24 *)
  Compute fact 1 5.                         (* 120 *)
  
End Summation.

(**
# Noneで停止のかわりにした例
*)
Section Collatz.

  Definition collatz' :=
    unfold id (fun x => if odd x then (x * 3).+1 else x %/2).
  Compute takeStream 20 (collatz' 11).
  (* = [:: 11; 34; 17; 52; 26; 13; 40; 20; 10; 5; 16; 8; 4; 2; 1; 4; 2; 1; 4; 2] *)

  Definition collatz :=
    unfold id (fun x => match x with
                          | None => None
                          | Some 1 => None
                          | Some x' => Some (if odd x' then (x' * 3).+1 else x' %/2)
                          end).
  Compute takeStream 20 (collatz' (Some 11)).
  (* = [:: Some 11; Some 34; Some 17; Some 52; Some 26; Some 13; 
     Some 40; Some 20; Some 10; Some 5; Some 16; Some 8; 
     Some 4; Some 2; Some 1; None; None; None; None; None]
   *)
  
End Collatz.

(**
# フィボナッチ数列 ！！超重要！！

メモ化再帰を実現した例になっている。
*)
Section Fibonacci.

  Definition psi (a : nat * nat) := let (x, y) := a in (y, x + y).

  Definition fibgen := unfold fst psi (0, 1).
  Compute takeStream 10 fibgen. (* = [:: 0; 1; 1; 2; 3; 5; 8; 13; 21; 34] *)
  
End Fibonacci.

(**
# ソート

- npca2012年部誌KOF号_データ構造の畳み込みと展開
*)
Section Sort.
(**
リスト s の最小の要素を返す。
*)
  Fixpoint minimum s :=                   (* 仮に最初の要素を返す。 *)
    match s with
    | a :: a' => a
    | _ => 0
    end.

(**
リスト s から m を削除する。
*)
  Fixpoint delete (m : nat) (s : seq nat) :=
    match s with
    | a :: a' => if (a == m) then a' else delete m a'
    | _ => [::]
    end.

  Definition ssort := unfold fst (fun s =>
                                    let (_, s') := s in
                                    let m' := minimum s' in
                                    (m', delete m' s')).
  Compute takeStream 7 (ssort (0, [:: 1; 2; 3; 4])).
  
End Sort.

(**
# Ryusei さんの証明

Ryusei's Notes (a.k.a. M59のブログ)

- 無限リストと証明じゃないCoqの話

https://mandel59.hateblo.jp/entry/2013/02/07/213230

- Coq 帰納法と余帰納法

https://mandel59.hateblo.jp/entry/2013/02/09/151347  
 *)

Section MyStreams.
  
  Variable A B : Type.

  CoFixpoint iterate (f : A -> A) (x : A) : Stream A :=
    Cons x (iterate f (f x)).
  
(**
Streamの先頭にlistを連結するapp。
*)
  Fixpoint appStream (l : list A) (s : Stream A) : Stream A :=
    match l with
    | [::] => s
    | a :: l1 => Cons a (appStream l1 s)
    end.

(**
Streamの先頭n要素を捨てるdrop。
*)
  Fixpoint dropStream (n : nat) (s : Stream A) : Stream A :=
    match n with
      | O => s
      | S n1 =>
        match s with
        | Cons _ s1 => dropStream n1 s1
        end
    end.

(**  
Streamからtakeしてから、dropした残りのStreamにappすると元のストリームに戻ることの証明。
*)
  Theorem app_take : forall (n : nat) (s : Stream A),
      EqSt (appStream (takeStream n s) (dropStream n s)) s.
  Proof.
    move=> n.
    induction n as [|n' IH].
    - by apply EqSt_reflex.
    - case=> a s' /=.
        by apply: eqst => /=.
  Qed.

(**  
listをStreamにappしてからtakeすると元のlistが得られることの証明。
*)
  Theorem take_app : forall (l : list A) (s : Stream A),
      (takeStream (length l) (appStream l s)) = l.
  Proof.
    induction l as [|a l' IH].
    - done.
    - case=> a0 s0 /=.
        by apply f_equal.
  Qed.

(**  
iterate id a が const a に等しいことの証明。

これは余帰納法を使わないといけない。
Stream A型を返す関数で、余再帰的に定義されているconstやiterateを簡約するには、
simplを使う前に補題 unfold_Stream を使って書き換えておく必要があった。
*)
  Theorem iterate_id (a : A) :
    EqSt (iterate id a) (const a).
  Proof.
    cofix iterate_id.
    rewrite (unfold_Stream (iterate id a)).
    rewrite (unfold_Stream (const a)).
    simpl.
    apply eqst.
    - done.
    - by apply iterate_id.
  Qed.

End MyStreams.  

(* END *)
