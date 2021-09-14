(* -*- coding: utf-8 -*- *)
(**
有限リストで表現するが、停止条件を外から与える再帰は、停止性が証明できないため、
Coqでは扱いにくい。

無限リストによる unfold の定義は、 ``ssr_rec_pat_2.v`` を参照のこと。
*)

(**
# 再帰のパターン

- 再帰のパターン maoe のブログ

https://maoe.hatenadiary.jp/entry/20090820/1250782646

https://en.wikipedia.org/wiki/Anamorphism
 *)
From mathcomp Require Import all_ssreflect.
Require Import ssromega.
Require Import Recdef.                   (* Function *)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section Homomorphism.

  Variable A B : Type.
  Variable _a : A.                          (* ダミー値 *)
  
(**
## Catamorphism
*)
  Fixpoint cata (b : B) (f : A -> B -> B) (s : seq A) : B :=
    match s with
    | [::] => b
    | a :: a' => f a (cata b f a')
    end.
  
(**
## Anamorphism - ダミー変数を使って定義する。
*)
  Fixpoint ana (h : nat) (g : B -> A * B) (p : pred B) (b : B) : seq A :=
    match h with
    | 0 => [::]
    | h.+1 => if (p b) then [::] else
                let (a, b') := g b in a :: (ana h g p b')
    end.

(**
## Hylomorphism - ダミー変数を使って定義する。
*)
  Fixpoint hylo (h : nat) (c : A) (f : B -> A -> A)
           (g : A -> B * A) (p : pred A) (a : A) : A :=
    match h with
    | 0 => _a
    | h.+1 =>
      if (p a) then c else
        let (b, a') := g a in f b (hylo h c f g p a')
    end.
  
(**
## Paramorphism
*)
  Fixpoint numPara (b : B) (f : nat -> B -> B) (n : nat) : B := (* 数 *)
    match n with
    | 0 => b
    | n'.+1 => f n' (numPara b f n')
    end.

  Fixpoint listPara (b : B) (f : A -> (seq A) * B -> B) (s : seq A) : B := (* リスト *)
    match s with
    | [::] => b
    | a :: a' => f a (a', listPara b f a')
    end.

End Homomorphism.

Section Function.

  Variable A B : Type.
  Variable _a : A.                          (* ダミー値 *)
  Variable _b : B.                          (* ダミー値 *)
  
  Definition cataLength : seq A -> nat :=
    cata 0 (fun (_ : A) (n : nat) => n.+1).
  
  Definition cataFilter (p : pred A) : seq A -> seq A :=
    cata [::] (fun (a : A) (a' : seq A) => if (p a) then (a :: a') else a').
  
  Definition unsp (s : (seq A * seq B)) : (A * B) * (seq A * seq B) :=
    match s with
    | ((a :: a'), (b :: b')) => ((a, b), (a', b'))
    | _ => ((_a, _b), ([::], [::]))
    end.
  
  Definition fin (s : (seq A * seq B)) : bool :=
    match s with
    | ([::], _) => true
    | (_, [::]) => true
    | _ => false
    end.

  Definition anaZip h : seq A * seq B -> seq (A * B) := ana h unsp fin.
  
  Definition anaIterate (f : A -> A) : A -> seq A :=
    ana 10 (fun a => (a, f a)) xpred0.      (* (fun _ => false) *)
  
  Definition cataMap (f : A -> B) : seq A -> seq B :=
    cata [::] (fun a a' => (f a) :: a').
  
  Definition anaMap (f : A -> A) : seq A -> seq A :=
    ana 10
        (fun s => match s with
                  | a :: a' => (f a, a')
                  | _ => (_a, [::])
                  end)
        (* fun s => s == [::] ではエラーになる。  *)
        (fun s => match s with
                  | [::] => true
                  | _ => false
                  end).
  
  Definition hyloFact : nat -> nat :=
    hylo 0 10 1 muln (* 再帰のダミー変数 h=10 が尽きると 0 を返す。 *)
         (fun n => match n with
                   | n'.+1 => (n, n')
                   | _ => (0, 0)
                   end)
         (eq_op 0).
  
  Definition paraFact : nat -> nat := numPara 1 (fun n m => n.+1 * m).

  Definition paraTails : seq A -> seq (seq A) :=
    listPara ([:: [::]; [::]])
             (fun (a : A) (s : (seq A * seq (seq A))) =>
                let (s', tls) := s in (a :: s') :: tls).
  
End Function.

Section Examples.
  
  Compute cataLength [:: 1; 2; 3; 4].       (* 4 *)
  
  Compute cataFilter odd [:: 1; 2; 3; 4].   (* [:: 1; 3] *)
  
  Compute anaZip ([:: 1; 3; 5], [:: 2; 4; 6]). (* [:: (1, 2); (3, 4); (5, 6)] *)
  
  Compute anaIterate succn 0.  (* [:: 0; 1; 2; 3; 4; 5; 6; 7; 8; 9] *)
  
  Compute cataMap succn [:: 0; 1; 2; 3; 4]. (* [:: 1; 2; 3; 4; 5] *)

  Compute hyloFact 5.                       (* 120 *)
  
  Compute paraFact 5.                       (* 120 *)

  Compute paraTails [:: 1; 2; 3].

End Examples.

Section TH.

  Variable A B : Type.
  Variable _a : A.
  Variable _b : B.
  
  Lemma length_ok (s : seq A) : cataLength s = length s.
  Proof.
    rewrite /cataLength.
      by elim: s => //= a s ->.
  Qed.

  Lemma filter_ok (b : pred A) (s : seq A) : cataFilter b s = filter b s.
  Proof.
    rewrite /cataFilter.
      by elim: s => //= a s ->.
  Qed.
  
  Lemma fact_ok (n : nat) : paraFact n = n`!.
  Proof.
    rewrite /paraFact.
      by elim: n => //= n ->.
  Qed.
  
End TH.

(*
# ダミー変数のためにうまくいかないzipの証明
*)
Section NG.

  Variable A B : Type.
  Variable _a : A.
  Variable _b : B.
  
  Function myZip (s : seq A) (t : seq B) : seq (A * B):=
    match s with
    | [::] => [::]
    | x :: s' => match t with
                 | [::] => [::]
                 | y :: t' => (x, y) :: myZip s' t'
                 end
    end.
  
  Lemma l_zip_nil_l (h : nat) (t : seq B) :
    0 < h  ->
    ana h (unsp _a _b) (fin (B:=B)) ([::], t) = [::].
  Proof.
      by elim: h => //.
  Qed.
  
  Lemma l_zip_nil_r (h : nat) (s : seq A) :
    0 < h  ->
    ana h (unsp _a _b) (fin (B:=B)) (s, [::]) = [::].
  Proof.
    elim: h => // h IHh Hh.
  Admitted.
  
  Lemma l_zip (h : nat) (a : A) (b : B) (s : seq A) (t : seq B) :
    0 < h ->
    ana h.+1 (unsp _a _b) (fin (B:=B)) (a :: s, b :: t) =
    (a, b) :: ana h (unsp _a _b) (fin (B:=B)) (s, t).
  Proof.
      by elim: h => //.
  Qed.
  
  Lemma zip_ok (h : nat) (s : seq A) (t : seq B) :
    2 < h -> anaZip _a _b h (s, t) = myZip s t.
  Proof.
    move: h.
    rewrite /anaZip.
    functional induction (myZip s t) => h Hh1.
    - by rewrite l_zip_nil_l; last ssromega.
    - by rewrite l_zip_nil_r; last ssromega.
    - rewrite -(IHl h.-1) => //.
      + rewrite -l_zip. 
        * rewrite prednK.
          ** done.
          ** ssromega.
        * ssromega.
      + admit.
  Admitted.

End NG.

Compute myZip [:: 1; 3; 5] [:: 2; 4; 6].  (* = [:: (1, 2); (3, 4); (5, 6)] *)

(* END *)
