(* -*- coding: utf-8 -*- *)
(**
再帰のパターン

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
Catamorphism
*)
  Fixpoint cata (b : B) (f : A -> B -> B) (s : seq A) : B :=
    match s with
    | [::] => b
    | a :: a' => f a (cata b f a')
    end.
  
(**
Anamorphism - ダミー変数を使って定義する。
*)
  Fixpoint ana (h : nat) (g : B -> A * B) (p : pred B) (b : B) : seq A :=
    match h with
    | 0 => [::]
    | h.+1 => if (p b) then [::] else
                let (a, b') := g b in a :: (ana h g p b')
    end.

(**
Hylomorphism - ダミー変数を使って定義する。
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
Paramorphism
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

(**
https://mandel59.hateblo.jp/entry/2013/02/07/213230

https://mandel59.hateblo.jp/entry/2013/02/09/151347  
 *)
Require Import Coq.Lists.Streams.
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
  
(**
Streamどうしが等しいことを余帰納的に定義する述語
*)
  CoInductive EqSt (s1 s2 : Stream) : Prop :=
  | eqst : hd s1 = hd s2 -> EqSt (tl s1) (tl s2) -> EqSt s1 s2.
  
  CoFixpoint EqSt_reflex (s : Stream) : EqSt s s :=
    eqst (erefl (hd s)) (EqSt_reflex (tl s)).

End Streams.
*)
Section MyStreams.
  
  Variable A B : Type.

  CoFixpoint iterate (f : A -> A) (x : A) : Stream A :=
    Cons x (iterate f (f x)).

  Fixpoint takeStream (n : nat) (s : Stream A) : list A :=
    match n with
    | O => nil
    | S n1 => (hd s) :: takeStream n1 (tl s)
    end.
  
(**
Anamorphism - coFix で定義した。
 *)
  CoFixpoint unfold (f : B -> A * B) (b : B) : Stream A :=
    let (a, b') := f b in Cons a (unfold f b').

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

(* **************************************************** *)
(* **************************************************** *)
(*
ダミー変数のためにうまくいかないzipの証明
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

(* END *)
