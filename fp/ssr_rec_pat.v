(* -*- coding: utf-8 -*- *)
(**
再帰のパターン

https://maoe.hatenadiary.jp/entry/20090820/1250782646

https://en.wikipedia.org/wiki/Anamorphism
 *)
From mathcomp Require Import all_ssreflect.
(* Require Import Recdef.                   (* Function *) *)

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
Anamorphism
 *)
  Fixpoint ana (h : nat) (g : B -> A * B) (p : B -> bool) (b : B) : seq A :=
    match h with
    | 0 => [::]
    | h.+1 => if (p b) then [::] else
                let (a, b') := g b in a :: (ana h g p b')
    end.

(**
Hylomorphism
*)
  Fixpoint hylo (h : nat) (c : A) f (g : A -> B * A) (p : A -> bool) (a : A) :=
    match h with
    | 0 => _a
    | h.+1 =>
      if (p a) then c else
        let (b, a') := g a in f b (hylo h c f g p a')
    end.

End Homomorphism.

Section Function.

  Variable A B : Type.
  Variable _a : A.                          (* ダミー値 *)
  Variable _b : B.                          (* ダミー値 *)
  
  Definition cataLength : seq A -> nat :=
    cata 0 (fun (_ : A) (n : nat) => n.+1).
  
  Definition cataFilter (p : A -> bool) : seq A -> seq A :=
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

  Definition anaZip : seq A * seq B -> seq (A * B) := ana 10 unsp fin.
  
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
    hylo 0 10 1 muln       (* ダミー変数 h=10 が尽きると 0 を返す。 *)
         (fun n => match n with
                   | n'.+1 => (n, n')
                   | _ => (0, 0)
                   end)
         (eq_op 0).
  
End Function.

Section Examples.
  
  Compute cataLength [:: 1; 2; 3; 4].       (* 4 *)
  
  Compute cataFilter odd [:: 1; 2; 3; 4].   (* [:: 1; 3] *)
  
  Compute anaZip ([:: 1; 3; 5], [:: 2; 4; 6]). (* [:: (1, 2); (3, 4); (5, 6)] *)
  
  Compute anaIterate succn 0.  (* [:: 0; 1; 2; 3; 4; 5; 6; 7; 8; 9] *)
  
  Compute cataMap succn [:: 0; 1; 2; 3; 4]. (* [:: 1; 2; 3; 4; 5] *)

  Compute hyloFact 5.                       (* 120 *)
  
End Examples.

(* END *)
