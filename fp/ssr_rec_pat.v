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
    | h.+1 => let (a, b') := g b in
              if (p b) then [::] else a :: (ana h g p b')
    end.

End Homomorphism.

Section Function.

  Variable T S : Type.
  Variable d : T.                           (* ダミー値 *)
  
  Definition cataLength : seq _ -> nat :=
    cata 0 (fun (_ n : nat) => n.+1).
  
  Definition cataFilter (p : _ -> bool) : seq nat -> seq nat :=
    cata [::] (fun (a : nat) (a' : seq nat) => if (p a) then (a :: a') else a').

  Definition unsp (s : (seq nat * seq nat)) : (nat * nat) * (seq nat * seq nat) :=
    match s with
    | ((a :: a'), (b :: b')) => ((a, b), (a', b'))
    | _ => ((0, 0), ([::], [::]))
    end.
  
  Definition fin (s : (seq nat * seq nat)) : bool :=
    match s with
    | ([::], _) => true
    | (_, [::]) => true
    | _ => false
    end.

  Definition anaZip := ana 10 unsp fin.

  Definition anaIterate (f : T -> T) :=
    ana 10 (fun a => (a, f a)) xpred0.      (* (fun _ => false) *)
  
  Definition cataMap (f : T -> S) :=
    cata [::] (fun a a' => (f a) :: a').
  
  Definition anaMap (f : T -> T) :=
    ana 10
        (fun s => match s with
                  | a :: a' => (f a, a')
                  | _ => (d, [::])
                  end)
        (* fun s => s == [::] ではエラーになる。  *)
        (fun s => match s with
                  | [::] => true
                  | _ => false
                  end).
End Function.

Section Examples.
  
  Compute cataLength [:: 1; 2; 3; 4].       (* 4 *)
  Compute cataFilter odd [:: 1; 2; 3; 4].   (* [:: 1; 3] *)
  Compute anaZip ([:: 1; 3; 5], [:: 2; 4; 6]). (* [:: (1, 2); (3, 4); (5, 6)] *)
  Compute anaIterate succn 0.  (* [:: 0; 1; 2; 3; 4; 5; 6; 7; 8; 9] *)
  Compute cataMap succn [:: 0; 1; 2; 3; 4]. (* [:: 1; 2; 3; 4; 5] *)

End Examples.

(* END *)
