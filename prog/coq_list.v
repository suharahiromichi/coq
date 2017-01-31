Require Import Omega.
Require Import List.
Require Import Arith.
Require Import Program.

Set Implicit Arguments.

Section List.
  Variable A : Type.
  
  (* l <> [] は Obligationに必要 *)
  Program Definition hd (l : list A | l <> []) :
    { a : A | exists l', a :: l' = l } :=
    match l with
    | [] => !
    | a :: l' => a
    end.
  Obligation 2.
  Proof.
    now exists l'.
  Defined.

  Program Definition tl (l : list A | l <> []) :
    { l' : list A | exists a, a :: l' = l } :=
    match l with
    | [] => !
    | a :: l' => l'
    end.
  Obligation 2.
  Proof.
    now exists a.
  Defined.

End List.

Extraction hd.                        (** val hd : 'a1 list -> 'a1 **)
(*
let hd = function
| Nil -> assert false (* absurd case *)
| Cons (a, _) -> a
*)

Extraction tl.                   (** val tl : 'a1 list -> 'a1 list **)
(*
let tl = function
| Nil -> assert false (* absurd case *)
| Cons (_, l') -> l'
*)

(* END *)
