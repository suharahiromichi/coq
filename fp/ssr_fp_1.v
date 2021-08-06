(** Backus' FP *)
(** @suharahiromicihi *)
(** 2021_08_05 *)

From mathcomp Require Import all_ssreflect.
Require Import ssrstring.                   (* Ascii String *)
Require Import ssrstar.                     (* S-EXP *)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Inductive value :=
| vb (b : bool)
| vn (n : nat)
| vc (c : ascii)
| vs (s : string).

Definition eqValue (x y : value) : bool :=
  match (x, y) with
  | (vb x, vb y) => x == y
  | (vn x, vn y) => x == y
  | (vc x, vc y) => x == y
  | (vs x, vs y) => x == y
  | _ => false
  end.
                           
Lemma value_eqP (x y : value) : reflect (x = y) (eqValue x y).
Proof.
  apply: (iffP idP).
  - case: x;
      case: y;
      rewrite /eqValue //=;
        by move=> b1 b2 /eqP ->.
  - move=> <-.
    case: x;
      by rewrite /eqValue.
Qed.

Definition value_eqMixin := EqMixin value_eqP.
Canonical value_eqType := EqType value value_eqMixin.

Compute (vn 1 == vn 1).
Compute (vn 1 == vn 2).

(**
object
*)
Definition sexp := star value.

(**
bottom は、None とする。
bottom は、リストの深いところに出現するわけでないことに、気づいてください。
 *)
Definition object := option sexp.

(**
Intrinsic
*)

Fixpoint _sel n l : object :=
  match (n, l) with
  | (1, S_CONS t l) => Some t
  | (n.+1, S_CONS t l) => _sel n l
  | (_, _) => None
  end.

Definition sel n (l : object) :=
  match l with
  | Some l => _sel n l
  | None => None
  end.

Definition tl (l : object) :=
  match l with
  | Some (S_CONS _ l) => Some l
  | _ => None
  end.

Definition id (l : object) := l.

Definition add l := 
  match l with
  | Some (S_CONS (S_ATOM (vn a)) (S_CONS (S_ATOM (vn b)) S_NIL)) =>
    Some (S_ATOM (vn (a + b)))
  | _ => None
  end.

Definition sub l :=
  match l with
  | Some (S_CONS (S_ATOM (vn a)) (S_CONS (S_ATOM (vn b)) S_NIL)) =>
    Some (S_ATOM (vn (a - b)))
  | _ => None
  end.

Definition mul l :=
  match l with
  | Some (S_CONS (S_ATOM (vn a)) (S_CONS (S_ATOM (vn b)) S_NIL)) =>
    Some (S_ATOM (vn (a * b)))
  | _ => None
  end.

Definition div l :=
  match l with
  | Some (S_CONS (S_ATOM (vn a)) (S_CONS (S_ATOM (vn b)) S_NIL)) =>
    Some (S_ATOM (vn (a %/ b)))
  | _ => None
  end.

Definition atom (l : object) :=
  match l with
  | Some (S_CONS _ _) => Some (S_ATOM (vb false))
  | Some (S_ATOM _ ) => Some (S_ATOM (vb true))
  | _ => None
  end.

Definition equals (l : object) :=
  match l with
  | Some (S_CONS (S_ATOM (vn a)) (S_CONS (S_ATOM (vn b)) S_NIL)) =>
    Some (S_ATOM (vb (a == b)))
  | _ => None
  end.


(**
test
*)

Definition test := Some (S_CONS (S_ATOM (vn 0))
                                (S_CONS (S_ATOM (vn 1))
                                        (S_CONS
                                           (S_CONS (S_ATOM (vn 2)) S_Nil)
                                           S_Nil))).
Compute sel 1 test.
Compute sel 2 test.
Compute sel 3 test.
Compute sel 4 test.

Definition test2 := Some (S_CONS (S_ATOM (vn 5))
                                 (S_CONS (S_ATOM (vn 2))
                                         S_Nil)).

Definition test5 := Some (S_CONS (S_ATOM (vn 5))
                                 (S_CONS (S_ATOM (vn 5))
                                         S_Nil)).

Compute add test2.                       (* = Some (S_ATOM (vn 7)) *)
Compute sub test2.                       (* = Some (S_ATOM (vn 3)) *)
Compute mul test2.                       (* = Some (S_ATOM (vn 10)) *)
Compute div test2.                       (* = Some (S_ATOM (vn 2)) *)

Compute atom test2.                   (* = Some (S_ATOM (vb false)) *)
Compute equals test2.                 (* = Some (S_ATOM (vb false)) *)

Compute equals test5.                 (* = Some (S_ATOM (vb true)) *)

(* END *)
