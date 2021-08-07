(** Backus' FP *)
(** @suharahiromicihi *)
(** 2021_08_05 *)

From mathcomp Require Import all_ssreflect.
Require Import ssrstring.                   (* Ascii String *)
Require Import ssrstar.                     (* S-EXP *)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(**
# FPの定義
*)
Section DEF_FP.

(**
## value
*)
Inductive value :=
| v_b (b : bool)
| v_n (n : nat)
| v_c (c : ascii)
| v_s (s : string).

Definition eqValue (x y : value) : bool :=
  match (x, y) with
  | (v_b x, v_b y) => x == y
  | (v_n x, v_n y) => x == y
  | (v_c x, v_c y) => x == y
  | (v_s x, v_s y) => x == y
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

Compute (v_n 1 == v_n 1).
Compute (v_n 1 == v_n 2).

(**
## object
*)
Definition sexp := star value.

(**
bottom は、None とする。
bottom は、リストの深いところに出現するわけでないことに、気づいてください。
 *)
Definition object := option sexp.

(**
## Intrinsic
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
  | Some (S_CONS (S_ATOM (v_n a)) (S_CONS (S_ATOM (v_n b)) S_NIL)) =>
    Some (S_ATOM (v_n (a + b)))
  | _ => None
  end.

Definition sub l :=
  match l with
  | Some (S_CONS (S_ATOM (v_n a)) (S_CONS (S_ATOM (v_n b)) S_NIL)) =>
    Some (S_ATOM (v_n (a - b)))
  | _ => None
  end.

Definition mul l :=
  match l with
  | Some (S_CONS (S_ATOM (v_n a)) (S_CONS (S_ATOM (v_n b)) S_NIL)) =>
    Some (S_ATOM (v_n (a * b)))
  | _ => None
  end.

Definition div l :=
  match l with
  | Some (S_CONS (S_ATOM (v_n a)) (S_CONS (S_ATOM (v_n b)) S_NIL)) =>
    Some (S_ATOM (v_n (a %/ b)))
  | _ => None
  end.

Definition atom (l : object) :=
  match l with
  | Some (S_CONS _ _) => Some (S_ATOM (v_b false))
  | Some (S_ATOM _ ) => Some (S_ATOM (v_b true))
  | _ => None
  end.

Definition equals (l : object) :=
  match l with
  | Some (S_CONS (S_ATOM (v_n a)) (S_CONS (S_ATOM (v_n b)) S_NIL)) =>
    Some (S_ATOM (v_b (a == b)))
  | _ => None
  end.

End DEF_FP.

(**
# test
*)

Definition test := Some (S_CONS (S_ATOM (v_n 0))
                                (S_CONS (S_ATOM (v_n 1))
                                        (S_CONS
                                           (S_CONS (S_ATOM (v_n 2)) S_Nil)
                                           S_Nil))).
Compute sel 1 test.
Compute sel 2 test.
Compute sel 3 test.
Compute sel 4 test.

Definition test2 := Some (S_CONS (S_ATOM (v_n 5))
                                 (S_CONS (S_ATOM (v_n 2))
                                         S_Nil)).

Definition test5 := Some (S_CONS (S_ATOM (v_n 5))
                                 (S_CONS (S_ATOM (v_n 5))
                                         S_Nil)).

Compute add test2.                       (* = Some (S_ATOM (v_n 7)) *)
Compute sub test2.                       (* = Some (S_ATOM (v_n 3)) *)
Compute mul test2.                       (* = Some (S_ATOM (v_n 10)) *)
Compute div test2.                       (* = Some (S_ATOM (v_n 2)) *)

Compute atom test2.                   (* = Some (S_ATOM (v_b false)) *)
Compute equals test2.                 (* = Some (S_ATOM (v_b false)) *)

Compute equals test5.                 (* = Some (S_ATOM (v_b true)) *)

(**
# seq to object
*)
Section FROM_TO_SEQ.

Fixpoint _from_list_bool (l : seq bool) : sexp :=
  match l with
  | [::] => S_Nil
  | a :: l => (S_CONS (S_ATOM (v_b a)) (_from_list_bool l))
  end.
Definition from_list_bool (l : seq bool) : object :=
  Some (_from_list_bool l).
Definition from_bool (x : bool) : object :=
  Some (S_ATOM (v_b x)).

Fixpoint _from_list_nat (l : seq nat) : sexp :=
  match l with
  | [::] => S_Nil
  | a :: l => (S_CONS (S_ATOM (v_n a)) (_from_list_nat l))
  end.
Definition from_list_nat (l : seq nat) : object :=
  Some (_from_list_nat l).
Definition from_nat (x : nat) : object :=
  Some (S_ATOM (v_n x)).

Fixpoint _from_list_ascii (l : seq ascii) : sexp :=
  match l with
  | [::] => S_Nil
  | a :: l => (S_CONS (S_ATOM (v_c a)) (_from_list_ascii l))
  end.
Definition from_list_ascii (l : seq ascii) : object :=
  Some (_from_list_ascii l).
Definition from_asicc (x : ascii) : object :=
  Some (S_ATOM (v_c x)).

Fixpoint _from_list_string (l : seq string) : sexp :=
  match l with
  | [::] => S_Nil
  | a :: l => (S_CONS (S_ATOM (v_s a)) (_from_list_string l))
  end.
Definition from_list_string (l : seq string) : object :=
  Some (_from_list_string l).
Definition from_string (x : string) : object :=
  Some (S_ATOM (v_s x)).

Fixpoint _from_list_list_nat (l : seq (seq nat)) : sexp :=
  match l with
  | [::] => S_Nil
  | a :: l => (S_CONS (_from_list_nat a) (_from_list_list_nat l))
  end.
Definition from_list_list_nat (l : seq (seq nat)) : object :=
  Some (_from_list_list_nat l).

Compute from_list_nat [:: 1; 2].
Compute from_list_list_nat [:: [:: 1; 2]; [:: 3; 4]].

End FROM_TO_SEQ.

(**
補題など
*)
Section LEMMAS.

Compute add (from_list_nat [:: 3; 5]).
Compute add (sel 1 (from_list_list_nat [:: [:: 1; 2]; [:: 1; 2]])).
Compute add (sel 2 (from_list_list_nat [:: [:: 1; 2]; [:: 1; 2]])).

Lemma add_ok x y : add (from_list_nat [:: x; y]) = from_nat (x + y).
Proof.
  done.
Qed.  

(**
## object の T は、bool の true とみなす。
 *)
Coercion is_object_true (x : object) : bool :=
  match x with
  | Some (S_CONS (S_ATOM (v_b a)) S_NIL) => a
  | _ => false
  end.

Lemma equals_ok x : equals (from_list_nat [:: x; x]).
Proof.
  done.
Qed.

End LEMMAS.

(* END *)
