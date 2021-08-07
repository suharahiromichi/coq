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
Module Basic.

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
# Intrinsic
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

End Basic.

(**
# test
*)

Section Test.

Definition test := Some (S_CONS (S_ATOM (Basic.v_n 0))
                                (S_CONS (S_ATOM (Basic.v_n 1))
                                        (S_CONS
                                           (S_CONS (S_ATOM (Basic.v_n 2)) S_Nil)
                                           S_Nil))).
Compute Basic.sel 1 test.
Compute Basic.sel 2 test.
Compute Basic.sel 3 test.
Compute Basic.sel 4 test.

Definition test2 := Some (S_CONS (S_ATOM (Basic.v_n 5))
                                 (S_CONS (S_ATOM (Basic.v_n 2))
                                         S_Nil)).

Definition test5 := Some (S_CONS (S_ATOM (Basic.v_n 5))
                                 (S_CONS (S_ATOM (Basic.v_n 5))
                                         S_Nil)).

Compute Basic.add test2.                (* = Some (S_ATOM (v_n 7)) *)
Compute Basic.sub test2.                (* = Some (S_ATOM (v_n 3)) *)
Compute Basic.mul test2.                (* = Some (S_ATOM (v_n 10)) *)
Compute Basic.div test2.                (* = Some (S_ATOM (v_n 2)) *)

Compute Basic.atom test2.            (* = Some (S_ATOM (v_b false)) *)
Compute Basic.equals test2.          (* = Some (S_ATOM (v_b false)) *)
Compute Basic.equals test5.           (* = Some (S_ATOM (v_b true)) *)

(**
# seq to object
*)
Section FROM_TO_SEQ.

Fixpoint _from_list_bool (l : seq bool) : Basic.sexp :=
  match l with
  | [::] => S_Nil
  | a :: l => (S_CONS (S_ATOM (Basic.v_b a)) (_from_list_bool l))
  end.
Definition from_list_bool (l : seq bool) : Basic.object :=
  Some (_from_list_bool l).
Definition from_bool (x : bool) : Basic.object :=
  Some (S_ATOM (Basic.v_b x)).

Fixpoint _from_list_nat (l : seq nat) : Basic.sexp :=
  match l with
  | [::] => S_Nil
  | a :: l => (S_CONS (S_ATOM (Basic.v_n a)) (_from_list_nat l))
  end.
Definition from_list_nat (l : seq nat) : Basic.object :=
  Some (_from_list_nat l).
Definition from_nat (x : nat) : Basic.object :=
  Some (S_ATOM (Basic.v_n x)).

Fixpoint _from_list_ascii (l : seq ascii) : Basic.sexp :=
  match l with
  | [::] => S_Nil
  | a :: l => (S_CONS (S_ATOM (Basic.v_c a)) (_from_list_ascii l))
  end.
Definition from_list_ascii (l : seq ascii) : Basic.object :=
  Some (_from_list_ascii l).
Definition from_asicc (x : ascii) : Basic.object :=
  Some (S_ATOM (Basic.v_c x)).

Fixpoint _from_list_string (l : seq string) : Basic.sexp :=
  match l with
  | [::] => S_Nil
  | a :: l => (S_CONS (S_ATOM (Basic.v_s a)) (_from_list_string l))
  end.
Definition from_list_string (l : seq string) : Basic.object :=
  Some (_from_list_string l).
Definition from_string (x : string) : Basic.object :=
  Some (S_ATOM (Basic.v_s x)).

Fixpoint _from_list_list_nat (l : seq (seq nat)) : Basic.sexp :=
  match l with
  | [::] => S_Nil
  | a :: l => (S_CONS (_from_list_nat a) (_from_list_list_nat l))
  end.
Definition from_list_list_nat (l : seq (seq nat)) : Basic.object :=
  Some (_from_list_list_nat l).

Compute from_list_nat [:: 1; 2].
Compute from_list_list_nat [:: [:: 1; 2]; [:: 3; 4]].

End FROM_TO_SEQ.

(**
補題など
*)
Section LEMMAS.

Compute Basic.add (from_list_nat [:: 3; 5]).
Compute Basic.add (Basic.sel 1 (from_list_list_nat [:: [:: 1; 2]; [:: 1; 2]])).
Compute Basic.add (Basic.sel 2 (from_list_list_nat [:: [:: 1; 2]; [:: 1; 2]])).

Lemma add_ok x y : Basic.add (from_list_nat [:: x; y]) = from_nat (x + y).
Proof.
  done.
Qed.  

(**
## object の T は、bool の true とみなす。
 *)
Coercion is_object_true (x : Basic.object) : bool :=
  match x with
  | Some (S_CONS (S_ATOM (Basic.v_b a)) S_NIL) => a
  | _ => false
  end.

Lemma equals_ok x : Basic.equals (from_list_nat [:: x; x]).
Proof.
  done.
Qed.

End LEMMAS.

(**
# FPの定義 3
 *)
Section Program.

Inductive intrinsics :=
| add
| sub
| mul
| div
| atom
| equals
.

Inductive program :=
| intrin of intrinsics
| compos of program & program
| constr of program & program
| none                                      (* constr の基底 *)
.
        
Fixpoint Apply (p : program) (x : Basic.object) : Basic.object :=
  match p with
  | intrin add => Basic.add x
  | intrin sub => Basic.sub x
  | intrin mul => Basic.mul x
  | intrin div => Basic.div x
  | intrin atom => Basic.atom x
  | intrin equals => Basic.equals x
  | compos p1 p2 => Apply p1 (Apply p2 x)
  | constr p1 p2 =>
    match x with
    | Some (S_CONS x1 x2) =>
      match Apply p1 (Some x1) with
      | Some y1 =>
        match Apply p2 (Some x2) with
        | Some y2 => Some (S_CONS y1 y2)
        | None => None
        end
      | _ => None
      end
    | _ => None
    end
  | none => Some S_Nil                      (* constr の基底 *)
  end.

Definition test3 := from_list_list_nat [:: [:: 1; 2]; [:: 1; 2]].

Compute Apply (constr (intrin add)
                      (constr (intrin add)
                              none))
        test3.
Compute Apply (compos (intrin equals)
                      (constr (intrin add)
                              (constr (intrin add)
                                      none)))
        test3.

End Program.

(* END *)
