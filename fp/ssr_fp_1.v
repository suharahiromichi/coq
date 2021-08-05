(** Backus' FP *)
(** @suharahiromicihi *)
(** 2021_08_05 *)

From mathcomp Require Import all_ssreflect.
Require Import ssrstring.                   (* Ascii String *)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(**
list
*)
Inductive list T : Type :=
| S_ATOM of T
| S_CONS of T & list T.

Fixpoint eqList {T : eqType} (x y : list T) : bool :=
  match (x, y) with
  | (S_ATOM a, S_ATOM b) => a == b          (* eqType *)
  | (S_CONS x1 y1, S_CONS x2 y2) => (x1 == x2) && eqList y1 y2
  | _ => false
  end.

Lemma eqCons {T : eqType} (x x' : T) (y y' : list T) :
  (x = x' /\ y = y') -> @S_CONS T x y = @S_CONS T x' y'.
Proof.
  case=> Hx Hy.
    by rewrite Hx Hy.
Qed.

Lemma list_eqP : forall (T : eqType) (x y : list T), reflect (x = y) (eqList x y).
Proof.
  move=> T x y.
  apply: (iffP idP).
  - elim: x y => //= x.
    case=> //=.
    + by move=> y /eqP <-.
    + move=> y1 IHy1.
        by case=> //= x1 y2 /andP [] /eqP <- /IHy1 <-.
  - move=> <-.
    elim: x => x /=.
    + by apply/eqP.
    + move=> l IHl.
      apply/andP.
        by split.
Qed.

Definition list_eqMixin (T : eqType) := EqMixin (@list_eqP T).
Canonical list_eqType (T : eqType) := EqType (list T) (list_eqMixin T).

(**
value
*)
Inductive value :=
| vb (b : bool)
| vn (n : nat)
| vc (c : ascii)
| vs (s : string)
| vbottom                                    (* bottom *)
.

(*
Definition eqValue (x y : value) : bool :=
  match (x, y) with
  | (vb x, vb y) => x == y
  | (vn x, vn y) => x == y
  | (vc x, vc y) => x == y
  | (vs x, vs y) => x == y
  | (vbottom, vbottom) => true
  | _ => false
  end.
                           
Lemma value_eqP : forall (x y : value), reflect (x = y) (eqValue x y).
Proof.
  move=> x y.
  apply: (iffP idP).
  - case: x.
    + case: y.
      * move=> b1 b2.
          by rewrite /eqValue => /eqP ->.
      * by rewrite /eqValue.
      * by rewrite /eqValue.
      * by rewrite /eqValue.
      * by rewrite /eqValue.
    + case: y.
      * by rewrite /eqValue.
      * move=> n1 n2.
          by rewrite /eqValue => /eqP ->.
      * by rewrite /eqValue.
      * by rewrite /eqValue.
      * by rewrite /eqValue.
    + case: y.
      * by rewrite /eqValue.
      * by rewrite /eqValue.
      * move=> c1 c2.
          by rewrite /eqValue => /eqP ->.
      * by rewrite /eqValue.
      * by rewrite /eqValue.
    + case: y.
      * by rewrite /eqValue.
      * by rewrite /eqValue.
      * by rewrite /eqValue.
      * move=> s1 s2.
          by rewrite /eqValue => /eqP ->.
      * by rewrite /eqValue.
    + case: y.
      * by rewrite /eqValue.
      * by rewrite /eqValue.
      * by rewrite /eqValue.
      * by rewrite /eqValue.
      * by rewrite /eqValue.
  - move=> <-.
    case: x.
    + move=> b.
        by rewrite /eqValue.
    + move=> n.
        by rewrite /eqValue.
    + move=> c.
        by rewrite /eqValue.
    + move=> s.
        by rewrite /eqValue.
    + by rewrite /eqValue.
Qed.

Definition value_eqMixin := EqMixin value_eqP.
Canonical value_eqType := EqType value value_eqMixin.

Compute (vn 1 == vn 1).
Compute (vn 1 == vn 2).
*)

(**
data
*)
Definition data := list value.
Definition S_NIL := S_ATOM vbottom.

(**
Intrinsic
*)
Record intrinsic :=
  mkfunc {
      func : data -> data;
      unit : data
    }.

Fixpoint _sel n l :=
  match (n, l) with
  | (1, S_CONS t l) => t
  | (n.+1, S_CONS t l) => _sel n l
  | (_, _) => vbottom
  end.
Compute _sel 1 (S_CONS (vn 0) (S_CONS (vn 1) (S_CONS (vn 2) S_NIL))).
Compute _sel 2 (S_CONS (vn 0) (S_CONS (vn 1) (S_CONS (vn 2) S_NIL))).
Compute _sel 3 (S_CONS (vn 0) (S_CONS (vn 1) (S_CONS (vn 2) S_NIL))).
Compute _sel 4 (S_CONS (vn 0) (S_CONS (vn 1) (S_CONS (vn 2) S_NIL))).

Definition sel n :=                         (* n は自然数でメタ変数 *)
  {| func l := S_ATOM (_sel n l);
     unit := S_ATOM vbottom
  |}.

Definition tl :=
  {|
    func l := match l with
              | S_CONS t l => l
              | _ => S_ATOM vbottom
              end;
     unit := S_ATOM vbottom
  |}.

Definition id :=
  {|
    func l := l;
    unit := S_ATOM vbottom
  |}.

Definition add :=
  {|
    func l := match l with
              | S_CONS (vn a) (S_CONS (vn b) S_NIL) => S_ATOM (vn (a + b))
              | _ => S_ATOM vbottom
              end;
    unit := S_ATOM (vn 0)
  |}.
Compute func add (S_CONS (vn 1) (S_CONS (vn 2) S_NIL)).

Definition sub :=
  {|
    func l := match l with
              | S_CONS (vn a) (S_CONS (vn b) S_NIL) => S_ATOM (vn (a - b))
              | _ => S_ATOM vbottom
              end;
     unit := S_ATOM (vn 0)
  |}.

Definition mul :=
  {|
    func l := match l with
              | S_CONS (vn a) (S_CONS (vn b) S_NIL) => S_ATOM (vn (a * b))
              | _ => S_ATOM vbottom
              end;
     unit := S_ATOM (vn 1)
  |}.

Definition div :=
  {|
    func l := match l with
              | S_CONS (vn a) (S_CONS (vn b) S_NIL) => S_ATOM (vn (a %/ b))
              | _ => S_ATOM vbottom
              end;
     unit := S_ATOM (vn 1)
  |}.

Definition atom :=
  {|
    func l := match l with
              | S_CONS t l => S_ATOM (vb false)
              | _ => S_ATOM (vb true)
              end;
     unit := S_ATOM vbottom
  |}.

(* equals <bottom, bottom> = bottom とする。 *)
Definition equals :=
  {|
    func l := match l with
              | S_CONS (vb a) (S_CONS (vb b) S_NIL) => S_ATOM (vb (a == b))
              | S_CONS (vn a) (S_CONS (vn b) S_NIL) => S_ATOM (vb (a == b))
              | S_CONS (vc a) (S_CONS (vc b) S_NIL) => S_ATOM (vb (a == b))
              | S_CONS (vs a) (S_CONS (vs b) S_NIL) => S_ATOM (vb (a == b))
              | _ => S_ATOM vbottom
              end;
     unit := S_ATOM vbottom
  |}.

(* END *)
