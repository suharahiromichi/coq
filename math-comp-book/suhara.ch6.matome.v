(* まとめのまとめ。

Mathcomp で理解するべきなのは、Propとbooleanのリフレクションである。

(eqP) eqType では、 == と =
(forallP) finType では、[forall x, P] と (forall x, P)
(funP) finFun では、=1 と = (関数どうしの等しさ)
(setP) finSet では、=i と = (集合どうしの等しさ)
(permP) perm では、集合とおなじ。本文に記載なし。

それを以下にまとめる。

@suharahiromichi 2017/08/14
 *)

From mathcomp Require Import all_ssreflect.
From mathcomp Require Import perm.

(* Mathcomp book まとめ *)
(* Mathcomp の数学体系 --- Perm まで *)

(* ************************ *)
(* 5.3 Records as relations *)
(* ************************ *)
Definition bool_eqMixin' := @EqMixin bool eqb eqbP.
Canonical  bool_eqType'  := EqType bool bool_eqMixin'.

Definition nat_eqMixin'  := @EqMixin nat eqn (@eqnP).
Canonical  nat_eqType'   := EqType nat nat_eqMixin'.

Definition seq_eqMixin' (T : eqType) := @EqMixin (seq T) (@eqseq T) (@eqseqP T).
Canonical  seq_eqType'  (T : eqType) := EqType (seq T) (seq_eqMixin' T).

Definition prod_eqMixin' (T1 T2 : eqType) :=
  @EqMixin (T1 * T2) (pair_eq T1 T2) (@pair_eqP T1 T2).
Canonical  prod_eqType'  (T1 T2 : eqType) :=
  EqType (T1 * T2) (prod_eqMixin' T1 T2).

(* ************************* *)
(* 6.2.1 subtype kit (p.160) *)
(* eqtype.v                  *)
(* ************************* *)
(*
Section MySubTypeKit.
  Variables (T : Type) (P : pred T).
  
  Structure subType' : Type :=
    SubType' {
        sub_sort :> Type;                   (* projector *)
        val : sub_sort -> T;                (* constructor *)
        Sub : forall x, P x -> sub_sort;    (* constructor *)
        (* elimination rule for sub_sort *)
        _: forall K (_ : forall x Px, K (@Sub x Px)) u, K u;
        _: forall x Px, val (@Sub x Px) = x
      }.
End MySubTypeKit.

(* Implicit Arguments SubType' [T P]. *)

Notation "[ 'subType_' 'for' v ]" :=
  (SubType' _ v _
            (fun K K_S u => let (x, Px) as u return K u := u in K_S x Px)
            (fun x px => erefl x))
    (at level 0).
*)

(* ********************************* *)
(* 6.3 Finite types and their theory *)
(* ********************************* *)

Notation count_mem x := (count [pred y | y == x]).
Module finite.
  Definition axiom (T : eqType) (e : seq T) :=
    forall x : T, count_mem x e = 1.

  Record mixin_of (T : eqType) :=
    Mixin {
        enum : seq T;
        _ : axiom T enum;
      }.

(*
The axiom asserts that any inhabitant of T occurs exactly once in the enumeration e.

この公理は、Tの任意な要素が、列挙eに1回づづ出現すると主張している。
*)
  
  Check @card_uniqP :
    forall (T : finType) (s : seq T), reflect (#|s| = size s) (uniq s).
  Check @forallP :
    forall (T : finType) (P : pred T), reflect (forall x : T, P x) [forall x, P x].
  (* XXX_finType に関して、(forall x, P x) と [forall x, P x] のリフレクションができる。 *)

  (* is a boolean expression, it enables reasoning by excluded middle
  and also combines well with other boolean connectives. *)
  (* bool式であり、排中律などのboolenaな論理演算との組み合わせも可能である *)
End finite.

(* ******************************* *)
(* 6.4 The ordinal subtype (p.164) *)
(* ******************************* *)
Definition ordinal_eqMixin' (n : nat) := [eqMixin of (ordinal n) by <:].
(* (@val_eqP nat_eqType (fun x : nat => x < n) (ordinal_subType n)) *)
Canonical  ordinal_eqType'  (n : nat) := EqType (ordinal n) (ordinal_eqMixin' n).

(* 重複がないこと、漏れがないこと、から定義する。 *)
Definition ordinal_finMixin' (n : nat) :=
  @UniqFinMixin _ (ord_enum n) (ord_enum_uniq n) (@mem_ord_enum n).
Canonical  ordinal_finType'  (n : nat) :=
  FinType (ordinal n) (ordinal_finMixin' n).

(* finType に関して、uniq s と #|s|=size s のリフレクションができる。 *)
Goal forall s : seq (ordinal_finType' 3), size s = 3 -> uniq s.
  move=> s H.
  apply/card_uniqP.
  (* #|s| = size s *)
  Admitted.

Compute val (@Ordinal 4 3 (leqnn 3)).       (* 3 *)
Goal forall n, map val (ord_enum n) = iota 0 n.
Proof.
  move=> n.
  rewrite pmap_filter.
  + apply/all_filterP/allP => i. by rewrite mem_iota isSome_insub.
  + by apply: insubK.
Qed.

(* finType に関して、(forall x, P x) と [forall x, P x] のリフレクションができる。 *)
Goal [forall a : ordinal_finType' 3, a < 3].
    by apply/forallP.
Qed.

(* ************ *)
(* 6.1 n-tuples *)
(* ************ *)
Structure tuple_of' (n : nat) (T : Type) := (* サイズnのseq *)
  Tuple' {
      tval' :> seq T;
      _     : size tval' == n
    }.
Notation "n .-TUPLE" := (tuple_of' n) (at level 2, format "n .-TUPLE").
Check tval' : forall (n : nat) (T : Type), n.-TUPLE T -> seq T.

Canonical tuple_subType' (n : nat) (T : Type) := [subType for tval' n T].
(* オリジナルの [subType for _] を使用している。 *)

Definition tuple_eqMixin' (n : nat) (T : finType) := [eqMixin of n.-TUPLE T by <:].
(* (@val_eqP (seq_eqType T) (fun x : seq T => size x == n) (tuple_subType n T)) *)
Canonical  tuple_eqType'  (n : nat) (T : finType) :=
  EqType (n.-TUPLE T) (tuple_eqMixin' n T).

(* countType と enum (seq) から定義する。 *)
Definition tuple_finMixin' (n : nat) (T : finType) :=
  @FinMixin (tuple_countType n T) (FinTuple.enum n T) (@FinTuple.enumP n T).
Canonical  tuple_finType' (n : nat) (T : finType) :=
  FinType (tuple_countType n T) (tuple_finMixin' n T).

(* **************************** *)
(* 6.5 Finite functions (p.165) *)
(* **************************** *)
Inductive finfun_type' (aT : finType) (rT : Type) : predArgType :=
  Finfun' of #|aT|.-TUPLE rT.
Definition finfun_of' (aT : finType) (rT : Type) of phant (aT -> rT) :=
  finfun_type'.

Identity Coercion type_of_finfun' : finfun_of >-> finfun_type.

Definition fgraph' (aT : finType) (rT : Type) (f : finfun_type' aT rT) :=
  let: Finfun' t := f in t.
Canonical finfun_subType' (aT : finType) (rT : Type) :=
  [newType for fgraph' aT rT].

Notation "{ 'FFUN' fT }" := (finfun_type' fT).
(*
テキストの記載：

The actual definition in the Mathematical Components library is slightly
more complex to statically check that the domain is finite
using the tricks ex- plained in 5.11.
I.e. Coq rejects {ffun nat -> nat} but accepts {ffun ’I_7 -> nat}
 *)
(*
Inductive finfun' (aT : finType) (rT : Type) : Type :=
  Finfun' of #|aT|.-TUPLE rT.
Notation "{ 'FFUN' fT }" := (finfun' fT).
Definition fgraph' (aT : finType) (rT : Type) (f : {FFUN aT} rT) :=
  let: Finfun' t := f in t.
(* match f with | Finfun' t => t end. *)

Check fgraph' : forall (aT : finType) (rT : Type), { FFUN aT} rT -> #|aT|.-TUPLE rT.
Canonical  finfun_subType' (aT : finType) (rT : Type) := [newType for fgraph' aT rT].
*)

Definition finfun_eqMixin' (aT rT : finType) := [eqMixin of {FFUN aT} rT by <:].
(* (@val_eqP (tuple_eqType #|aT| rT) xpredT (finfun_subType aT rT)) *)
Canonical  finfun_eqType'  (aT rT : finType) := EqType ({FFUN aT} rT) (finfun_eqMixin' aT rT).

Definition finfun_finMixin' (aT rT : finType) := [finMixin of finfun_type aT rT by <:].
Canonical  finfun_finType'  (aT rT : finType) :=
  FinType (finfun_type aT rT) (finfun_finMixin' aT rT).

(* 
In standard mathematics functions that are point wise equal are
considered as equal. This principle, that we call functional
extensionality, is compatible with the Calculus of Inductive
Constructions but is not built-in.

functional extension はCICとコンパチブルだがCoqに組み込まれていない。

as expected, finite functions validate extensionality.
finfun では、それが成立する。

定義域の全てで値が(=)で等しいなら(=1)、関数として等しい(=)。逆も成立する。
*)

Definition eqfun {A B : Type} (f g : B -> A) : Prop := forall x, f x = g x. (* ssrfun.v *)
Notation "f1 =1 f2" := (eqfun f1 f2).
Check ffunP :
  forall (aT : finType) (rT : Type) (f1 f2 : {ffun aT -> rT}),
    f1 =1 f2 <-> f1 = f2.

(* ********** *)
(* 6.6 FinSet *)
(* ********** *)
Inductive set_type' (T : finType) : Type :=
  FinSet' of {ffun pred T}.                 (* FFUN XXXX *)
Notation "{ 'SET' T }" := (set_type' T).
Definition finfun_of_set' (T : finType) (A : {SET T}) :=
  let: FinSet' f := A in f.
(* match A with | FinSet' t => t end. *)
Check finfun_of_set' : forall T : finType, {SET T} -> {ffun pred T}. (* XXXX *)

Canonical  set_subType'     (T : finType) (A : {SET T}) := [newType for finfun_of_set' T].

Definition set_eqMixin'     (T : finType) := [eqMixin of {set T} by <:]. (* SET XXX *)
(* (@val_eqP (finfun_of_eqType T bool_eqType) xpredT (set_subType T)) *)
Canonical  set_eqType'      (T : finType) := EqType {set T} (set_eqMixin' T).

Definition set_finMixin'    (T     : finType) := [finMixin of {set T} by <:].
Canonical  set_finType'     (T     : finType) :=
  FinType {set T} (set_finMixin' T).

(* 集合の要素どうしが(=)で等しいなら(=i)、おなじ集合(=)。逆も成立する。 *)
Locate "_ =i _".                            (* eq_mem (mem A) (mem B) *)
Check setP : forall (T : finType) (A B : {set T}), A =i B <-> A = B. (* ssrbool.v *)

(* ******** *)
(* 6.7 Perm *)
(* ******** *)
Inductive perm_of' (T : finType) : Type :=
  Perm' (pval' : {ffun T -> T}) & injectiveb pval'. (* FFUN XXX *)
Notation "{ 'PERM' T }" := (perm_of' T).
Definition pval' (T : finType) (p : {PERM T}) :=
  let : Perm' f _ := p in f.

Canonical perm_subType' (T : finType) := [subType for pval' T].

Definition perm_eqMixin'   (T : finType) := [eqMixin of {PERM T} by <:].
(* (@val_eqP (finfun_of_eqType T T)
      (fun x : {ffun T -> T} => injectiveb (aT:=T) (rT:=T) x) 
      (perm_subType T)) *)
Canonical  perm_eqType'    (T : finType) := EqType {PERM T} (perm_eqMixin' T).

Definition perm_finMixin'   (T     : finType) := [finMixin of {perm T} by <:]. (* PERM XXXX *)
Canonical  perm_finType'    (T     : finType) :=
  FinType {perm T} (perm_finMixin' T).

(* Q.E.D. *)
