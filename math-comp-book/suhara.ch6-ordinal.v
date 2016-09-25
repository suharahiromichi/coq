From mathcomp Require Import all_ssreflect.

(* 6. Sub-Types Terms with properties *)
(* 6.4 The ordinal subtype *)

(*
Section MySubTypeKit.
  Variables (T : Type) (P : pred T).
  
  Structure subType : Type :=
    SubTypeKit {
        sub_sort :> Type;                   (* projector *)
        val : sub_sort -> T;                (* constructor *)
        Sub : forall x, P x -> sub_sort;    (* constructor *)
        (* elimination rule for sub_sort *)
        _: forall K (_ : forall x Px, K (@Sub x Px)) u, K u;
        _: forall x Px, val (@Sub x Px) = x
      }.

  Notation "[ ’subType’ ’for’ v ]" :=
    (SubType _ v _
             (fun K K_S u => let (x, Px) as u return K u := u in K_S x Px)
             (fun x px => erefl x)).
End MySubTypeKit.
*)
Section MyOrdinal.
  Variable n : nat.

  Inductive ordinal : Type := Ordinal m of m < n.

  Print Canonical Projections.
  Coercion nat_of_ord i := let: @Ordinal m _ := i in m. (* i : 'I_n *)
  (* _ は、H : m < n である。 *)
  Print Graph.
  (* [nat_of_ord] : ordinal >-> nat *)
  
  Canonical ordinal_subType := [subType for nat_of_ord].
  Print ordinal_subType.
  (*
    ordinal_subType = 
    [subType for nat_of_ord]
     : subType (T:=nat) (fun x : nat => x < n)
   *)
  Print Canonical Projections.
  (* nat_of_ord <- val ( ordinal_subType ) *)
  
  (* 次の定義には、カノニカルが必要 Canonical ordinal_subType。
     カノニカルにしないと、"SubEqMixin ?s" has type "Equality.mixin_of ?s"
     while it is expected to have type "Equality.mixin_of ordinal". *)
  Definition ordinal_eqMixin := Eval hnf in [eqMixin of ordinal by <:].
  Set Printing Coercions.
  Print ordinal_eqMixin.
  (*
ordinal_eqMixin = 
EqMixin (T:=ordinal) (op:=fun x y : ordinal => nat_of_ord x == nat_of_ord y)
  (@val_eqP nat_eqType (fun x : nat => x < n) ordinal_subType)
     : Equality.mixin_of ordinal
 *)
  
  Canonical ordinal_eqType := Eval hnf in EqType ordinal ordinal_eqMixin.
  Print Canonical Projections.
  (* ordinal <- sort ( ordinal_eqType ) *)

  Definition ord_enum : seq ordinal := pmap insub (iota 0 n).

  Check @pmap : forall aT rT : Type, (aT -> option rT) -> seq aT -> seq rT.
  (* 要素に関数(この場合は insub : aT -> option rT)を適用して、
     結果の Some x の Some を外し、None なら捨てる。 *)

  (* ord_enum n から値を取り出した結果は、自然数の0からn-1までのリストと等しい。 *)
  Lemma val_ord_enum : map val ord_enum = (iota 0 n).
  Proof.
    rewrite pmap_filter; last exact: insubK.
    by apply/all_filterP; apply/allP=> i; rewrite mem_iota isSome_insub.
  Qed.

  (* 以下の証明において、Canonical ordinal_eqType が必要。カノニカルにしないと、
  "ord_enum" has type "seq ordinal" while it is expected to have type "seq ?T". *)
  
  (* ordinal <- sort ( ordinal_eqType ) *)
  Check @uniq : forall T : eqType, seq T -> bool.
  Check ord_enum : seq ordinal.
  (* ordinal と sort (ordinal_eqType) = eqType のユニファイが可能になる。 *)
  
  (* ord_enum n の要素はユニークである。 *)
  Lemma ord_enum_uniq : uniq ord_enum.
  Proof.
      by rewrite pmap_sub_uniq ?iota_uniq.
  Qed.
  
  Lemma ord_inj : injective nat_of_ord.     (* fintype.v から転記 *)
  Proof.
    exact: val_inj.
  Qed.
  
  Lemma ltn_ord (i : ordinal) : i < n.      (* fintype.v から転記 *)
  Proof.
    exact: valP i.
  Qed.
  
  Lemma mem_ord_enum i : i \in ord_enum.
  Proof.
    Check pmap insub (iota 0 n).
    Check (mem_map ord_inj).
    rewrite -(mem_map ord_inj).
    rewrite val_ord_enum.
    rewrite mem_iota.
    rewrite add0n /=.
    Check ltn_ord.
    by apply ltn_ord.
  Qed.

End MyOrdinal.

(* Definition p1 : 'I_3. Proof. have : 1 < 3 by []. apply Ordinal. Defined. *)
Definition p1 := Ordinal 3 1 is_true_true.

Check @insub: forall (T : Type) (P : pred T) (sT : subType (T:=T) P), T -> option sT.
(* サブタイプに含まれるなら Some x、さもなければ None を返す。 *)
Print ordinal_subType.
Check (fun i : nat => i < 3).
Check (fun i : 'I_3 => i < 3).              (* カノニカル効くけど、それじゃない。 *)
Check @insub nat.
Check @insub nat (fun i : nat => i < 3).
Check @insub nat (fun i : nat => i < 3) (ordinal_subType 3).
Check @insub nat (fun i : nat => i < 3) (ordinal_subType 3) 1.
Check @insub nat (fun i : nat => i < 3) (ordinal_subType 3) 1 = Some p1.
Check insub 1 = Some p1.
Goal insub 1 = Some p1.
Proof.
  by rewrite insubT.
Qed.

(* *************** *)
Notation "''I_' n" := (ordinal n).
(* *************** *)

(* ******* *)
(* SUBTYPE *)
(* ******* *)

(*
  Definition ordinal_finMixin :=
    Eval hnf in UniqFinMixin ord_enum_uniq mem_ord_enum.
  
  Canonical ordinal_finType :=
    Eval hnf in FinType ordinal ordinal_finMixin.

*)

Lemma tnth_default {T n} (t : n.-tuple T) : 'I_n -> T.
Proof.
  rewrite -(size_tuple t).
  elim: (tval t).
  - case=> //=.
  - move=> a l H1 H2.
    done.
  Restart.
    by rewrite -(size_tuple t); case: (tval t) => [|//] [].
Qed.


Check @nth : forall T : Type, T -> seq T -> nat -> T.
Definition tnth T n (t : n.-tuple T) (i : 'I_n) : T :=
  nth (tnth_default t i) t i.
(* nth の最後の引数 nat に、 'I_n を与えている。 *)
(* nth の最後から二つ目の引数 seq T に、n.tuple T を与えている。 *)

Check tnth : forall (T : Type) (n : nat), n.-tuple T -> 'I_n -> T.

Lemma Hsize : size [::false;true;false] == 3. Proof. done. Qed.
Check Tuple Hsize.
Check tnth bool 3 (Tuple Hsize) p1 : bool.
Eval compute in tnth bool 3 (Tuple Hsize) p1. (* true *)

Check Tuple Hsize : 3.-tuple bool.
Check @tnth_default bool 3 (Tuple Hsize) p1 : bool.
Eval compute in @tnth_default bool 3 (Tuple Hsize) p1. (* bool型のなにか *)
Eval compute in tnth_default (Tuple Hsize) p1.         (* bool型のなにか *)
Eval compute in @nth bool (tnth_default (Tuple Hsize) p1) (Tuple Hsize) p1. (* true *)
Eval compute in nth _ (Tuple Hsize) p1. (* true *)
Eval compute in nth _ (Tuple Hsize) 1. (* true *)

(* END *)
