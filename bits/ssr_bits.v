(* バイナリデータのタプル表現と集合表現 *)
(* @suharahiromichi *)

(* 参考：From Sets to Bits in Coq *)
(* coq-bits パッケージ、coq-bitset パッケージ *)

From mathcomp Require Import all_ssreflect.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Definition BITS n := n.-tuple bool.         (* タプル表現 *)
Definition FSET n := {set 'I_n}.            (* 集合表現 *)

Definition bits_data : BITS 4 := [tuple true; false; true; false].
Definition fset_data : FSET 4 := [set inord 0; inord 2].
  
Section Bits.
  
  (* タプルの要素の書き換えでサイズが変わらない補題 *)
  Check size_set_nth.           (* 要素が増えることを考慮している。 *)
  (* seqのset_nthでは要素が増えるが、タプルならインデクスがnで抑えられる。 *)
  Lemma set_nth_tupleP (n : nat) (T : Type)
        (x0 : T) (t : n.-tuple T) (i : 'I_n) (x : T) :
    size (set_nth x0 t i x) = n.
  Proof.
    case: t => t H /=.
    rewrite size_set_nth.
    move/eqP in H.
    rewrite H.
    (* maxn i.+1 n = n *)
    apply/maxn_idPr.
    (* i < n *)
    now apply ltn_ord.
  Qed.
  
  (* タプルの任意の要素を書き換える関数。tcastを使う際にサイズが変化ない証明を与える。 *)
  Definition set_tnth {n} (T : Type) (x0 : T)
             (t : n.-tuple T) (i : 'I_n) (x : T) :=
    tcast (@set_nth_tupleP n T x0 t i x) (in_tuple (set_nth x0 t i x)).
  Check @set_tnth :
    forall (n : nat) (T : Type), T -> n.-tuple T -> 'I_n -> T -> n.-tuple T.
  
  (* タプル表現の任意の要素をセットする。 *)
  Definition bsets {n} (bs : BITS n) (i : 'I_n) : BITS n :=
    set_tnth false bs i true.
  
  (* 集合表現の任意の要素をセットする。 *)
  Definition bsetr {n} (bs : FSET n) (i : 'I_n) : FSET n := i |: bs.
  
  (* 集合表現で、データ幅を増やす関数。 *)
  (* 数値はそのまま *)
  Definition lcast {n} (m : nat) (bs : {set 'I_n}) : {set 'I_(n + m)} :=
    [set lshift m x | x in bs].
  Check lcast 4 fset_data : FSET 8.
  (* 数値に m を加算する。 *)
  Definition rcast {n} (m : nat) (bs : {set 'I_n}) : {set 'I_(m + n)} :=
    [set rshift m x | x in bs].
  Check rcast 4 fset_data : FSET 8.
  
  (* これの逆はうまくいかない。 *)
  Definition fset_data2 : FSET 6 := [set inord 0; inord 2; inord 4].
  Definition x2 := [set @split 4 2 x | x in fset_data2] : {set 'I_4 + 'I_2}.
  Definition test {m n} (i : 'I_m + 'I_n) : ('I_m + unit) :=
    match i with
    | inl i' => inl i'
    | inr i' => inr tt
    end.
  Check [set test x | x in x2] : {set 'I_4 + unit}.
End Bits.
  
(*
  coq-bitset/blob/master/src/repr_op.v などを参考に、
  タプル表現と集合表現の一致を証明する。
 *)

Section Repr.

  (* タプル表現を集合表現に変換する関数。 *)
  Definition bs2fs {n} (bs : BITS n) := [set x : 'I_n | tnth bs x].
  
  (* この変換関数を使った場合に、タプル表現の要素と集合表現に要素が一致する補題。 *)
  Lemma bs_eq_fs {n} (bs : BITS n) (fs : FSET n) :
    forall (i : 'I_n), bs2fs bs = fs -> tnth bs i = (i \in fs).
  Proof.
    Locate "[ set _ | _ ]".
    Search _ ([ set _ : _ | _ ]).
    Check inE.
    rewrite /bs2fs.
    move=> i <-.
    now rewrite inE.
  Qed.
  
  (* ゼロが一致する証明 *)
  Check [tuple] : BITS 0.
  Check set0 : FSET 0.
  Lemma zero_repr : forall (i : 'I_0), tnth [tuple] i = (i \in set0).
  Proof.
    now elim.
  Qed.
  
End Repr.  

(* END *)
