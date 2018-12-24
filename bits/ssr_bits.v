(* バイナリデータのタプル表現と集合表現 *)
(* @suharahiromichi *)

(* 参考：From Sets to Bits in Coq *)
(* coq-bits パッケージ、coq-bitset パッケージ *)

From mathcomp Require Import all_ssreflect.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Section Bits.

  Definition BITS n := n.-tuple bool.       (* タプル表現 *)
  Definition FSET n := {set 'I_n}.          (* 集合表現 *)
  
  Definition bits_data : BITS 4 := [tuple true; false; true; false].
  Definition fset_data : FSET 4 := [set inord 0; inord 2].
  
  (* タプル表現を集合表現に変換する関数。 *)
  Definition bs2fs {n} (bs : BITS n) := [set x : 'I_n | tnth bs x].
  
  (* タプル表現の要素と集合表現に要素が一致する補題。 *)
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
    apply/maxn_idPr.
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
  
End Bits.

(* END *)
