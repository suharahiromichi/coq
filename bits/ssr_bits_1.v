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
  
(*
  coq-bitset/blob/master/src/repr_op.v などを参考に、
  タプル表現と集合表現の一致を証明する。
 *)

Section Repr.

  Definition repr' {n} (bs : BITS n) (fs : FSET n) :=
    forall (i : 'I_n), tnth bs i = (i \in fs).
  
  Definition repr {n} (bs : BITS n) (fs : FSET n) :=
    [set i : 'I_n | tnth bs i] = fs.
  
  Lemma reprs {n} (bs : BITS n) (fs : FSET n) : repr bs fs <-> repr' bs fs.
  Proof.
    rewrite /repr /repr'.
    split.
    - move=> <- i.
      by rewrite inE.
    - move=> H.
      apply/setP=> i'.
      by rewrite inE -H.
  Qed.
  
  (* ******** *)
  (* 変換関数 *)
  (* ******** *)
  
  (* タプル表現を集合表現に変換する関数。 *)
  Definition bs2fs {n} (bs : BITS n) : FSET n := [set x : 'I_n | tnth bs x].
  
  (* この変換関数を使った場合に、タプル表現の要素と集合表現に要素が一致する補題。 *)
  Lemma bs_eq_fs {n} (bs : BITS n) (fs : FSET n) : repr bs (bs2fs bs).
  Proof.
    apply/setP => i.
    now rewrite inE.
  Qed.
  
  (* ***** *)
  (* 長さ0 *)
  (* ***** *)
  
  Check [tuple] : BITS 0.
  Check set0 : FSET 0.
  Lemma zero_repr : repr [tuple] set0.
  Proof.
    apply/setP => i.
    by elim: i.
  Qed.
  
  (* *************** *)
  (* 全 true / false *)
  (* *************** *)
  
  (* 全 true *)
  Check (nseq_tuple 4 true) : BITS 4.
  Check [set: 'I_4] : FSET 4.
  
  Definition all_true {n} := nseq_tuple n true.
  Lemma all_true_repr {n} : repr all_true [set: 'I_n].
  Proof.
    apply/setP => i.
    rewrite !inE.
    Check (tnth_nth false (nseq_tuple n true) i) :
      tnth (nseq_tuple n true) i = nth false (nseq_tuple n true) i.
    rewrite (tnth_nth false).        (* nth の default は指定する。 *)
    
    Check nth_nseq.
    Check nth_nseq (nseq_tuple n true).
    rewrite nth_nseq.
    
    (* Goal : (if i < n then true else false) == true *)
    Check ltn_ord i.
    rewrite ltn_ord.
    done.
  Qed.
  
  (* 全 false *)
  Definition all_false {n} := nseq_tuple n false.
  Lemma all_false_repr {n} : repr (@all_false n) set0.
  Proof.
    apply/setP => i.
    by rewrite !inE (tnth_nth false) nth_nseq ltn_ord.
  Qed.
  

  (* **** *)
  (* inv  *)
  (* **** *)
  Lemma neg_neg a b : a == b -> ~~a == ~~b.
  Proof.
    by move/eqP => ->.
  Qed.
  
  Check fun x => negb x.
  Definition binv {n} (s : BITS n) :=
    map_tuple (fun x => negb x) s.
  Lemma binvP_repr {n} (bs : BITS n) (fs : FSET n) :
    repr bs fs -> repr (binv bs) (~: fs).
  Proof.
    move=> H1.
    apply reprs.
    apply reprs in H1.
    move=> i.
    move/eqP: (H1 i) => {H1} H1'.
    rewrite inE (tnth_nth false) /binv.
    rewrite (@nth_map bool false bool false).
    - apply/eqP.
      apply neg_neg.
      move/eqP in H1'.
        by rewrite -H1' !(tnth_nth false).
    -  by rewrite size_tuple.
  Qed.
  
  (* ****** *)
  (* and/or *)
  (* ****** *)
  Check fun x => andb x.1 x.2.
  Definition band {n} (s t : BITS n) :=
    map_tuple (fun x => andb x.1 x.2) (zip_tuple s t).
  Lemma bandP_repr {n} (bs bt : BITS n) (fs ft : FSET n) :
    repr bs fs -> repr bt ft -> repr (band bs bt) (fs :&: ft).
  Proof.
    move=> H1 H2.
    apply reprs.
    apply reprs in H1.
    apply reprs in H2.
    rewrite /repr'.
    rewrite /repr' in H1.
    rewrite /repr' in H2.
    
    move=> i.
    move: (H1 i) => {H1} H1'.
    move: (H2 i) => {H2} H2'.
    rewrite inE (tnth_nth false) /band.
    rewrite (@nth_map (bool * bool) (false, false) bool false).
    - rewrite !nth_zip.
      + by rewrite -H1' -H2' !(tnth_nth false).
      + by rewrite !size_tuple.
    - by rewrite size_tuple ltn_ord.
  Qed.
  
  Definition bor {n} (s t : BITS n) :=
    map_tuple (fun x => orb x.1 x.2) (zip_tuple s t).
  Lemma borP_repr {n} (bs bt : BITS n) (fs ft : FSET n) :
    repr bs fs -> repr bt ft -> repr (bor bs bt) (fs :|: ft).
  Proof.
    move=> H1 H2.
    apply reprs.
    apply reprs in H1.
    apply reprs in H2.
    rewrite /repr'.
    rewrite /repr' in H1.
    rewrite /repr' in H2.
    
    move=> i.
    move: (H1 i) => {H1} H1'.
    move: (H2 i) => {H2} H2'.
    rewrite inE (tnth_nth false) /bor.
    rewrite (@nth_map (bool * bool) (false, false) bool false).
    - rewrite !nth_zip.
      + by rewrite -H1' -H2' !(tnth_nth false).
      + by rewrite !size_tuple.
    - by rewrite size_tuple ltn_ord.
  Qed.
  
  (* ****** *)
  (* シフト *)
  (* ****** *)
  
  Check prednK : forall n : nat, 0 < n -> n.-1.+1 = n.
  (* H : 0 < n |- prednK H : n.=1.+1 = n *)

  (* 左シフト *)
  
  Compute rcons (behead [:: 0;1;2;3]) 9.    (* [:: 1;2;3;9] *)
  Compute behead (rcons [:: 0;1;2;3] 9).    (* [:: 1;2;3;9] *)

  (* tuple型の関数を組み合わせる場合  *)
  Definition shl1' {n} (bs : BITS n) : BITS n :=
    behead_tuple (rcons_tuple bs false).

  (* seq型の関数をtupleに適用できるようにする。 *)
  Lemma shl1P {n} (t : BITS n) : size (behead (rcons t false)) == n.
  Proof.
    by rewrite size_behead size_rcons -pred_Sn size_tuple.
  Qed.
  Canonical shl1 {n} t := Tuple (@shl1P n t).
  Check shl1 : BITS 4 -> BITS 4.
  
  (* 1 が 0 に移ること。 *)
  (* n.+1 が n に移ること。 *)
  (* coq-bitset/src/ops/shift.v 参照 *)

  Definition fset_shl1 {n} (fs : FSET n) (H : n.-1.+1 = n) : FSET n :=
    [set i : 'I_n | i < n.-1 & cast_ord H (@inord n.-1 i.+1) \in fs].
  (* シフトした後の、0〜n.-2 は、シフト前の 1〜n.-1 である。 *)
  (* シフトで追加される、シフト後の最右(bitn.-1)の値は、とりあえず不問とする。 *)
  
  Lemma shl1_repr n (bs : BITS n) (fs : FSET n) :
    forall (H : 0 < n), repr bs fs ->
                        repr (shl1 bs) (fset_shl1 fs (prednK H)).
  Proof.
    move=> H.
    move/setP => H1.
    apply/setP => i.
    move: (H1 i) => {H1} H1'.  
    rewrite inE (tnth_nth false) in H1'.
    rewrite inE (tnth_nth false) /shl1.
    case H2 : (i < n.-1).
    - admit.
    - admit.
  Admitted.
  
  
  (* 右シフト *)
  
  Compute belast 9 [:: 0;1;2;3].            (* [:: 9;0;1;2] *)
  Definition shr1 {n} : BITS n -> BITS n := belast_tuple false.
  Check shr1 : BITS 4 -> BITS 4.
  
(*
  Compute belast 9 [:: 0;1;2;3].            (* [:: 9;0;1;2] *)
  Compute 9 :: belast 0 [:: 1;2;3].
  Lemma test (x0 x : bool) s (i : nat) :
    nth false (belast x0 (x :: s)) i == nth false (x0 :: belast x s) i.
  Proof.
    done.
  Qed.
*)  
  (* おまけ *)
  Lemma nth_cat (s1 s2 : seq bool) (x0 : bool) (n : nat) :
    n < size s1 -> nth x0 (s1 ++ s2) n = nth x0 s1 n.
  Proof. by elim: s1 n => [|x s1 IHs] []. Qed.
  
  Lemma nth_cat' (s1 s2 : seq bool) (x0 : bool) (n : nat) :
    n >= size s1 -> nth x0 (s1 ++ s2) n = nth x0 s2 (n - size s1).
  Proof. by elim: s1 n => [|x s1 IHs] []. Qed.

  Lemma nth_cons (T : Type) (x0 : T) (a : T) (s : seq T) (i : nat) :
    0 < i -> nth x0 (a :: s) i = nth x0 s i.-1.
  Proof.
    by elim: s i => [|x s IHs]; case. 
  Qed.
  
  Lemma nth_belast_nil (x0 : bool) (i : nat) :
    0 < i -> nth false (belast x0 [::]) i = nth false [::] i.-1.
  Proof.
    move=> H.
    by rewrite /belast !nth_nil.
  Qed.
  
  Lemma nth_belast_cons (x0 x : bool) s (i : nat) :
    0 < i -> nth false (belast x0 (x :: s)) i = nth false (belast x s) i.-1.
  Proof.
    by elim: s i => [| a s IHs]; case.
  Qed.  
  
  Lemma nth_belast1' (x0 : bool) (s : seq bool) (i : nat) :
    nth false (belast x0 s) i.+1 = nth false s i.
  Admitted.
  
    Lemma nth_belast1 (x0 : bool) (s : seq bool) (i : nat) :
    0 < i -> nth false (belast x0 s) i = nth false s i.-1.
  Proof.
    elim: s i x0.
    - move=> i x0 H.
      by apply: nth_belast_nil.
    - move=> a s IHs i x0 H.
      Check nth_belast_cons false false s.
      rewrite nth_belast_cons.
      + Check @nth_cons bool false a s i.
        rewrite nth_cons.
        * Check (IHs i.-1 a).
          rewrite -(IHs i.-1 a).
          done.
        * Check leq0n.                      (* 0 <= n *)
          Search _ (_ < _).
          Search _ (0  _).
          admit.
      + admit.                              (* 0 < i.-1 *)
    - done.
  Admitted.
  
  (* 右シフトで追加される最左(bit0)は、falseである。 *)
  Lemma nth_belast2 (s : seq bool) (i : nat) :
    i = 0 -> nth false (belast false s) i = false.
  Proof.
    move=> ->.
    by elim: s.
  Qed.
  
  Definition fset_shr1 {n} (fs : FSET n) (H : n.-1.+1 = n) : FSET n :=
    [set i : 'I_n | 0 < i & cast_ord H (@inord n.-1 i.-1) \in fs].
  (* シフトした後の、1〜n.-1 は、シフト前の 0〜n.-2 である。 *)
  (* シフトで追加される、シフト後の最左(bit0)の値は、とりあえず不問とする。 *)
  
  (* i : 'I_n の半端ものの証明に使いそうである。 *)
  Lemma not_0lt__0 (i : nat) : (0 < i) = false -> i = 0.
  Proof.
    move=> H.
    rewrite lt0n in H.
    by move/eqP in H.
  Qed.
  
  Lemma shr1_repr n (bs : BITS n) (fs : FSET n) :
    forall (H : 0 < n), repr bs fs ->
                        repr (shr1 bs) (fset_shr1 fs (prednK H)).
  Proof.
    move=> H.
    move/setP => H1.
    apply/setP => i.
    move: (H1 (cast_ord (prednK H) (inord i.-1))) => {H1} H1'.  
    rewrite !inE (tnth_nth false) in H1'.
    rewrite !inE (tnth_nth false) /shr1 /fset_shr1.
    
    case H2 : (0 < i).
    - rewrite nth_belast1 /=.
      + rewrite -H1' /= inordK.
        * done.
        * rewrite !prednK.
          ** admit.
          ** admit.
        * done.
      + done.
    - rewrite nth_belast2 /=.
      + done.
      + by apply: not_0lt__0.
  Admitted.
  
  
  (* cons してから外す例。 *)
  (* n.+1.-1 は n と判断してくれる。 *)
  Compute behead (cons false [:: true; false]).
  Definition test' {n} (bs : BITS n) : BITS n :=
    behead_tuple (cons_tuple false bs).
  
  (* drop はかならず 1 とは限らないため、tcast が必要になる。 *)
  Lemma n1_1_n n : n.+1 - 1 = n.
  Proof.
    by rewrite subn1 -pred_Sn.
  Qed.
  Check behead_tuple.

  Compute drop 1 (cons false [:: true; false]).
  Definition test {n} (bs : BITS n) : BITS n :=
    tcast (n1_1_n n)
      (@drop_tuple n.+1 1 bool (cons_tuple false bs)).
End Repr.  

(* END *)
