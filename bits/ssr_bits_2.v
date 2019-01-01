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
  Check fun x => negb x.
  Definition binv {n} (s : BITS n) :=
    map_tuple (fun x => negb x) s.
  Lemma binvP_repr {n} (bs : BITS n) (fs : FSET n) :
    repr bs fs -> repr (binv bs) (~: fs).
  Proof.
    move/setP => H1.
    apply/setP => i.
    move: (H1 i) => {H1} H1.
    rewrite !inE !(tnth_nth false) in H1.
    rewrite !inE !(tnth_nth false) /binv.
    rewrite (@nth_map bool false bool false).
    - by rewrite H1.                        (* rewrite in_setC *)
    - by rewrite size_tuple.
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
    move/setP => H1.
    move/setP => H2.
    apply/setP => i.
    
    move: (H1 i) => {H1} H1.
    move: (H2 i) => {H2} H2.
    
    rewrite inE (tnth_nth false) in H1.
    rewrite inE (tnth_nth false) in H2.
    rewrite inE (tnth_nth false) /band.     (* and *)
    rewrite (@nth_map (bool * bool) (false, false) bool false).
    
    - rewrite !nth_zip.
      + by rewrite in_setI -H1 -H2.         (* setI *)
      + by rewrite !size_tuple.
    - by rewrite size_tuple ltn_ord.
  Qed.
  
  Definition bor {n} (s t : BITS n) :=
    map_tuple (fun x => orb x.1 x.2) (zip_tuple s t).
  Lemma borP_repr {n} (bs bt : BITS n) (fs ft : FSET n) :
    repr bs fs -> repr bt ft -> repr (bor bs bt) (fs :|: ft).
  Proof.
    move/setP => H1.
    move/setP => H2.
    apply/setP => i.
    
    move: (H1 i) => {H1} H1.
    move: (H2 i) => {H2} H2.
    
    rewrite inE (tnth_nth false) in H1.
    rewrite inE (tnth_nth false) in H2.
    rewrite inE (tnth_nth false) /bor.      (* or *)
    rewrite (@nth_map (bool * bool) (false, false) bool false).
    
    - rewrite !nth_zip.
      + by rewrite in_setU -H1 -H2.         (* setU *)
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

  Definition shl1_seq bs := behead (rcons bs false).
  
  (* 1 が 0 に移ること。 *)
  (* n.+1 が n に移ること。 *)
  (* coq-bitset/src/ops/shift.v 参照 *)

  Lemma nth_shl1 (n : nat) (a : bool) (s : seq bool) (i : nat) :
    i < n.-1 -> nth false (shl1_seq (a :: s)) i = nth false (shl1_seq s) i.-1.
  Proof.
  Admitted.
  
  Lemma nth_shl1_1 (n : nat) (s : seq bool) (i : nat) :
    i = n.-1 -> nth false (behead (rcons s false)) i = false.
  Proof.
  Admitted.
  
  Lemma nth_shl1_n (n : nat) (s : seq bool) (i : nat) :
    i < n.-1 -> nth false (shl1_seq s) i = nth false s i.+1.
  Proof.
  Admitted.
  
  Definition fset_shl1 {n} (fs : FSET n) (H : n.-1.+1 = n) : FSET n :=
    [set i : 'I_n | i < n.-1 & cast_ord H (@inord n.-1 i.+1) \in fs].
  (* シフトした後の、0〜n.-2 は、シフト前の 1〜n.-1 である。 *)
  (* シフトで追加される、シフト後の最右(bitn.-1)の値は、とりあえず不問とする。 *)
  
  Lemma pltn__not_1lt__n_1 n i : i < n -> i < n.-1 = false -> i = n.-1.
    elim: i.
  Admitted.
  
  Lemma shl1_repr n (bs : BITS n) (fs : FSET n) :
    forall (H : 0 < n), repr bs fs ->
                        repr (shl1 bs) (fset_shl1 fs (prednK H)).
  Proof.
    move=> H.
    move/setP => H1.
    apply/setP => i.
    
    move: (H1 (cast_ord (prednK H) (inord i.+1))) => {H1} H1'.
    
    rewrite !inE (tnth_nth false) in H1'.
    rewrite !inE (tnth_nth false) /fset_shl1.
    
    case Hi : (i < n.-1).
    - rewrite (@nth_shl1_n n).
      + rewrite -H1' /=.
        Check inordK.
        rewrite inordK.
        * done.
        * by apply Hi.                      (* i.+1 < n.-1.+1 *)
      + done.
    - rewrite -H1' /=.
      Check @nth_shl1_1 n bs.
      rewrite (@nth_shl1_1 n).
      + done.
      + apply pltn__not_1lt__n_1.
        * done.
        * done.
  Qed.
  
  (* 右シフト *)
  
  (* i : 'I_n の半端ものの証明に使いそうである。 *)
  Lemma not_0lt__0 (i : nat) : (0 < i) = false -> i = 0.
  Proof.
    move=> H.
    rewrite lt0n in H.
    by move/eqP in H.
  Qed.
  
  Lemma p0lt__not_1lt__1 i : 0 < i -> 0 < i.-1 = false -> i = 1.
    elim: i.
    + done.
    + move=> i IHi H1 H2.
      Check @not_0lt__0 i.+1.-1.
      apply (@not_0lt__0 i.+1.-1) in H2.
      rewrite PeanoNat.Nat.pred_succ in H2.
      by rewrite H2.
  Qed.
  
  Definition shr1_seq := belast false.
  Compute shr1_seq [::].
  Compute shr1_seq [:: true].
  Compute shr1_seq [:: true; true].
  Compute shr1_seq [:: true; true; true].
  
  Lemma shr1P {n} (t : BITS n) : size (shr1_seq t) == n.
  Proof.
    by rewrite size_belast size_tuple.
  Qed.
  Canonical shr1 {n} t := Tuple (@shr1P n t).
  Check shr1 : BITS 4 -> BITS 4.
  
  Lemma nth_shr1_0 (s : seq bool) :
    nth false (shr1_seq s) 0 = false.
  Proof.
    by elim: s.
  Qed.
  
  Lemma nth_cons (T : Type) (x0 : T) (a : T) (s : seq T) (i : nat) :
    0 < i -> nth x0 (a :: s) i = nth x0 s i.-1.
  Proof.
    by elim: s i => [|x s IHs]; case. 
  Qed.

  (* s = [::] で i = 1 のとき、左辺は a、右辺は false であり、成立しない。 *)
  Lemma nth_shr1 (a : bool) (s : seq bool) (i : nat) :
    0 < i -> nth false (shr1_seq (a :: s)) i = nth false (shr1_seq s) i.-1.
  Proof.
  Admitted.
  
  (* s = [::] のとき false になり、成立しない。 *)
  Lemma nth_shr1_1 (a : bool) (s : seq bool) :
    nth false (shr1_seq (a :: s)) 1 = a.
  Proof.
  Admitted.
  
  Lemma nth_shr1_n (s : seq bool) (i : nat) :
    0 < i -> nth false (shr1_seq s) i = nth false s i.-1.
  Proof.
    elim: s i.
    - move=> i Hi.
        by rewrite !nth_nil.
    - move=> a s IHs i Hi.
      case Hi' : (0 < i.-1).
      + rewrite nth_cons.
        * rewrite nth_shr1.
          ** rewrite IHs.
             *** done.
             *** done.
          ** done.
        * done.
      + have H1 : i = 1 by apply p0lt__not_1lt__1.
        rewrite H1.
        rewrite [1.-1]/=.
        rewrite [nth false (a :: s) 0]/=.
        apply nth_shr1_1.
  Qed.
  
  Definition fset_shr1 {n} (fs : FSET n) (H : n.-1.+1 = n) : FSET n :=
    [set i : 'I_n | 0 < i & cast_ord H (@inord n.-1 i.-1) \in fs].
  (* シフトした後の、1〜n.-1 は、シフト前の 0〜n.-2 である。 *)
  (* シフトで追加される、シフト後の最左(bit0)の値は、とりあえず不問とする。 *)
  
  Lemma shr1_repr n (bs : BITS n) (fs : FSET n) :
    forall (H : 0 < n), repr bs fs ->
                        repr (shr1 bs) (fset_shr1 fs (prednK H)).
  Proof.
    move=> H.
    move/setP => H1.
    apply/setP => i.
    
(*  move: (H1 (cast_ord (prednK H) (@inord n.-1 i.-1))) => {H1} H1'. *)
    move: (H1 (cast_ord (prednK H) (inord i.-1))) => {H1} H1'.
    
    rewrite !inE (tnth_nth false) in H1'.
    rewrite !inE (tnth_nth false) /fset_shr1.
    
    (* i < n から i < n.-1.+1 。 +1になるのは inordの定義による。 *)
    (* i : 'I_n に値を足しても引いても、'I_n.-1.+1 型になる。 *)
    Check inord i : 'I_n.-1.+1.
    Check @inord n.-1 i : 'I_n.-1.+1.
    (* n を指定すればよいが、cast_ord できないので代入できない。 *)
    Check @inord n i.-1 : 'I_n.+1.
    Check @inord n.+1 i : 'I_n.+1.+1.

    case Hi : (0 < i).
    - rewrite nth_shr1_n /=.
      + rewrite -H1' /=.
        Check inordK.
        rewrite inordK.
        * done.
        * (* 普通は i < n なのだが、i.-1 を与えるので、i <= n になってしまう。 *)
          (* i.-1 < n.-1.+1 *)
          (* i.-1.+1 <= n.-1.+1 *)
          Check prednK.
          rewrite !prednK.
          ** apply ltnW.                    (* i < n -> i <= n *)
             by apply ltn_ord.              (* i : 'I_n -> i < n *)
          ** done.
          ** done.
      + done.
    - apply not_0lt__0 in Hi.
      rewrite Hi.
      by rewrite nth_shr1_0.
  Qed.
  
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
